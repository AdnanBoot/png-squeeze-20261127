// Deterministic Zopfli-style optimal-parsing DEFLATE + zlib wrapper (RFC 1950 / 1951).

const W_SIZE = 32768;
const W_MASK = W_SIZE - 1;
const MIN_MATCH = 3;
const MAX_MATCH = 258;
const HASH_BITS = 16;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;

// RFC 1951 length base and extra bits (codes 257..285)
const LEN_BASE = Int32Array.of(
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258
);
const LEN_EXTRA = Uint8Array.of(
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0
);

// RFC 1951 distance base and extra bits (codes 0..29)
const DIST_BASE = Int32Array.of(
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577
);
const DIST_EXTRA = Uint8Array.of(
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
);

// Code length alphabet order (RFC 1951 3.2.7)
const CL_ORDER = Uint8Array.of(
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
);

// Lookup tables for length 3..258 -> symbol 257..285
const LEN_SYM = new Uint16Array(259);
// Lookup tables for dist 1..32768 -> symbol 0..29
const DIST_SYM = new Uint8Array(32769);
const CHECKPOINTS = Int32Array.of(20, 24, 32, 48, 64, 96, 128, 192);

(() => {
  for (let code = 0; code < 29; code++) {
    const base = LEN_BASE[code];
    const next = code === 28 ? 259 : LEN_BASE[code + 1];
    for (let l = base; l < next; l++) LEN_SYM[l] = 257 + code;
  }
  for (let code = 0; code < 30; code++) {
    const base = DIST_BASE[code];
    const next = code === 29 ? 32769 : DIST_BASE[code + 1];
    for (let d = base; d < next; d++) DIST_SYM[d] = code;
  }
})();

function adler32(bytes: Uint8Array): number {
  let a = 1;
  let b = 0;
  for (let i = 0; i < bytes.length; ) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) {
      a += bytes[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

/**
 * Package-Merge algorithm for length-limited canonical Huffman code lengths.
 * Returns bit lengths in [0..maxBits] for each symbol in `freqs`.
 */
function lengthLimitedHuffman(freqs: Int32Array, maxBits: number): Uint8Array {
  const n = freqs.length;
  const lengths = new Uint8Array(n);
  const syms: number[] = [];
  for (let i = 0; i < n; i++) {
    if (freqs[i] > 0) syms.push(i);
  }
  if (syms.length === 0) {
    lengths[0] = 1;
    return lengths;
  }
  if (syms.length === 1) {
    lengths[syms[0]] = 1;
    return lengths;
  }
  if (syms.length === 2) {
    lengths[syms[0]] = 1;
    lengths[syms[1]] = 1;
    return lengths;
  }

  // Sort symbols by increasing frequency, then symbol index for determinism
  syms.sort((a, b) => freqs[a] - freqs[b] || a - b);
  const m = syms.length;

  // Package-Merge: each node in a level is represented by its weight and a leaf-count array or tree
  // Using flat arrays for speed: at most 2*m items per level.
  interface PkgNode {
    weight: number;
    sym: number; // >= 0 for leaf, -1 for package
    left: PkgNode | null;
    right: PkgNode | null;
  }

  const leaves: PkgNode[] = new Array(m);
  for (let i = 0; i < m; i++) {
    leaves[i] = { weight: freqs[syms[i]], sym: syms[i], left: null, right: null };
  }

  let prev: PkgNode[] = [];
  for (let bit = 0; bit < maxBits; bit++) {
    // Merge leaves and packaged pairs from prev
    const cur: PkgNode[] = new Array(m + (prev.length >> 1));
    let li = 0;
    let pi = 0;
    let ci = 0;
    const pPairs = prev.length & ~1;
    while (li < m && pi < pPairs) {
      const pkgWeight = prev[pi].weight + prev[pi + 1].weight;
      if (leaves[li].weight <= pkgWeight) {
        cur[ci++] = leaves[li++];
      } else {
        cur[ci++] = { weight: pkgWeight, sym: -1, left: prev[pi], right: prev[pi + 1] };
        pi += 2;
      }
    }
    while (li < m) cur[ci++] = leaves[li++];
    while (pi < pPairs) {
      cur[ci++] = { weight: prev[pi].weight + prev[pi + 1].weight, sym: -1, left: prev[pi], right: prev[pi + 1] };
      pi += 2;
    }
    prev = cur;
  }

  // Count leaf occurrences in the first 2*m - 2 nodes of the final level
  const take = Math.min(prev.length, 2 * m - 2);
  const stack: PkgNode[] = [];
  for (let i = 0; i < take; i++) stack.push(prev[i]);
  while (stack.length > 0) {
    const node = stack.pop()!;
    if (node.sym >= 0) {
      lengths[node.sym]++;
    } else {
      if (node.left !== null) stack.push(node.left);
      if (node.right !== null) stack.push(node.right);
    }
  }
  return lengths;
}

function buildCanonicalCodes(lengths: Uint8Array): Uint16Array {
  let maxLen = 0;
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] > maxLen) maxLen = lengths[i];
  }
  const blCount = new Int32Array(maxLen + 1);
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] > 0) blCount[lengths[i]]++;
  }
  const nextCode = new Int32Array(maxLen + 1);
  let code = 0;
  for (let bits = 1; bits <= maxLen; bits++) {
    code = (code + blCount[bits - 1]) << 1;
    nextCode[bits] = code;
  }
  const codes = new Uint16Array(lengths.length);
  for (let n = 0; n < lengths.length; n++) {
    const len = lengths[n];
    if (len > 0) {
      const c = nextCode[len]++;
      // Bit-reverse `c` over `len` bits for RFC 1951 LSB-first writing
      let rev = 0;
      for (let b = 0; b < len; b++) {
        rev = (rev << 1) | ((c >>> b) & 1);
      }
      codes[n] = rev;
    }
  }
  return codes;
}

class BitWriter {
  private buf: Uint8Array;
  private bytePos = 0;
  private bitBuf = 0;
  private bitCount = 0;

  constructor(initialCapacity: number) {
    this.buf = new Uint8Array(initialCapacity);
  }

  private ensure(extraBytes: number): void {
    if (this.bytePos + extraBytes > this.buf.length) {
      const next = new Uint8Array(Math.max(this.buf.length * 2, this.bytePos + extraBytes));
      next.set(this.buf.subarray(0, this.bytePos));
      this.buf = next;
    }
  }

  writeBits(val: number, len: number): void {
    this.bitBuf |= (val & ((1 << len) - 1)) << this.bitCount;
    this.bitCount += len;
    if (this.bitCount >= 16) {
      this.ensure(4);
      while (this.bitCount >= 8) {
        this.buf[this.bytePos++] = this.bitBuf & 0xff;
        this.bitBuf >>>= 8;
        this.bitCount -= 8;
      }
    }
  }

  flushBits(): void {
    this.ensure(2);
    while (this.bitCount > 0) {
      this.buf[this.bytePos++] = this.bitBuf & 0xff;
      this.bitBuf >>>= 8;
      this.bitCount = Math.max(0, this.bitCount - 8);
    }
  }

  writeByte(b: number): void {
    this.ensure(1);
    this.buf[this.bytePos++] = b;
  }

  writeUint32BE(v: number): void {
    this.ensure(4);
    this.buf[this.bytePos++] = (v >>> 24) & 0xff;
    this.buf[this.bytePos++] = (v >>> 16) & 0xff;
    this.buf[this.bytePos++] = (v >>> 8) & 0xff;
    this.buf[this.bytePos++] = v & 0xff;
  }

  finish(): Uint8Array {
    return this.buf.subarray(0, this.bytePos);
  }
}

interface TokenList {
  // Each token: if dist === 0, lit = val; if dist > 0, len = val (3..258), dist = 1..32768
  vals: Uint16Array;
  dists: Uint16Array;
  count: number;
}

function encodeRleCodeLengths(
  allLens: Uint8Array,
  total: number
): { syms: number[]; extras: number[] } {
  const syms: number[] = [];
  const extras: number[] = [];
  let i = 0;
  while (i < total) {
    const len = allLens[i];
    let run = 1;
    while (i + run < total && allLens[i + run] === len) run++;
    if (len === 0) {
      while (run >= 11) {
        const take = Math.min(138, run);
        syms.push(18);
        extras.push(take - 11);
        run -= take;
      }
      if (run >= 3) {
        syms.push(17);
        extras.push(run - 3);
        run = 0;
      }
      while (run > 0) {
        syms.push(0);
        extras.push(0);
        run--;
      }
    } else {
      syms.push(len);
      extras.push(0);
      run--;
      while (run >= 3) {
        const take = Math.min(6, run);
        syms.push(16);
        extras.push(take - 3);
        run -= take;
      }
      while (run > 0) {
        syms.push(len);
        extras.push(0);
        run--;
      }
    }
    let adv = 1;
    while (i + adv < total && allLens[i + adv] === len) adv++;
    i += adv;
  }
  return { syms, extras };
}

function writeDynamicBlock(
  bw: BitWriter,
  tokens: TokenList,
  startIdx: number,
  endIdx: number,
  isFinal: boolean
): void {
  const litFreq = new Int32Array(286);
  const distFreq = new Int32Array(30);
  litFreq[256] = 1; // EOB

  for (let i = startIdx; i < endIdx; i++) {
    const d = tokens.dists[i];
    const v = tokens.vals[i];
    if (d === 0) {
      litFreq[v]++;
    } else {
      litFreq[LEN_SYM[v]]++;
      distFreq[DIST_SYM[d]]++;
    }
  }

  const litLens = lengthLimitedHuffman(litFreq, 15);
  const distLens = lengthLimitedHuffman(distFreq, 15);
  const litCodes = buildCanonicalCodes(litLens);
  const distCodes = buildCanonicalCodes(distLens);

  let hlit = 286;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;

  const combined = new Uint8Array(hlit + hdist);
  combined.set(litLens.subarray(0, hlit), 0);
  combined.set(distLens.subarray(0, hdist), hlit);

  const rle = encodeRleCodeLengths(combined, hlit + hdist);
  const clFreq = new Int32Array(19);
  for (let i = 0; i < rle.syms.length; i++) clFreq[rle.syms[i]]++;

  const clLens = lengthLimitedHuffman(clFreq, 7);
  const clCodes = buildCanonicalCodes(clLens);

  let hclen = 19;
  while (hclen > 4 && clLens[CL_ORDER[hclen - 1]] === 0) hclen--;

  // Block header: BFINAL (1), BTYPE=10 (2)
  bw.writeBits(isFinal ? 1 : 0, 1);
  bw.writeBits(2, 2);
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hclen - 4, 4);

  for (let i = 0; i < hclen; i++) {
    bw.writeBits(clLens[CL_ORDER[i]], 3);
  }
  for (let i = 0; i < rle.syms.length; i++) {
    const s = rle.syms[i];
    bw.writeBits(clCodes[s], clLens[s]);
    if (s === 16) bw.writeBits(rle.extras[i], 2);
    else if (s === 17) bw.writeBits(rle.extras[i], 3);
    else if (s === 18) bw.writeBits(rle.extras[i], 7);
  }

  for (let i = startIdx; i < endIdx; i++) {
    const d = tokens.dists[i];
    const v = tokens.vals[i];
    if (d === 0) {
      bw.writeBits(litCodes[v], litLens[v]);
    } else {
      const lSym = LEN_SYM[v];
      bw.writeBits(litCodes[lSym], litLens[lSym]);
      const lCode = lSym - 257;
      if (LEN_EXTRA[lCode] > 0) bw.writeBits(v - LEN_BASE[lCode], LEN_EXTRA[lCode]);
      const dSym = DIST_SYM[d];
      bw.writeBits(distCodes[dSym], distLens[dSym]);
      if (DIST_EXTRA[dSym] > 0) bw.writeBits(d - DIST_BASE[dSym], DIST_EXTRA[dSym]);
    }
  }
  bw.writeBits(litCodes[256], litLens[256]);
}

interface MatchCache {
  // For each position i, store pareto-optimal matches in flat arrays
  offsets: Int32Array;
  lengths: Uint16Array;
  dists: Uint16Array;
}

function buildMatchCache(data: Uint8Array, maxChain: number): MatchCache {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(W_SIZE).fill(-1);
  const offsets = new Int32Array(n + 1);
  // Pre-allocate generous match buffer; grow if needed
  let cap = Math.max(1024, n * 2);
  let lengths = new Uint16Array(cap);
  let dists = new Uint16Array(cap);
  let mCount = 0;

  const ensureCap = (needed: number) => {
    if (mCount + needed > cap) {
      cap *= 2;
      const nl = new Uint16Array(cap);
      const nd = new Uint16Array(cap);
      nl.set(lengths.subarray(0, mCount));
      nd.set(dists.subarray(0, mCount));
      lengths = nl;
      dists = nd;
    }
  };

  for (let i = 0; i < n; i++) {
    offsets[i] = mCount;
    if (i + MIN_MATCH > n) continue;

    const h = ((data[i] << 11) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK;
    let cur = head[h];
    prev[i & W_MASK] = cur;
    head[h] = i;

    const maxLen = Math.min(MAX_MATCH, n - i);
    let bestLen = MIN_MATCH - 1;
    let chain = maxChain;
    let rleSkip = i;

    // Fast RLE check for dist = 1
    if (i > 0 && data[i] === data[i - 1] && data[i + 1] === data[i] && data[i + 2] === data[i]) {
      let rle = 3;
      const b = data[i];
      while (rle < maxLen && data[i + rle] === b) rle++;
      ensureCap(1);
      lengths[mCount] = rle;
      dists[mCount] = 1;
      mCount++;
      bestLen = rle;
      rleSkip = i - rle;
      if (bestLen === maxLen) continue;
    }

    const limit = i - W_SIZE;
    while (cur > limit && chain-- > 0) {
      if (cur < rleSkip && data[cur + bestLen] === data[i + bestLen] && data[cur] === data[i] && data[cur + 1] === data[i + 1]) {
        let len = 2;
        while (len < maxLen && data[cur + len] === data[i + len]) len++;
        if (len > bestLen) {
          ensureCap(1);
          lengths[mCount] = len;
          dists[mCount] = i - cur;
          mCount++;
          bestLen = len;
          if (bestLen === maxLen) break;
          if (bestLen >= 64 && chain > 32) chain = 32;
        }
      }
      cur = prev[cur & W_MASK];
    }
  }
  offsets[n] = mCount;
  return { offsets, lengths: lengths.subarray(0, mCount), dists: dists.subarray(0, mCount) };
}

function greedyInitialTokens(data: Uint8Array, cache: MatchCache): TokenList {
  const n = data.length;
  const vals = new Uint16Array(n);
  const dists = new Uint16Array(n);
  let count = 0;
  let i = 0;

  while (i < n) {
    const start = cache.offsets[i];
    const end = cache.offsets[i + 1];
    if (end > start) {
      const bestLen = cache.lengths[end - 1];
      const bestDist = cache.dists[end - 1];
      // Simple lazy check at i+1
      if (i + 1 < n && bestLen < MAX_MATCH) {
        const nextEnd = cache.offsets[i + 2];
        const nextStart = cache.offsets[i + 1];
        if (nextEnd > nextStart && cache.lengths[nextEnd - 1] > bestLen + 1) {
          vals[count] = data[i];
          dists[count] = 0;
          count++;
          i++;
          continue;
        }
      }
      vals[count] = bestLen;
      dists[count] = bestDist;
      count++;
      i += bestLen;
    } else {
      vals[count] = data[i];
      dists[count] = 0;
      count++;
      i++;
    }
  }
  return { vals: vals.subarray(0, count), dists: dists.subarray(0, count), count };
}

function optimalParseRange(
  data: Uint8Array,
  startPos: number,
  endPos: number,
  cache: MatchCache,
  litCost: Float64Array,
  distCost: Float64Array
): TokenList {
  const n = endPos - startPos;
  const costs = new Float64Array(n + 1).fill(Infinity);
  const bestLen = new Uint16Array(n + 1);
  const bestDist = new Uint16Array(n + 1);
  costs[0] = 0;

  for (let rel = 0; rel < n; rel++) {
    const i = startPos + rel;
    const c = costs[rel];
    if (c === Infinity) continue;

    // Literal step
    const lc = c + litCost[data[i]];
    if (lc < costs[rel + 1]) {
      costs[rel + 1] = lc;
      bestLen[rel + 1] = 1;
      bestDist[rel + 1] = 0;
    }

    // Match steps from pareto-optimal cache, clamped to endPos
    const mStart = cache.offsets[i];
    const mEnd = cache.offsets[i + 1];
    const maxAvail = endPos - i;
    let prevL = MIN_MATCH - 1;
    for (let m = mStart; m < mEnd; m++) {
      let maxL = cache.lengths[m];
      if (maxL > maxAvail) maxL = maxAvail;
      if (maxL < MIN_MATCH) break;
      const d = cache.dists[m];
      const dSym = DIST_SYM[d];
      const dCost = distCost[dSym] + DIST_EXTRA[dSym];
      const limitShort = maxL < 16 ? maxL : 16;
      for (let l = prevL + 1; l <= limitShort; l++) {
        const lSym = LEN_SYM[l];
        const mc = c + litCost[lSym] + LEN_EXTRA[lSym - 257] + dCost;
        if (mc < costs[rel + l]) {
          costs[rel + l] = mc;
          bestLen[rel + l] = l;
          bestDist[rel + l] = d;
        }
      }
      if (maxL > 16) {
        for (let ci = 0; ci < CHECKPOINTS.length; ci++) {
          const l = CHECKPOINTS[ci];
          if (l > prevL && l < maxL - 1) {
            const lSym = LEN_SYM[l];
            const mc = c + litCost[lSym] + LEN_EXTRA[lSym - 257] + dCost;
            if (mc < costs[rel + l]) {
              costs[rel + l] = mc;
              bestLen[rel + l] = l;
              bestDist[rel + l] = d;
            }
          }
        }
        if (maxL - 1 > prevL && maxL - 1 > 16) {
          const l = maxL - 1;
          const lSym = LEN_SYM[l];
          const mc = c + litCost[lSym] + LEN_EXTRA[lSym - 257] + dCost;
          if (mc < costs[rel + l]) {
            costs[rel + l] = mc;
            bestLen[rel + l] = l;
            bestDist[rel + l] = d;
          }
        }
        const lSym = LEN_SYM[maxL];
        const mc = c + litCost[lSym] + LEN_EXTRA[lSym - 257] + dCost;
        if (mc < costs[rel + maxL]) {
          costs[rel + maxL] = mc;
          bestLen[rel + maxL] = maxL;
          bestDist[rel + maxL] = d;
        }
      }
      prevL = maxL;
      if (maxL === maxAvail) break;
    }
  }

  const revVals: number[] = [];
  const revDists: number[] = [];
  let pos = n;
  while (pos > 0) {
    const l = bestLen[pos];
    const d = bestDist[pos];
    if (d === 0) {
      revVals.push(data[startPos + pos - 1]);
      revDists.push(0);
      pos -= 1;
    } else {
      revVals.push(l);
      revDists.push(d);
      pos -= l;
    }
  }

  const count = revVals.length;
  const vals = new Uint16Array(count);
  const dists = new Uint16Array(count);
  for (let i = 0; i < count; i++) {
    vals[i] = revVals[count - 1 - i];
    dists[i] = revDists[count - 1 - i];
  }
  return { vals, dists, count };
}

function optimalParsePass(
  data: Uint8Array,
  cache: MatchCache,
  litCost: Float64Array,
  distCost: Float64Array
): TokenList {
  return optimalParseRange(data, 0, data.length, cache, litCost, distCost);
}

function tokensToCostModelRange(
  tokens: TokenList,
  start: number,
  end: number
): { litCost: Float64Array; distCost: Float64Array } {
  const litFreq = new Int32Array(286);
  const distFreq = new Int32Array(30);
  litFreq[256] = 1;
  for (let i = start; i < end; i++) {
    const d = tokens.dists[i];
    const v = tokens.vals[i];
    if (d === 0) litFreq[v]++;
    else {
      litFreq[LEN_SYM[v]]++;
      distFreq[DIST_SYM[d]]++;
    }
  }
  const litLens = lengthLimitedHuffman(litFreq, 15);
  const distLens = lengthLimitedHuffman(distFreq, 15);
  const litCost = new Float64Array(286);
  const distCost = new Float64Array(30);
  for (let i = 0; i < 286; i++) litCost[i] = litLens[i] > 0 ? litLens[i] : 15;
  for (let i = 0; i < 30; i++) distCost[i] = distLens[i] > 0 ? distLens[i] : 15;
  return { litCost, distCost };
}

function tokensToCostModel(tokens: TokenList): { litCost: Float64Array; distCost: Float64Array } {
  return tokensToCostModelRange(tokens, 0, tokens.count);
}

function estimateBlockBits(litFreq: Int32Array, distFreq: Int32Array): number {
  let litTotal = 0;
  let litActive = 0;
  for (let i = 0; i < 286; i++) {
    const f = litFreq[i];
    if (f > 0) {
      litTotal += f;
      litActive++;
    }
  }
  let distTotal = 0;
  let distActive = 0;
  for (let i = 0; i < 30; i++) {
    const f = distFreq[i];
    if (f > 0) {
      distTotal += f;
      distActive++;
    }
  }
  let bits = 32 + (litActive + distActive) * 5; // approximate dynamic header overhead
  if (litTotal > 0) {
    const logTotal = Math.log2(litTotal);
    for (let i = 0; i < 286; i++) {
      const f = litFreq[i];
      if (f > 0) bits += f * (logTotal - Math.log2(f));
    }
  }
  if (distTotal > 0) {
    const logTotal = Math.log2(distTotal);
    for (let i = 0; i < 30; i++) {
      const f = distFreq[i];
      if (f > 0) bits += f * (logTotal - Math.log2(f));
    }
  }
  return bits;
}

function findBlockSplits(tokens: TokenList, start: number, end: number, splits: number[]): void {
  const len = end - start;
  if (len < 2048 || splits.length >= 31) return;

  const totalLit = new Int32Array(286);
  const totalDist = new Int32Array(30);
  totalLit[256] = 1;
  for (let i = start; i < end; i++) {
    const d = tokens.dists[i];
    const v = tokens.vals[i];
    if (d === 0) totalLit[v]++;
    else {
      totalLit[LEN_SYM[v]]++;
      totalDist[DIST_SYM[d]]++;
    }
  }
  const baseBits = estimateBlockBits(totalLit, totalDist);

  const leftLit = new Int32Array(286);
  const leftDist = new Int32Array(30);
  const rightLit = new Int32Array(totalLit);
  const rightDist = new Int32Array(totalDist);
  leftLit[256] = 1;

  const numProbes = 64;
  const step = Math.floor(len / numProbes);
  let bestMid = -1;
  let bestBits = baseBits - 384; // require at least 48 bytes savings to split

  for (let i = start; i < end - 1024; i++) {
    const d = tokens.dists[i];
    const v = tokens.vals[i];
    if (d === 0) {
      leftLit[v]++;
      rightLit[v]--;
    } else {
      const ls = LEN_SYM[v];
      const ds = DIST_SYM[d];
      leftLit[ls]++;
      rightLit[ls]--;
      leftDist[ds]++;
      rightDist[ds]--;
    }
    const rel = i - start + 1;
    if (rel >= 1024 && rel % step === 0) {
      const bits = estimateBlockBits(leftLit, leftDist) + estimateBlockBits(rightLit, rightDist);
      if (bits < bestBits) {
        bestBits = bits;
        bestMid = i + 1;
      }
    }
  }

  if (bestMid !== -1) {
    findBlockSplits(tokens, start, bestMid, splits);
    splits.push(bestMid);
    findBlockSplits(tokens, bestMid, end, splits);
  }
}

function encodeSplitBlocksZlib(
  data: Uint8Array,
  cache: MatchCache,
  tokens: TokenList,
  blockIters: number
): Uint8Array {
  const splits: number[] = [];
  findBlockSplits(tokens, 0, tokens.count, splits);
  splits.push(tokens.count);

  const bw = new BitWriter(Math.max(1024, data.length >> 1));
  bw.writeByte(0x78);
  bw.writeByte(0xda);

  let prevTok = 0;
  let prevByte = 0;
  for (let b = 0; b < splits.length; b++) {
    const endTok = splits[b];
    if (endTok <= prevTok) continue;
    let blockBytes = 0;
    for (let i = prevTok; i < endTok; i++) {
      blockBytes += tokens.dists[i] === 0 ? 1 : tokens.vals[i];
    }
    const endByte = prevByte + blockBytes;
    if (blockIters > 0 && splits.length > 1) {
      let { litCost, distCost } = tokensToCostModelRange(tokens, prevTok, endTok);
      let blockTokens = optimalParseRange(data, prevByte, endByte, cache, litCost, distCost);
      for (let bi = 1; bi < blockIters; bi++) {
        const model = tokensToCostModelRange(blockTokens, 0, blockTokens.count);
        blockTokens = optimalParseRange(data, prevByte, endByte, cache, model.litCost, model.distCost);
      }
      writeDynamicBlock(bw, blockTokens, 0, blockTokens.count, b === splits.length - 1);
    } else {
      writeDynamicBlock(bw, tokens, prevTok, endTok, b === splits.length - 1);
    }
    prevTok = endTok;
    prevByte = endByte;
  }
  bw.flushBits();
  bw.writeUint32BE(adler32(data));
  return bw.finish();
}

export function zopfliDeflateZlib(data: Uint8Array, iterations?: number, maxChain?: number): Uint8Array {
  if (data.length === 0) {
    const bw = new BitWriter(16);
    bw.writeByte(0x78);
    bw.writeByte(0xda);
    bw.writeBits(1, 1);
    bw.writeBits(0, 2);
    bw.flushBits();
    bw.writeBits(0, 16);
    bw.writeBits(0xffff, 16);
    bw.writeUint32BE(adler32(data));
    return bw.finish();
  }

  const iters = iterations ?? (data.length > 2_000_000 ? 1 : 2);
  const chain = maxChain ?? (data.length > 2_000_000 ? 128 : 256);
  const cache = buildMatchCache(data, chain);
  let curTokens = greedyInitialTokens(data, cache);
  let bestBytes = encodeSplitBlocksZlib(data, cache, curTokens, 0);

  for (let it = 0; it < iters; it++) {
    const { litCost, distCost } = tokensToCostModel(curTokens);
    const nextTokens = optimalParsePass(data, cache, litCost, distCost);
    const blockIters = it === iters - 1 ? 1 : 0;
    const nextBytes = encodeSplitBlocksZlib(data, cache, nextTokens, blockIters);
    if (nextBytes.length < bestBytes.length) {
      bestBytes = nextBytes;
    }
    if (it === iters - 1) {
      // Also check single-block encoding in case splitting overhead exceeded savings
      const bw = new BitWriter(Math.max(1024, data.length >> 1));
      bw.writeByte(0x78);
      bw.writeByte(0xda);
      writeDynamicBlock(bw, nextTokens, 0, nextTokens.count, true);
      bw.flushBits();
      bw.writeUint32BE(adler32(data));
      const single = bw.finish();
      if (single.length < bestBytes.length) {
        bestBytes = single;
      }
    }
    curTokens = nextTokens;
  }

  return bestBytes;
}
