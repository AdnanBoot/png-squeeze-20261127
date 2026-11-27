import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';
import { zopfliDeflateZlib } from './deflate.ts';

const PNG_SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS: Record<number, number> = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes: Uint8Array, start = 0, end = bytes.length): number {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function paethPredictor(a: number, b: number, c: number): number {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

interface DecodedImage {
  width: number;
  height: number;
  rgba: Uint8Array;
}

function decodePng(bytes: Uint8Array): DecodedImage {
  if (bytes.length < 8) throw new Error('Invalid PNG: too short');
  for (let i = 0; i < 8; i++) {
    if (bytes[i] !== PNG_SIGNATURE[i]) throw new Error('Invalid PNG signature');
  }

  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let width = 0;
  let height = 0;
  let colourType = -1;
  let palette: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idatChunks: Uint8Array[] = [];

  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;

    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      width = dv.getUint32(0);
      height = dv.getUint32(4);
      colourType = data[9];
    } else if (type === 'PLTE') {
      palette = data;
    } else if (type === 'tRNS') {
      trns = data;
    } else if (type === 'IDAT') {
      idatChunks.push(data);
    } else if (type === 'IEND') {
      break;
    }
  }

  const bpp = CHANNELS[colourType];
  if (!bpp) throw new Error(`Unsupported colour type ${colourType}`);
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idatChunks.length === 1 ? idatChunks[0] : Buffer.concat(idatChunks), {
    maxOutputLength: expected + 1,
  });

  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) {
      samples.set(raw.subarray(src, src + stride), o);
    } else if (ft === 1) {
      for (let i = 0; i < stride; i++) {
        samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
      }
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) {
        samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
      }
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        samples[o + i] = raw[src + i] + ((a + b) >> 1);
      }
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paethPredictor(a, b, c);
      }
    }
  }

  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) {
    rgba.set(samples);
  } else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else if (palette !== null) {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }

  return { width, height, rgba };
}

interface ReducedImage {
  colourType: number;
  bpp: number;
  samples: Uint8Array;
  plte: Uint8Array | null;
  trns: Uint8Array | null;
}

function reduceColourType(rgba: Uint8Array, width: number, height: number): ReducedImage {
  const n = width * height;
  let isGrey = true;
  let allOpaque = true;
  const colorMap = new Map<number, number>();
  let tooManyColors = false;

  for (let i = 0, p = 0; i < n; i++, p += 4) {
    const r = rgba[p];
    const g = rgba[p + 1];
    const b = rgba[p + 2];
    const a = rgba[p + 3];
    if (r !== g || g !== b) isGrey = false;
    if (a !== 255) allOpaque = false;
    if (!tooManyColors) {
      const key = ((r << 24) | (g << 16) | (b << 8) | a) >>> 0;
      if (!colorMap.has(key)) {
        if (colorMap.size >= 256) {
          tooManyColors = true;
        } else {
          colorMap.set(key, colorMap.size);
        }
      }
    }
  }

  // Grey opaque -> type 0 (1 bpp, no PLTE, smooth spatial correlation)
  if (isGrey && allOpaque) {
    const samples = new Uint8Array(n);
    for (let i = 0, p = 0; i < n; i++, p += 4) {
      samples[i] = rgba[p];
    }
    return { colourType: 0, bpp: 1, samples, plte: null, trns: null };
  }

  // <= 256 distinct RGBA colours -> type 3 (palette)
  if (!tooManyColors) {
    const baseEntries = Array.from(colorMap.keys());
    const freqs = new Map<number, number>();
    for (let i = 0, p = 0; i < n; i++, p += 4) {
      const key = ((rgba[p] << 24) | (rgba[p + 1] << 16) | (rgba[p + 2] << 8) | rgba[p + 3]) >>> 0;
      freqs.set(key, (freqs.get(key) ?? 0) + 1);
    }

    const buildPaletteCandidate = (sortMode: 'appearance' | 'luminance' | 'frequency' | 'rgb' | 'nearest'): ReducedImage => {
      let entries = baseEntries.slice();
      if (sortMode === 'nearest') {
        const trans: number[] = [];
        const opq: number[] = [];
        for (const c of entries) {
          if ((c & 0xff) < 255) trans.push(c);
          else opq.push(c);
        }
        trans.sort((a, b) => a - b);
        const ordered: number[] = [];
        if (opq.length > 0) {
          opq.sort((a, b) => (freqs.get(b)! - freqs.get(a)!) || (a - b));
          const used = new Uint8Array(opq.length);
          let cur = opq[0];
          used[0] = 1;
          ordered.push(cur);
          for (let step = 1; step < opq.length; step++) {
            const cr = (cur >>> 24) & 0xff;
            const cg = (cur >>> 16) & 0xff;
            const cb = (cur >>> 8) & 0xff;
            let bestIdx = -1;
            let bestDist = Infinity;
            for (let j = 0; j < opq.length; j++) {
              if (used[j]) continue;
              const o = opq[j];
              const dr = ((o >>> 24) & 0xff) - cr;
              const dg = ((o >>> 16) & 0xff) - cg;
              const db = ((o >>> 8) & 0xff) - cb;
              const d = dr * dr + dg * dg + db * db;
              if (d < bestDist) {
                bestDist = d;
                bestIdx = j;
              }
            }
            used[bestIdx] = 1;
            cur = opq[bestIdx];
            ordered.push(cur);
          }
        }
        entries = trans.concat(ordered);
      } else {
        entries.sort((a, b) => {
          const aa = a & 0xff;
          const ba = b & 0xff;
          if ((aa < 255) !== (ba < 255)) return aa < 255 ? -1 : 1;
          if (sortMode === 'appearance') return (colorMap.get(a)! - colorMap.get(b)!);
          if (sortMode === 'frequency') return (freqs.get(b)! - freqs.get(a)!) || (a - b);
          if (sortMode === 'rgb') return a - b;
          const la = 299 * ((a >>> 24) & 0xff) + 587 * ((a >>> 16) & 0xff) + 114 * ((a >>> 8) & 0xff);
          const lb = 299 * ((b >>> 24) & 0xff) + 587 * ((b >>> 16) & 0xff) + 114 * ((b >>> 8) & 0xff);
          return la - lb || a - b;
        });
      }

      const sortedMap = new Map<number, number>();
      const plte = new Uint8Array(entries.length * 3);
      let trnsLen = 0;
      for (let i = 0; i < entries.length; i++) {
        const c = entries[i];
        sortedMap.set(c, i);
        plte[i * 3] = (c >>> 24) & 0xff;
        plte[i * 3 + 1] = (c >>> 16) & 0xff;
        plte[i * 3 + 2] = (c >>> 8) & 0xff;
        if ((c & 0xff) < 255) trnsLen = i + 1;
      }

      let trns: Uint8Array | null = null;
      if (trnsLen > 0) {
        trns = new Uint8Array(trnsLen);
        for (let i = 0; i < trnsLen; i++) {
          trns[i] = entries[i] & 0xff;
        }
      }

      const samples = new Uint8Array(n);
      for (let i = 0, p = 0; i < n; i++, p += 4) {
        const key = ((rgba[p] << 24) | (rgba[p + 1] << 16) | (rgba[p + 2] << 8) | rgba[p + 3]) >>> 0;
        samples[i] = sortedMap.get(key)!;
      }
      return { colourType: 3, bpp: 1, samples, plte, trns };
    };

    let bestCand: ReducedImage | null = null;
    let bestCandSize = Infinity;
    for (const sm of ['appearance', 'luminance', 'frequency', 'rgb', 'nearest'] as const) {
      const cand = buildPaletteCandidate(sm);
      const stride = width;
      const raw = new Uint8Array(height * (stride + 1));
      for (let y = 0; y < height; y++) {
        raw.set(cand.samples.subarray(y * stride, (y + 1) * stride), y * (stride + 1) + 1);
      }
      const z = deflateSync(raw, { level: 6, memLevel: 9 });
      if (z.length < bestCandSize) {
        bestCandSize = z.length;
        bestCand = cand;
      }
    }
    return bestCand!;
  }

  // Grey + alpha -> type 4
  if (isGrey) {
    const samples = new Uint8Array(n * 2);
    for (let i = 0, p = 0, d = 0; i < n; i++, p += 4, d += 2) {
      samples[d] = rgba[p];
      samples[d + 1] = rgba[p + 3];
    }
    return { colourType: 4, bpp: 2, samples, plte: null, trns: null };
  }

  // RGB opaque -> type 2
  if (allOpaque) {
    const samples = new Uint8Array(n * 3);
    for (let i = 0, p = 0, d = 0; i < n; i++, p += 4, d += 3) {
      samples[d] = rgba[p];
      samples[d + 1] = rgba[p + 1];
      samples[d + 2] = rgba[p + 2];
    }
    return { colourType: 2, bpp: 3, samples, plte: null, trns: null };
  }

  // RGBA -> type 6
  return { colourType: 6, bpp: 4, samples: rgba, plte: null, trns: null };
}

function buildPng(
  width: number,
  height: number,
  colourType: number,
  plte: Uint8Array | null,
  trns: Uint8Array | null,
  idat: Uint8Array
): Uint8Array {
  const ihdr = new Uint8Array(13);
  const ihdrView = new DataView(ihdr.buffer);
  ihdrView.setUint32(0, width);
  ihdrView.setUint32(4, height);
  ihdr[8] = 8;
  ihdr[9] = colourType;

  const chunks: Array<[string, Uint8Array]> = [['IHDR', ihdr]];
  if (plte !== null) chunks.push(['PLTE', plte]);
  if (trns !== null) chunks.push(['tRNS', trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);

  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(PNG_SIGNATURE, 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out[at + 4] = type.charCodeAt(0);
    out[at + 5] = type.charCodeAt(1);
    out[at + 6] = type.charCodeAt(2);
    out[at + 7] = type.charCodeAt(3);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function filterRow(
  type: number,
  cur: Uint8Array,
  prev: Uint8Array | null,
  bpp: number,
  out: Uint8Array
): number {
  const n = cur.length;
  let sum = 0;
  if (type === 0) {
    out.set(cur);
    for (let i = 0; i < n; i++) {
      const v = out[i];
      sum += v < 128 ? v : 256 - v;
    }
  } else if (type === 1) {
    for (let i = 0; i < n; i++) {
      const v = (cur[i] - (i >= bpp ? cur[i - bpp] : 0)) & 0xff;
      out[i] = v;
      sum += v < 128 ? v : 256 - v;
    }
  } else if (type === 2) {
    for (let i = 0; i < n; i++) {
      const v = (cur[i] - (prev === null ? 0 : prev[i])) & 0xff;
      out[i] = v;
      sum += v < 128 ? v : 256 - v;
    }
  } else if (type === 3) {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const v = (cur[i] - ((a + b) >> 1)) & 0xff;
      out[i] = v;
      sum += v < 128 ? v : 256 - v;
    }
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      const v = (cur[i] - paethPredictor(a, b, c)) & 0xff;
      out[i] = v;
      sum += v < 128 ? v : 256 - v;
    }
  }
  return sum;
}

function rowEntropyCost(buf: Uint8Array, counts: Int32Array): number {
  counts.fill(0);
  const n = buf.length;
  for (let i = 0; i < n; i++) counts[buf[i]]++;
  let cost = 0;
  for (let i = 0; i < 256; i++) {
    const c = counts[i];
    if (c > 0) cost -= c * Math.log2(c / n);
  }
  return cost;
}

function rowCrossEntropyCost(buf: Uint8Array, globalCounts: Int32Array, globalTotal: number): number {
  const n = buf.length;
  const denom = globalTotal + n + 256;
  let cost = 0;
  for (let i = 0; i < n; i++) {
    cost -= Math.log2((globalCounts[buf[i]] + 1) / denom);
  }
  return cost;
}

function filterImage(
  samples: Uint8Array,
  width: number,
  height: number,
  bpp: number,
  mode: 'none' | 'sub' | 'up' | 'avg' | 'paeth' | 'minsum' | 'entropy' | 'xentropy' | 'strip16'
): Uint8Array {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));

  if (mode === 'none' || mode === 'sub' || mode === 'up' || mode === 'avg' || mode === 'paeth') {
    const ft = mode === 'none' ? 0 : mode === 'sub' ? 1 : mode === 'up' ? 2 : mode === 'avg' ? 3 : 4;
    for (let y = 0; y < height; y++) {
      const cur = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
      const dst = y * (stride + 1);
      raw[dst] = ft;
      filterRow(ft, cur, prev, bpp, raw.subarray(dst + 1, dst + 1 + stride));
    }
    return raw;
  }

  if (mode === 'strip16') {
    const stripBuf = Array.from({ length: 5 }, () => new Uint8Array(stride));
    for (let y0 = 0; y0 < height; y0 += 16) {
      const y1 = Math.min(height, y0 + 16);
      let bestType = 0;
      let bestSum = Infinity;
      for (let t = 0; t < 5; t++) {
        let s = 0;
        for (let y = y0; y < y1; y++) {
          const cur = samples.subarray(y * stride, (y + 1) * stride);
          const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
          s += filterRow(t, cur, prev, bpp, stripBuf[t]);
        }
        if (s < bestSum) {
          bestSum = s;
          bestType = t;
        }
      }
      for (let y = y0; y < y1; y++) {
        const cur = samples.subarray(y * stride, (y + 1) * stride);
        const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
        const dst = y * (stride + 1);
        raw[dst] = bestType;
        filterRow(bestType, cur, prev, bpp, raw.subarray(dst + 1, dst + 1 + stride));
      }
    }
    return raw;
  }

  const trials = Array.from({ length: 5 }, () => new Uint8Array(stride));
  const counts = new Int32Array(256);
  const globalCounts = new Int32Array(256);
  let globalTotal = 0;

  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    let bestType = 0;
    let bestScore = Infinity;
    for (let t = 0; t < 5; t++) {
      const s = filterRow(t, cur, prev, bpp, trials[t]);
      const score =
        mode === 'minsum'
          ? s
          : mode === 'entropy'
            ? rowEntropyCost(trials[t], counts)
            : rowCrossEntropyCost(trials[t], globalCounts, globalTotal);
      if (score < bestScore) {
        bestScore = score;
        bestType = t;
      }
    }
    const chosen = trials[bestType];
    if (mode === 'xentropy') {
      for (let i = 0; i < stride; i++) globalCounts[chosen[i]]++;
      globalTotal += stride;
    }
    const dst = y * (stride + 1);
    raw[dst] = bestType;
    raw.set(chosen, dst + 1);
  }
  return raw;
}

function encodePng(rgba: Uint8Array, width: number, height: number): Uint8Array {
  const reduced = reduceColourType(rgba, width, height);
  const modes: Array<'none' | 'sub' | 'up' | 'avg' | 'paeth' | 'minsum' | 'entropy' | 'xentropy' | 'strip16'> =
    reduced.colourType === 3
      ? ['none', 'sub', 'up', 'paeth', 'minsum', 'entropy', 'xentropy']
      : ['none', 'sub', 'up', 'paeth', 'minsum', 'entropy', 'xentropy', 'strip16'];

  let bestIdat: Uint8Array | null = null;
  let bestRaw: Uint8Array | null = null;
  let bestPreLen = Infinity;
  let secondRaw: Uint8Array | null = null;
  let secondPreLen = Infinity;

  for (const mode of modes) {
    const raw = filterImage(reduced.samples, width, height, reduced.bpp, mode);
    const z = new Uint8Array(deflateSync(raw, { level: 6, memLevel: 9, strategy: 0 }));
    if (z.length < bestPreLen) {
      secondPreLen = bestPreLen;
      secondRaw = bestRaw;
      bestPreLen = z.length;
      bestRaw = raw;
    } else if (z.length < secondPreLen) {
      secondPreLen = z.length;
      secondRaw = raw;
    }
  }
  if (bestRaw !== null) {
    for (const strategy of [0, 1]) {
      const z = new Uint8Array(deflateSync(bestRaw, { level: 9, memLevel: 9, strategy }));
      if (bestIdat === null || z.length < bestIdat.length) {
        bestIdat = z;
      }
    }
    const zopfli = zopfliDeflateZlib(bestRaw);
    if (bestIdat === null || zopfli.length < bestIdat.length) {
      bestIdat = zopfli;
    }
    if (secondRaw !== null && secondRaw.length <= 1_000_000 && secondPreLen <= bestPreLen * 1.02) {
      const zopfli2 = zopfliDeflateZlib(secondRaw);
      if (zopfli2.length < bestIdat.length) {
        bestIdat = zopfli2;
      }
    }
  }
  return buildPng(width, height, reduced.colourType, reduced.plte, reduced.trns, bestIdat!);
}

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT_DIR).sort()) {
  const img = decodePng(new Uint8Array(readFileSync(join(INPUT_DIR, id, 'image.png'))));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'image.png'), encodePng(img.rgba, img.width, img.height));
}
