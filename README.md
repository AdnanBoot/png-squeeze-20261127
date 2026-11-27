# png-squeeze-20261127

[![Competition](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![Rank](https://make.fun/badge/png-squeeze-01-run-20261127/AdnanBoot/png-squeeze-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![Reward](https://make.fun/badge/png-squeeze-01-run-20261127/AdnanBoot/png-squeeze-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

Lossless PNG compressor for [png-squeeze-01-run-20261127](https://make.fun/bounty/png-squeeze-01-run-20261127) written in Node 22 erasable TypeScript (`main.ts` + `deflate.ts`).

## Architecture
- **Decoder & PNG Writer (`main.ts`)**: Strict lossless PNG decoder and minimal chunk writer (`IHDR`, optional `PLTE`/`tRNS`, single `IDAT`, `IEND`) with bit depth 8, non-interlaced.
- **Colour-Type Reduction (`main.ts`)**: Reduces RGBA to greyscale (`0`), greyscale+alpha (`4`), RGB (`2`), or indexed palette (`3`, with minimal `tRNS` and multi-order palette evaluation) when lossless.
- **Adaptive Filtering (`main.ts`)**: Evaluates fixed filters (`None`, `Sub`, `Up`, `Paeth`) and per-row adaptive heuristics (`minsum`, `xentropy`).
- **Optimal-Parsing DEFLATE (`deflate.ts`)**: Deterministic Zopfli-style LZ77 hash-chain matching, iterative dynamic-programming optimal parsing, package-merge length-limited Huffman trees, and recursive histogram-based block splitting, with `node:zlib` level 9 fallback.
