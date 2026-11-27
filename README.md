# png-squeeze-01: lossless PNG re-encoder

One program, `main.ts` (Node 22, built-ins only, no installs), that rewrites each
1280x720 RGBA screenshot as the smallest exact PNG it can, in one run over the
whole set of 8.

How it works:

- Decodes the stored input PNG with the kit checker's own rules.
- Analyses the image: opaque? grey? at most 256 colours? one transparent key?
- Tries every exact form: palette (colour type 3, in count / luminance /
  first-occurrence order), grey, grey+alpha, RGB, RGBA, with a tRNS key where
  one exists. Fully transparent pixels keep their colours exactly.
- For each form, tries per-row filter choices: fixed Paeth, fixed None,
  minimum-sum heuristic, and brute force — each row's five filters weighed by
  an actual deflate of the row after the previous 32 KiB (level 9 for channel
  forms, level 4 for palette forms).
- Screens every candidate at zlib level 6, re-screens the best two at level 9,
  then re-compresses the winner at level 9 (default and filtered strategies)
  and with 256 KiB block splitting (one deflate state, dictionary kept across
  blocks). Keeps the smallest.
- Writes one PNG: IHDR, PLTE (type 3 only), tRNS, a single IDAT, IEND, correct
  CRCs.

Deterministic: no clock, no randomness, every choice by byte comparison with
a fixed tie-break. Two runs write identical bytes.

Practice-set local grade (kit scorer, `makefun grade-local --driver process`):
score 711,750 of 1,000,000 (house baseline fixed-paeth: 420,399), all 8
instances exact, runtime ~25 s locally for the set of 8.

## License

MIT — see LICENSE.
