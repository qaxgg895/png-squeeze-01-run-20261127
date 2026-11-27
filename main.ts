// png-squeeze-01 entry: a lossless PNG re-encoder for 1280x720 RGBA screenshots.
//
// Strategy (general, no fitting to any one set):
//   - decode the stored input PNG with the kit's own decoder rules
//   - analyse the image: opaque? grey? at most 256 colours? one transparent key?
//   - try every exact form: palette (colour type 3, three entry orders),
//     grey / grey+alpha / RGB / RGBA, with a tRNS key where one exists
//   - for each form, try several per-row filter choices: fixed Paeth, fixed None,
//     minimum-sum heuristic, and brute force (each row's five filters weighed by
//     an actual level-4 deflate of the row after the previous 32 KiB)
//   - screen every candidate at zlib level 6, keep the smallest (with PLTE/tRNS
//     chunk overhead counted), then re-compress the winner at level 9 (default
//     and filtered strategies) and with 256 KiB block splitting (one deflate
//     state, per-block strategy, dictionary kept across blocks)
//   - write one PNG: IHDR, PLTE (type 3 only), tRNS, one IDAT, IEND, CRCs correct
//
// Deterministic by construction: no clock, no randomness, every choice by byte
// comparison with a fixed tie-break. Pure Node built-ins, no installs.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import zlib, { constants, deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- PNG codec
// Adapted from the kit's own checker codec (program/scorer/checker/png.mjs,
// MIT): the exact reader the scorer uses, plus the chunk writer.

const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
const CHUNKS = ['IHDR', 'PLTE', 'tRNS', 'IDAT', 'IEND'];

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function adler32(bytes) {
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

const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function pngOf(chunks) {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

const fail = (why) => ({ ok: false, why });

function decodePng(bytes, expect = null) {
  if (!(bytes instanceof Uint8Array)) return fail('it is not bytes');
  if (bytes.length < SIGNATURE.length || SIGNATURE.some((b, i) => bytes[i] !== b)) return fail('no PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = SIGNATURE.length;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let idatDone = false;
  let ended = false;
  while (at < bytes.length) {
    if (ended) return fail('bytes after IEND');
    if (at + 12 > bytes.length) return fail('chunk cut short');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) return fail('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (!/^[A-Za-z]{4}$/.test(type)) return fail('bad chunk type');
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) return fail(`${type} CRC`);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (!CHUNKS.includes(type)) return fail(`chunk ${type} not read`);
    if (header === null && type !== 'IHDR') return fail('first chunk not IHDR');
    if (type !== 'IDAT' && idat.length > 0) idatDone = true;
    if (type === 'IHDR') {
      if (header !== null) return fail('IHDR twice');
      if (len !== 13) return fail('IHDR not 13 bytes');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], compression: data[10], filter: data[11], interlace: data[12] };
      if (header.width === 0 || header.height === 0) return fail('zero size');
      if (expect !== null && (header.width !== expect.width || header.height !== expect.height)) return fail('size mismatch');
      if (header.depth !== 8) return fail('bit depth not 8');
      if (!Object.hasOwn(CHANNELS, header.colourType)) return fail('bad colour type');
      if (header.compression !== 0 || header.filter !== 0) return fail('bad compression/filter method');
      if (header.interlace !== 0) return fail('interlaced');
    } else if (type === 'PLTE') {
      if (palette !== null) return fail('PLTE twice');
      if (header.colourType !== 3) return fail('PLTE without type 3');
      if (idat.length > 0) return fail('PLTE after IDAT');
      if (len === 0 || len % 3 !== 0 || len > 768) return fail('bad PLTE');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) return fail('tRNS twice');
      if (idat.length > 0) return fail('tRNS after IDAT');
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null) return fail('tRNS before PLTE');
        if (len > palette.length / 3) return fail('tRNS longer than palette');
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) return fail('bad tRNS length');
        for (let i = 0; i < len; i += 2) if (data[i] !== 0) return fail('tRNS sample over 255');
      } else return fail(`tRNS with type ${ct}`);
      trns = data;
    } else if (type === 'IDAT') {
      if (idatDone) return fail('IDAT not in a row');
      if (header.colourType === 3 && palette === null) return fail('IDAT before PLTE');
      idat.push(data);
    } else {
      if (len !== 0) return fail('IEND not empty');
      ended = true;
    }
  }
  if (!ended) return fail('no IEND');
  if (idat.length === 0) return fail('no IDAT');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  let raw;
  try {
    raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  } catch (err) {
    return fail(`IDAT not one zlib stream: ${String(err && err.message).split('\n')[0]}`);
  }
  if (raw.length !== expected) return fail(`IDAT inflates to ${raw.length}, not ${expected}`);
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) return fail(`row ${y} filter ${ft}`);
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
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
  } else {
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
      if (e >= entries) return fail(`palette index ${e} out of range`);
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { ok: true, width, height, colourType, rgba };
}

// ---------------------------------------------------------------- analysis

function wordsOf(rgba) {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}

function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many
    ? null
    : [...counts.keys()].map((c) => {
        const b = new Uint8Array(Uint32Array.of(c).buffer);
        return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
      });
  return { opaque, grey, colours };
}

// The one fully transparent value the image may key by tRNS instead of an
// alpha channel: every pixel opaque or that exact value at alpha 0, and no
// opaque pixel of the same value. Null when there is none.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

// Palette entries: transparent ones first (by alpha), then by `order`:
// 'count' (most used first), 'luminance', or 'first' (first occurrence in
// scan order). A colour's index decides how well rows filter, so the order
// is worth trying more than one way.
function paletteOrder(colours, order, firstSeen) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    if (order === 'first') return firstSeen.get(x.word) - firstSeen.get(y.word);
    return y.count - x.count || x.word - y.word;
  });
}

function paletteForm(rgba, colours, order, firstSeen) {
  const entries = paletteOrder(colours, order, firstSeen);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { colourType: 3, bpp: 1, samples: indices, plte, trns };
}

function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    // First-occurrence positions, for the 'first' palette order.
    const firstSeen = new Map();
    const u32 = wordsOf(rgba);
    for (let i = 0; i < u32.length; i++) {
      if (!firstSeen.has(u32[i])) firstSeen.set(u32[i], i);
    }
    for (const order of ['count', 'luminance', 'first']) {
      forms.push({ ...paletteForm(rgba, colours, order, firstSeen), filters: order === 'luminance' ? [0, 'minsum', 'brute'] : [0] });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [4, 0, 'minsum', 'brute'], bruteLevel: BRUTE_LEVEL_CHANNEL });
  return forms;
}

// ---------------------------------------------------------------- filtering

const BRUTE_CONTEXT = 32768;
/** Level-4 brute force is cheap and near-optimal on small (palette) data; level-9 brute costs ~2x but picks better
    rows on full-size channel data, so channel forms use 9 and palette forms 4. */
const BRUTE_LEVEL_PALETTE = 4;
const BRUTE_LEVEL_CHANNEL = 9;

function filtered(samples, width, height, bpp, choice, raw = new Uint8Array(height * (width * bpp + 1)), bruteLevel = BRUTE_LEVEL_PALETTE) {
  const stride = width * bpp;
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else {
        cost = deflateSync(trial[t], before.length === 0 ? { level: bruteLevel, memLevel: 9 } : { level: bruteLevel, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------------------------------------------------------------- deflate

const SCREEN = { level: 6, memLevel: 8 };
const FINAL = { level: 9, memLevel: 9 };
const FINAL_FILTERED = { level: 9, memLevel: 9, strategy: constants.Z_FILTERED };

const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// One zlib stream of `data`, in 256 KiB segments, each block with its own
// Huffman table; the dictionary is kept across segments (one DeflateRaw
// state, Z_SYNC_FLUSH between segments). `strategy` per segment when given.
function segmentedZlib(data, segSize, strategy) {
  return new Promise((resolve, reject) => {
    const out = [];
    const df = new zlib.DeflateRaw({ level: 9, memLevel: 9 });
    df.on('data', (c) => out.push(c));
    df.on('error', reject);
    df.on('end', () => {
      const raw = Buffer.concat(out);
      const wrapped = Buffer.alloc(2 + raw.length + 4);
      wrapped[0] = 0x78;
      wrapped[1] = 0xda;
      raw.copy(wrapped, 2);
      wrapped.writeUInt32BE(adler32(data), 2 + raw.length);
      resolve(wrapped);
    });
    const segs = [];
    for (let off = 0; off < data.length; off += segSize) segs.push(data.subarray(off, Math.min(data.length, off + segSize)));
    let i = 0;
    (function step() {
      if (i >= segs.length) {
        df.end();
        return;
      }
      const go = () =>
        df.write(segs[i], () => {
          if (i === segs.length - 1) {
            i++;
            step();
          } else {
            df.flush(constants.Z_SYNC_FLUSH, () => {
              i++;
              step();
            });
          }
        });
      if (strategy !== null && strategy !== undefined) df.params(9, strategy, go);
      else go();
    })();
  });
}

// The smallest zlib stream of `data` over the tried encodings.
async function bestZlib(data) {
  let best = deflateSync(data, FINAL);
  const alt = deflateSync(data, FINAL_FILTERED);
  if (alt.length < best.length) best = alt;
  try {
    const seg = await segmentedZlib(data, 262144, constants.Z_FILTERED);
    if (seg.length < best.length) best = seg;
  } catch {
    // Streaming path unavailable: keep the sync winner.
  }
  try {
    const seg = await segmentedZlib(data, 262144, null);
    if (seg.length < best.length) best = seg;
  } catch {
    // Keep the sync winner.
  }
  return best;
}

function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------------------------------------------------------------- entry

async function encode(rgba, width, height) {
  let best = null;
  for (const form of formsOf(rgba)) {
    const size = height * (width * form.bpp + 1);
    const chunks = chunkBytes(form);
    // Stage 1: screen every filter choice at zlib level 6.
    const cands = [];
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice, new Uint8Array(size), form.bruteLevel ?? BRUTE_LEVEL_PALETTE);
      cands.push({ choice, data, l6: deflateSync(data, SCREEN).length + chunks });
    }
    cands.sort((a, b) => a.l6 - b.l6);
    // Stage 2: re-screen the best two at level 9 (default and filtered
    // strategies), because level 6 and level 9 do not always rank alike.
    const top = cands.slice(0, 2);
    for (const c of top) {
      c.l9 = Math.min(deflateSync(c.data, FINAL).length, deflateSync(c.data, FINAL_FILTERED).length) + chunks;
    }
    top.sort((a, b) => a.l9 - b.l9 || a.l6 - b.l6);
    const winner = top[0];
    if (best === null || winner.l9 < best.score) best = { form, choice: winner.choice, data: winner.data, score: winner.l9 };
  }
  const idat = await bestZlib(best.data);
  const png = pngOfForm(width, height, best.form, new Uint8Array(idat.buffer, idat.byteOffset, idat.length));
  return { png, colourType: best.form.colourType, choice: best.choice };
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DEBUG = process.env.MAKEFUN_DEBUG === '1';
for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  if (!image.ok) throw new Error(`${id}/image.png: ${image.why}`);
  mkdirSync(join(O, id), { recursive: true });
  const out = await encode(image.rgba, image.width, image.height);
  if (DEBUG) console.log(`${id}: ${out.png.length} bytes (type ${out.colourType}, filter ${out.choice})`);
  writeFileSync(join(O, id, 'image.png'), out.png);
}
