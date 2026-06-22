// SDK-version-independent counterfeit construction for the scanner tests.
//
// WHY raw-hex: @bsv/sdk 2.x's Transaction.toHex() does NOT re-serialise an output PUSHED onto a parsed
// tx's `.outputs` array (mutate-after-parse is dropped) — so the old `parse -> outputs.push -> toHex`
// tamper produced a BYTE-IDENTICAL tx under 2.x and the scanner (correctly) accepted a non-tampered tx,
// giving false "scanner accepts a counterfeit" failures. Building the counterfeit at the byte level is
// exactly what an on-the-wire counterfeiter does, and is robust across every @bsv/sdk version.
import { Transaction } from '@bsv/sdk';

const toLEHex = (n: number, bytes: number): string => {
  let h = '';
  for (let i = 0; i < bytes; i++) {
    h += (n & 0xff).toString(16).padStart(2, '0');
    n = Math.floor(n / 256);
  }
  return h;
};
const varInt = (n: number): string =>
  n < 0xfd ? toLEHex(n, 1) : n <= 0xffff ? 'fd' + toLEHex(n, 2) : 'fe' + toLEHex(n, 4);

/** Walk a raw tx hex to the byte offset (in hex chars) of its vout-count varint. */
function voutCountOffset(txHex: string): { at: number; count: number; after: number } {
  let p = 8; // skip version (4 bytes)
  const readVar = (): number => {
    const b = parseInt(txHex.slice(p, p + 2), 16);
    p += 2;
    if (b < 0xfd) return b;
    if (b === 0xfd) { const v = parseInt(txHex.slice(p + 2, p + 4) + txHex.slice(p, p + 2), 16); p += 4; return v; }
    if (b === 0xfe) { const v = parseInt(txHex.slice(p, p + 8).match(/../g)!.reverse().join(''), 16); p += 8; return v; }
    const v = Number(BigInt('0x' + txHex.slice(p, p + 16).match(/../g)!.reverse().join(''))); p += 16; return v;
  };
  const vin = readVar();
  for (let i = 0; i < vin; i++) {
    p += 72; // prevout (36 bytes)
    const sl = readVar();
    p += sl * 2; // scriptSig
    p += 8; // sequence (4 bytes)
  }
  const at = p;
  const count = readVar();
  return { at, count, after: p };
}

/** A serialised tx output: 8-byte LE satoshis + varint(scriptLen) + script. */
const serializeOutput = (scriptHex: string, sats: number): string =>
  toLEHex(sats, 8) + varInt(scriptHex.length / 2) + scriptHex;

/**
 * Append an extra output to a raw tx hex (bumping the vout-count varint and inserting the serialised
 * output before the 4-byte locktime). Pure byte surgery — independent of any @bsv/sdk version.
 */
export function appendOutput(txHex: string, scriptHex: string, sats = 0): string {
  const { at, count, after } = voutCountOffset(txHex);
  return (
    txHex.slice(0, at) +
    varInt(count + 1) +
    txHex.slice(after, txHex.length - 8) +
    serializeOutput(scriptHex, sats) +
    txHex.slice(-8)
  );
}

/** Sanity guard: appendOutput must actually add one parseable output (catches a version regression). */
export function assertOutputAdded(originalHex: string, tamperedHex: string): void {
  const a = Transaction.fromHex(originalHex).outputs.length;
  const b = Transaction.fromHex(tamperedHex).outputs.length;
  if (b !== a + 1) throw new Error(`appendOutput failed: ${a} -> ${b} outputs (expected +1)`);
}
