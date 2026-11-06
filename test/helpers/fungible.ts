// Shared fungible-token test helpers: the 16-byte little-endian balance the SimpleMultiBOLT family's lock carries,
// and a P2PKH source for a builder's mint to spend. About twenty suites still carry their own copy of these two;
// new suites import them from here, and the copies can be retired over time.
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'

const MASK64 = (1n << 64n) - 1n

/** A balance as the 16-byte little-endian field the fungible lock carries (the amount is taken mod 2^128). */
export function bal(amount: bigint): number[] {
  const x = amount & ((1n << 128n) - 1n)
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(x & MASK64, 0)
  b.writeBigUInt64LE(x >> 64n, 8)
  return Array.from(b)
}

/** A P2PKH output owned by `key`, for a builder's mint to spend (the builder finds its input by owner). */
export const freshSource = (key: PrivateKey, satoshis = 1000): Transaction =>
  new Transaction(1, [], [{ satoshis, change: true, lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])) }])
