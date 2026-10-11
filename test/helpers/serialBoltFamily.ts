// The SerialBOLT family adapter for the chain harness (zero-funding NFT carrying its own mint outpoint, 38-arg
// unlock). The harness passes only (owner, commitment, txoType, parent, gp), so the adapter derives the genesis
// field from the lineage it builds: the mint (parent null) carries null; the genesis spend (gp null) carries the
// mint outpoint it spends (its parent); every later hop copies that root.
import SerialBoltTemplate from '../../src/tokens/templates/SerialBolt.sx.template.js'
import { SERIAL_PIECE_NAMES } from '../../src/lib/single/singleAncestor.js'
import { NULL_OUTPOINT } from '../../src/lib/genesis.js'
import { issuerPub, type Family } from './minSimpleChain.js'

export const tpl = new SerialBoltTemplate()
const isNull = (b: number[]) => b.every((x) => x === 0)

/** A SerialBOLT family whose mint carries `mintData` (default none). */
export function serialBoltFamily(mintData: number[] = []): Family {
  let root: number[] = [...NULL_OUTPOINT]
  return {
    name: 'SerialBOLT',
    lock: (owner, commitment, txoType, parent, gp) => {
      let genesis: number[]
      if (isNull(parent)) genesis = [...NULL_OUTPOINT]       // the mint
      else if (isNull(gp)) genesis = root = [...parent]       // the genesis spend: the mint outpoint it spends
      else genesis = root                                     // copied
      return tpl.lock(owner, issuerPub, commitment, txoType, parent, gp, genesis, mintData)
    },
    unlock: (key, beneficiary, prevTxs) => tpl.unlock(key, beneficiary, prevTxs),
    melt: (key) => tpl.melt(key),
    pieceNames: SERIAL_PIECE_NAMES,
    ancestorStart: 0,
  }
}

export const serialBolt: Family = serialBoltFamily()
