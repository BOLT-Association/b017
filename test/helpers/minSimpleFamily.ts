// The MinSimpleBOLT family adapter for the chain harness (zero-funding MinSimple, 37-arg unlock).
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import { PIECE_NAMES } from '../../src/lib/single/singleAncestor.js'
import { issuerPub, type Family } from './minSimpleChain.js'

const tpl = new MinSimpleTemplate()

export const minSimple: Family = {
  name: 'MinSimpleBOLT',
  lock: (owner, commitment, txoType, parent, gp) => tpl.lock(owner, issuerPub, commitment, txoType, parent, gp),
  unlock: (key, beneficiary, prevTxs) => tpl.unlock(key, beneficiary, prevTxs),
  melt: (key) => tpl.melt(key),
  pieceNames: PIECE_NAMES,
  ancestorStart: 0,
}
