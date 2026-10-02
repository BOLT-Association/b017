// The AuthBolt family adapter for the chain harness (zero-funding + authOrMiscData, 39-arg unlock).
import AuthBoltTemplate from '../../src/tokens/templates/AuthBolt.sx.template.js'
import { AUTH_PIECE_NAMES } from '../../src/lib/single/singleAncestor.js'
import { issuerPub, type Family } from './minSimpleChain.js'

export const tpl = new AuthBoltTemplate()

export const authBolt: Family = {
  name: 'AuthBOLT',
  lock: (owner, commitment, txoType, parent, gp) => tpl.lock(owner, issuerPub, commitment, txoType, parent, gp),
  unlock: (key, beneficiary, prevTxs, auth) => tpl.unlock(key, beneficiary, prevTxs, auth),
  pieceNames: AUTH_PIECE_NAMES,
  ancestorStart: 1, // [0] = authOrMiscData, then the 27 ancestor pieces
}
