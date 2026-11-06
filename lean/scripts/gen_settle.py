#!/usr/bin/env python3
"""Generate lean/BoltProof/Bridge/Glue/SimpleMulti/Settle.lean: the settle spends' vocabulary (the gate stack and the
outputs per mode, the grandparent outpoint the first rebuild derives, the alt-stack items), the structure EnforcedSettle,
its goal normaliser, and the three settle path theorems, from the folded-design probes F1_settle21, F7_settle23, F8_settle25."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chunks as C, facts as F
SP = WORK
ARMS = [(1961, 2426), (2591, 2609), (3186, 3623), (3773, 3790), (1426, 2715), (2715, 3897), (3899, 4652)]
UNFOLD = C.unfold(423, 5000, keep=ARMS)
def balanced(s, i):
    d = 0; k = i
    while True:
        if s[k] == '(': d += 1
        elif s[k] == ')':
            d -= 1
            if d == 0: return s[i:k+1]
        k += 1
def window(name, needle, span=600):
    lines = []; found = None
    with open(f'{SP}/{name}.out') as fh:
        for n, l in enumerate(fh):
            if found is None and needle in l: found = n
            if found is not None:
                lines.append(l)
                if n > found + span: break
    return ' '.join(' '.join(lines).split())
def zero_map(name):
    head = open(f'{SP}/{name}.out').read(400000)
    out = {}
    for _, a, b, w in re.findall(r'num2bin \[\] \(decode (\(encode (\d+)\)|\[(\d+)(?:, 0)?\])\)\.toNat = some (w✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*)', head):
        out[w] = f'zeros {a or b}'
    return out
def clean(s, zmap):
    for w, z in zmap.items(): s = s.replace(w, f'({z})')
    s = F.rename(s)
    s = re.sub(r'T\[(\d+)\]\?\.getD \[\]', r'(item T \1)', s)
    return s
MODES = [  # (probe, nty hex, spent ty hex, extra hypotheses, mode word)
    ('F1_settle21', 0x20, 0x21, [], 'transfer'),
    ('F7_settle23', 0x22, 0x23, [], 'split'),
    ('F8_settle25', 0x24, 0x25, [('hoi', 'decode f.outIdx = 0')], 'merge'),
]
reg = open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Regions.lean').read()
# the first rebuild's result items: `item T 2 :: (gpOutA) :: t0 :: T`, its alt stack `(a1) :: w46 :: A`
stA = re.search(r'def rebuildA_stack .*?:=\n  (.*)\n', reg).group(1)
gpA = balanced(stA, stA.index('(Hash.hash256 '))
wsA = re.search(r'def rebuildA_stack \(t0 : Bytes\) \(T : List Bytes\) \((.*?) : Bytes\)', reg).group(1).split()
thmA = reg[reg.index('theorem rebuildA_shape'):]
altA = balanced(thmA, thmA.index('(St (rebuildA_stack') + len('(St (rebuildA_stack'))  # skip; recompute below
m = re.search(r'run Eval\.opExec env k t \(St \(rebuildA_stack t0 T [^)]*\) (\(.*?\)) m\' C k\' cs\) = r := by', thmA)
altA = m.group(1)
while altA.startswith('(') and balanced(altA, 0) == altA: altA = altA[1:-1].strip()   # `a1 :: a2 :: A`
def split_cons(s):
    items = []; d = 0; cur = ''; j = 0
    while j < len(s):
        ch = s[j]
        if ch in '([': d += 1
        elif ch in ')]': d -= 1
        if d == 0 and s.startswith(' :: ', j): items.append(cur.strip()); cur = ''; j += 4; continue
        cur += ch; j += 1
    items.append(cur.strip()); return items
altItems = split_cons(altA)
assert altItems[-1] == 'A' and len(altItems) == 3, altItems[:1]
altA1, altA2 = altItems[0], altItems[1]
nA = len(re.findall(r'abbrev rebuildA_fact\d+', reg))
wsB1 = re.search(r'def rebuildB_1_stack \(t1 t0 a1 a2 : Bytes\) \(T : List Bytes\) \((.*?) : Bytes\)', reg).group(1).split()
wsB2 = re.search(r'def rebuildB_2_stack \(t1 t0 a1 a2 : Bytes\) \(T : List Bytes\) \((.*?) : Bytes\)', reg).group(1).split()
nB1 = len(re.findall(r'abbrev rebuildB_1_fact\d+', reg)); nB2 = len(re.findall(r'abbrev rebuildB_2_fact\d+', reg))
stB = {k: re.search(r'def rebuildB_%d_stack .*?:=\n  (.*)\n' % k, reg).group(1) for k in (1, 2)}
# item 0 of rebuildB_k_stack: `(t1 ++ (gpOutB))` for k=1 (this lineage's grandparent first), `(gpOutB ++ t1)`
# for k=2 (the other lineage's first: the spent lock's index is not zero, so the other input precedes it)
gpB = {}
for k in (1, 2):
    first = balanced(stB[k], 0)
    inner = first[1:-1]
    if k == 1:
        assert inner.startswith('t1 ++ '), inner[:20]
        gpB[k] = inner[len('t1 ++ '):]
    else:
        assert inner.endswith(' ++ t1'), inner[-20:]
        gpB[k] = inner[:-len(' ++ t1')]
out = []
out.append("""import BoltProof.Bridge.Glue.SimpleMulti.Enforced

/-!
# The settle spends

A settle spend (spent type odd, the next type the mode's settled type) rebuilds the ancestors from
the pieces when the token has a grandparent: `EnforcedSettle` is what the suffix then establishes,
`Enforced` with the null clause replaced by the regions' facts (`Regions.lean`) read on the stack at
the gate (`gateT`, by mode) and the grandparent outpoints the rebuilds derive (`gpOutA`,
`gpOutB`) in `hashPrevouts`. Without a grandparent the gate sends the run through the null arm instead:
`EnforcedSettle0` has the pieces empty and `hashPrevouts` over this outpoint and the funding outpoint.
The path theorems, in `Settle/{Transfer,Split,Merge}.lean` by mode, are the three settles with a
grandparent (`settle_<ty>_<nty>`) and without (`settle0_<ty>_<nty>`), the token at input 0; the split
theorems case on both split flags (`pkh1`, `i2`), the merge theorems with a grandparent on the spent lock's
output index, and every theorem on the input-index argument, which only sets the new token's index byte
(`inIdxByte`), so none fixes an argument; none assumes anything of the parent either (only the prologue's
issuer guard reads it). This file holds the vocabulary and the normalisers. Generated by the glue's `gen_settle.py` from the folded-design probes; regenerate rather
than edit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (reached_of_append scLen sc preVersion preHashPrevouts preOutpoint preValue
  preHashOutputs preSighashType encode_eq_one_iff encode_length_eq_nil_iff)

""")
gates = []; outs = []
for probe, nty, ty, extra, word in MODES:
    zmap = zero_map(probe)
    T = open(f'{SP}/{probe}.gateT.txt').read()
    T = clean(T, zmap)
    assert T.startswith('(') and T.endswith(')'); T = T[1:-1]
    gpat = '[1] :: f.gp :: [] :: f.parent ::'
    assert T.count(gpat) == 1, ('guard flag', nty, T.count(gpat))
    T = T.replace(gpat, '[1] :: f.gp :: encode (if decode f.parent = 0 then 1 else 0) :: f.parent ::')
    tpat = f':: f.outIdx :: [{ty}] :: f.ogp ::'
    assert T.count(tpat) == 1, ('spent type', nty, T.count(tpat))
    T = T.replace(tpat, ':: f.outIdx :: f.ty :: f.ogp ::')
    pat = f'[1, {nty}] ++ [1, 0]'
    assert pat in T, ('gate index byte', nty)
    T = T.replace(pat, f'[1, {nty}] ++ [1, inIdxByte a]')
    gates.append((nty, word))
    out.append(f'/-- The stack under the gate flag (suffix 1425) for a {word} settle (`nextTxoType = 0x{nty:x}`): the new token\'s varint, the mode flags, the bound, the pay-to-proof template, the scriptCode\'s pushes, the preimage\'s fields, the lock fields, the arguments, the pieces. -/')
    out.append(f'abbrev gateT_{nty:x} (f : Fields) (a : Args) (S : List Bytes) : List Bytes :=\n  {T}\n')
    of = open(f'{SP}/{probe}.outs.txt').read()
    lhs = of[of.index('Hash.hash256 (') + len('Hash.hash256 '):]
    lhs = balanced(lhs, 0)[1:-1]
    assert lhs.endswith(' ++ a.chg'), lhs[-40:]
    body = clean(lhs[:-len(' ++ a.chg')], zmap)
    pat = f'[1, {nty}] ++ [1, 0]'
    assert pat in body, ('outs index byte', nty)
    body = body.replace(pat, f'[1, {nty}] ++ [1, inIdxByte a]')
    outs.append(nty)
    if nty == 0x22:
        d = 0; cuts = []
        for i, c in enumerate(body):
            if c in '([': d += 1
            elif c in ')]': d -= 1
            elif d == 0 and body.startswith(' ++ (List.take 8', i): cuts.append(i)
        assert len(cuts) == 1, len(cuts)
        outA = body[:cuts[0]]; outB = body[cuts[0] + 4:]
        assert outB.startswith('(') and outB.endswith(')') and balanced(outB, 0) == outB
        outB = outB[1:-1]
        assert outB.count('[1, 34] ++ [1, 1]') == 1, outB.count('[1, 34] ++ [1, 1]')
        outB = outB.replace('[1, 34] ++ [1, 1]', '[1, 34] ++ [1, splitIdx a]')
        out.append('/-- The split settle\'s first token output: the remainder `bal - balCommit` to the first commitment, index byte 0. -/')
        out.append(f'abbrev splitOutA (f : Fields) (a : Args) : Bytes :=\n  {outA}\n')
        out.append('/-- The second token\'s index byte: 1 when the second interop slot `i2` is zero, else 0. -/')
        out.append('abbrev splitIdx (a : Args) : Nat :=\n  if decode a.i2 = 0 then 1 else 0\n')
        out.append('/-- The split settle\'s second token output: the committed balance to the second commitment, its index byte by `i2`. -/')
        out.append(f'abbrev splitOutB (f : Fields) (a : Args) : Bytes :=\n  {outB}\n')
        out.append('/-- The outputs of a split settle before the change blob: the two token outputs, in the order `pkh1` selects\n(the bytes leave both flags to the spender; the honest spend has both empty). -/')
        out.append('abbrev settleOuts_22 (f : Fields) (a : Args) : Bytes :=\n  if decode a.pkh1 = 0 then splitOutA f a ++ splitOutB f a else splitOutB f a ++ splitOutA f a\n')
    else:
        out.append(f'/-- The outputs of a {word} settle before the change blob. -/')
        out.append(f'abbrev settleOuts_{nty:x} (f : Fields) (a : Args) : Bytes :=\n  {body}\n')
sel = lambda prefix, args: ' else '.join(f'if a.nty = [0x{n:x}] then {prefix}_{n:x} {args}' for n, _ in gates[:-1]) + f' else {prefix}_{gates[-1][0]:x} {args}'
out.append(f'/-- The stack under the gate flag, by the next type. -/\nabbrev gateT (f : Fields) (a : Args) (S : List Bytes) : List Bytes :=\n  {sel("gateT", "f a S")}\n')
out.append(f'/-- The outputs of a settle before the change blob, by the next type. -/\nabbrev settleOuts (f : Fields) (a : Args) : Bytes :=\n  {sel("settleOuts", "f a")}\n')
wA = ' '.join(wsA)
out.append(f'/-- The grandparent outpoint the first rebuild derives: the rebuilt transaction\'s hash and the fifth interop slot. -/')
out.append(f'abbrev gpOutA (t0 : Bytes) (T : List Bytes) ({wA} : Bytes) : Bytes :=\n  {gpA}\n')
out.append(f'/-- The alt-stack items the first rebuild leaves for the second: the rebuilt unlocking script and 150 zero bytes. -/')
out.append(f'abbrev altA1 (t0 : Bytes) (T : List Bytes) ({wA} : Bytes) : Bytes :=\n  {altA1}\n')
out.append(f'abbrev altA2 ({wA} : Bytes) : Bytes :=\n  {altA2}\n')
for k in (1, 2):
    ws = ' '.join(wsB1 if k == 1 else wsB2)
    out.append(f'/-- The other grandparent outpoint the second rebuild derives (case {k}: the spent lock\'s index {"zero" if k == 1 else "non-zero"}). -/')
    out.append(f'abbrev gpOutB_{k} (t1 t0 a1 a2 : Bytes) (T : List Bytes) ({ws} : Bytes) : Bytes :=\n  {gpB[k]}\n')
factsA = ' ∧\n      '.join(f'rebuildA_fact{i} (preOutpoint a.pre) (gateT f a S) {wA}' for i in range(nA))
wB1 = ' '.join(wsB1); wB2 = ' '.join(wsB2)
argsB = f'(gpOutA (preOutpoint a.pre) (gateT f a S) {wA}) (preOutpoint a.pre) (altA1 (preOutpoint a.pre) (gateT f a S) {wA}) (altA2 {wA}) (gateT f a S)'
factsB1 = ' ∧\n        '.join(f'rebuildB_1_fact{i} {argsB} {wB1}' for i in range(nB1))
factsB2 = ' ∧\n        '.join(f'rebuildB_2_fact{i} {argsB} {wB2}' for i in range(nB2))
out.append(f"""/-- What the suffix enforces on a settle spend with a grandparent, the token at input 0. -/
structure EnforcedSettle (env : Env) (f : Fields) (a : Args) (S : List Bytes) (cs : Bytes) : Prop where
  pushTx : PushTxReached env a.pre cs
  version : 2 ≤ decode (preVersion a.pre)
  sighashType : preSighashType a.pre = [0x41]
  value : decode (preValue a.pre) = 1
  balLo : 0 ≤ decode f.bal
  balHi : decode f.bal ≤ maxBalance
  nbcLo : 0 ≤ decode a.nbc
  nbcHi : decode a.nbc ≤ maxBalance
  /-- a split or merge settle reads the carried balance (suffix 779–796, 933–949) -/
  balCommitLo : a.nty ≠ [0x20] → 0 ≤ decode f.balCommit
  /-- a split settle keeps a non-negative remainder -/
  splitRem : a.nty = [0x22] → 0 ≤ decode f.bal - decode f.balCommit
  /-- a merge settle keeps the sum within the bound -/
  mergeSum : a.nty = [0x24] → decode f.bal + decode f.balCommit ≤ maxBalance
  /-- the settled token (two for a split), then the change blob, hash to `hashOutputs` -/
  outputs : Hash.hash256 (settleOuts f a ++ a.chg) = preHashOutputs a.pre
  /-- the first rebuild's facts on the stack at the gate: the grandparent rebuilt from the pieces and hashed
  against `gp`, its balances anchored, the widths its `OP_NUM2BIN`s fixed; the second rebuild's facts under the
  merge flag and the spent lock's index; `hashPrevouts` over this outpoint, the rebuilt grandparents' outpoints
  and the funding outpoint, the other lineage's first when the spent lock's index is not zero -/
  rebuild : ∃ ({wA} {wB1} {wB2} : Bytes),
    ({factsA}) ∧
    (castToBool (item (gateT f a S) 2) = true → decode (item (gateT f a S) 39) = 0 →
      {factsB1}) ∧
    (castToBool (item (gateT f a S) 2) = true → ¬ decode (item (gateT f a S) 39) = 0 →
      {factsB2}) ∧
    Hash.hash256 (preOutpoint a.pre ++
      (if castToBool (item (gateT f a S) 2) = true then
        (if decode (item (gateT f a S) 39) = 0 then gpOutA (preOutpoint a.pre) (gateT f a S) {wA} ++ gpOutB_1 {argsB} {wB1}
          else gpOutB_2 {argsB} {wB2} ++ gpOutA (preOutpoint a.pre) (gateT f a S) {wA})
        else gpOutA (preOutpoint a.pre) (gateT f a S) {wA}) ++ a.fund) = preHashPrevouts a.pre
  issuer : GuardF f → f.issuer = a.pk ∧ a.nty ≠ [0x25] ∧ a.nty ≠ [0x27]
  owner : Hash.hash160 a.pk = f.pkh
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()

""")
names = re.findall(r'^(?:abbrev|def) (\w+)', reg, re.M)
names = [n for n in names if n.endswith('_stack') or '_fact' in n]
gnames = [f'gateT_{n:x}' for n, _ in gates] + ['gateT'] + [f'settleOuts_{n:x}' for n in outs] + ['settleOuts', 'splitOutA', 'splitOutB', 'gpOutA', 'altA1', 'altA2', 'gpOutB_1', 'gpOutB_2']
NORM = ('decode_lit, Nat.reduceLT, Int.reduceToNat, Int.toNat_natCast, Int.pred_toNat, decode_encode, castToBool_encode_ite, '
        'decide_eq_true_eq, ge_iff_le, encode_eq_one_iff, encode_length_eq_nil_iff, num2bin_nil_16, num2bin_nil_20, num2bin_nil_33, '
        'num2bin_nil_36, num2bin_nil_150, Option.some.injEq, encode_two, encode_three, encode_four, List.append_assoc, List.cons_append, '
        'List.nil_append, List.singleton_append, ' + ', '.join(names) + ', item, Pieces75.stack, List.getElem?_cons_succ, '
        'List.getElem?_cons_zero, Option.getD_some, Option.getD_none, zeros')
SETN = NORM.replace(', '.join(names), ', '.join(n for n in names if n.endswith('_stack'))) + (
    ', preOutpoint, preHashPrevouts, List.drop_drop, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, castToBool_nil, castToBool_one, eq_self_iff_true, false_implies, true_implies, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, '
    'not_true_eq_false, ↓reduceIte')
out.append(f"""open Lean Meta Elab Tactic in
/-- Closes an equation by the one hypothesis with the same right-hand side, matched at default transparency.
The rebuilt outpoints carry `if`s whose decidability instances `simp` keeps under casts, still naming the gate
stack's items unread, and the run's facts are equations in `Bytes` where `simp` rebuilds the goal's in `List Nat`;
reducible matching sees neither, and default matching is cheap once the right-hand side has picked the hypothesis. -/
elab "factD" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some (_, _, rhs) := tgt.eq? | throwError "factD: the goal is not an equation"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, _, r) := t.eq? then
      if r == rhs then
        if ← withTransparency .default (isDefEq t tgt) then
          g.assign d.toExpr
          replaceMainGoal []
          return
  throwError "factD: no hypothesis matches"

open Lean Elab Tactic in
/-- Selects the mode's gate stack and outputs in the goal from the `nextTxoType` hypothesis and, for a split, the\nflags' hypotheses. -/
elab "settleSel" hs:(colGt ident)* : tactic => do
  let extras ← hs.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  evalTactic (← `(tactic| simp (config := {{ decide := true, failIfUnchanged := false }}) only [gateT, settleOuts,
    gateT_20, gateT_22, gateT_24, settleOuts_20, settleOuts_22, settleOuts_24, splitOutA, splitOutB, splitIdx,
    inIdxByte, eq_self_iff_true, ↓reduceIte, $extras,*]))

/-- The settle paths' normaliser on the facts: `enforced_normF`'s set with the regions' facts kept folded (their
arguments are the gate stack and the derived outpoints), the concrete flags reduced and the vacuous arms dropped. -/
macro "settleNormF" h:ident : tactic =>
  `(tactic| (revert $h:ident; simp (config := {{ failIfUnchanged := false }}) only [{SETN}] at *; subst_vars; intro $h:ident))

/-- `settleNormF` with the null arm's fact opened, for the settles without a grandparent. -/
macro "settleNormF0" h:ident : tactic =>
  `(tactic| (revert $h:ident; simp (config := {{ failIfUnchanged := false }}) only [nullArm_fact0, {SETN}] at *; subst_vars; intro $h:ident))

/-- The same normaliser on the goal, the settle vocabulary unfolded first. -/
macro "settleNorm" : tactic =>
  `(tactic| simp (config := {{ failIfUnchanged := false }}) only [{', '.join(g for g in gnames if g not in ('gateT', 'settleOuts'))}, {SETN}])
""")
out.append("""/-- What the suffix enforces on a settle spend of a token without a grandparent, the token at input 0: the
prefix clauses and the settle outputs as in `EnforcedSettle`, the 150 pieces empty (the null arm, suffix
3899–4651) and `hashPrevouts` over this outpoint and the funding outpoint. -/
structure EnforcedSettle0 (env : Env) (f : Fields) (a : Args) (cs : Bytes) : Prop where
  pushTx : PushTxReached env a.pre cs
  version : 2 ≤ decode (preVersion a.pre)
  sighashType : preSighashType a.pre = [0x41]
  value : decode (preValue a.pre) = 1
  balLo : 0 ≤ decode f.bal
  balHi : decode f.bal ≤ maxBalance
  nbcLo : 0 ≤ decode a.nbc
  nbcHi : decode a.nbc ≤ maxBalance
  balCommitLo : a.nty ≠ [0x20] → 0 ≤ decode f.balCommit
  splitRem : a.nty = [0x22] → 0 ≤ decode f.bal - decode f.balCommit
  mergeSum : a.nty = [0x24] → decode f.bal + decode f.balCommit ≤ maxBalance
  outputs : Hash.hash256 (settleOuts f a ++ a.chg) = preHashOutputs a.pre
  /-- no grandparent: the pieces carry nothing -/
  null : nullCat a = []
  prevouts : Hash.hash256 (preOutpoint a.pre ++ a.fund) = preHashPrevouts a.pre
  issuer : GuardF f → f.issuer = a.pk ∧ a.nty ≠ [0x25] ∧ a.nty ≠ [0x27]
  owner : Hash.hash160 a.pk = f.pkh
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()
""")
out.append('end BoltProof.Glue.SimpleMulti\n')
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Settle.lean', 'w').write('\n'.join(out))

# ---- the path theorems, one per (spent commit type, next type), with and without a grandparent ----
COMMIT = {0x21: 'transfer', 0x23: 'split', 0x25: 'merge'}
SETTLE = {0x20: 'transfer', 0x22: 'split', 0x24: 'merge'}
def gp_thm(ty, nty):
    word = SETTLE[nty]
    extra = [('hoi', 'decode f.outIdx = 0')] if nty == 0x24 else []
    hyps = ' '.join(f'({h} : {p})' for h, p in extra)
    hnames = ' '.join(h for h, _ in extra)
    doc = (f'A {word} settle (`txoType = 0x{ty:x}`, `nextTxoType = 0x{nty:x}`)' if COMMIT[ty] == word else
           f'A {COMMIT[ty]} commit (`txoType = 0x{ty:x}`) settled as a {word} (`nextTxoType = 0x{nty:x}`)')
    return f"""/-- {doc} of a token with a grandparent, the token at input 0. -/
theorem settle_{ty:x}_{nty:x} {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{f : Fields}} {{a : Args}}
    {{S A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)
    (hpre : castToBool a.pre = true) (hvar : List.take 1 (List.drop 104 a.pre) = [0xfd])
    (hty : f.ty = [0x{ty:x}]) (hnty : a.nty = [0x{nty:x}]) (hgp : ¬ decode f.gp = 0)
    (hidx : decode a.inIdx = 0) {hyps}
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) : EnforcedSettle env f a S cs ∧ Ends env a k t r C cs := by
  obtain ⟨hguard, m', k', h⟩ := prologue he hact hpre h hr
  rw [suffix_drop_38_append, pushTxBlock_eq] at h
  have hpt : PushTxReached env a.pre cs := by
    obtain ⟨r', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr
    exact ⟨_, _, _, _, _, _, r', by simp [hact], hst, hok⟩
  replace h := pushTx_shape he (by simp [hact]) h hr
  obtain ⟨_, _, h⟩ := h
  simp only [stack38, guardFlag, hasGpFlag, {UNFOLD}, List.cons_append, List.nil_append] at h
  sym_all h hvar hty hnty hgp hidx {hnames}
  settleNormF h
  refine ⟨⟨hpt, (by factF), (by factF), (by factF), (by factF), (by factF), (by factF), (by factF),
    ?bcl, ?srem, ?msum, ?outs, ?reb, fun hG => hguard hG, (by factF), (by factF), (by factF), (by factF)⟩, _, _, _, _, h⟩
  case bcl => {'exact fun h0 => absurd hnty h0' if nty == 0x20 else 'exact fun _ => (by factF)'}
  case srem => {'exact fun _ => (by factF)' if nty == 0x22 else 'exact fun h0 => absurd (hnty.symm.trans h0) (by decide)'}
  case msum => {'exact fun _ => (by factF)' if nty == 0x24 else 'exact fun h0 => absurd (hnty.symm.trans h0) (by decide)'}
  case outs =>
    settleSel hnty
    settleNorm
    factF
  case reb =>
    settleSel hnty
    settleNorm
    refine ⟨{', '.join(['_'] * len(wsA) + (['_'] if nty == 0x24 else ['[]']) * len(wsB1) + ['[]'] * len(wsB2))},
      (by factF), {'(by factF)' if nty == 0x24 else 'trivial'}, {'(fun h0 => absurd hoi h0)' if nty == 0x24 else 'trivial'},
      {'(by simp only [ite_eq_left hoi, List.append_assoc]; factD)' if nty == 0x24 else '(by factD)'}⟩
"""

def nogp_thm(ty, nty):
    word = SETTLE[nty]
    extra = []
    hyps = ''
    hnames = ''
    doc = (f'A {word} settle (`txoType = 0x{ty:x}`, `nextTxoType = 0x{nty:x}`)' if COMMIT[ty] == word else
           f'A {COMMIT[ty]} commit (`txoType = 0x{ty:x}`) settled as a {word} (`nextTxoType = 0x{nty:x}`)')
    return f"""/-- {doc} of a token without a grandparent, the token at input 0. -/
theorem settle0_{ty:x}_{nty:x} {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{f : Fields}} {{a : Args}}
    {{S A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)
    (hpre : castToBool a.pre = true) (hvar : List.take 1 (List.drop 104 a.pre) = [0xfd])
    (hty : f.ty = [0x{ty:x}]) (hnty : a.nty = [0x{nty:x}]) (hgp0 : decode f.gp = 0)
    (hidx : decode a.inIdx = 0) {hyps}
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) : EnforcedSettle0 env f a cs ∧ Ends env a k t r C cs := by
  obtain ⟨hguard, m', k', h⟩ := prologue he hact hpre h hr
  rw [suffix_drop_38_append, pushTxBlock_eq] at h
  have hpt : PushTxReached env a.pre cs := by
    obtain ⟨r', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr
    exact ⟨_, _, _, _, _, _, r', by simp [hact], hst, hok⟩
  replace h := pushTx_shape he (by simp [hact]) h hr
  obtain ⟨_, _, h⟩ := h
  simp only [stack38, guardFlag, hasGpFlag, {UNFOLD}, List.cons_append, List.nil_append] at h
  sym_all h hvar hty hnty hgp0 hidx {hnames}
  settleNormF0 h
  refine ⟨⟨hpt, (by factF), (by factF), (by factF), (by factF), (by factF), (by factF), (by factF),
    ?bcl, ?srem, ?msum, ?outs, ?null, ?prev, fun hG => hguard hG, (by factF), (by factF), (by factF), (by factF)⟩,
    _, _, _, _, h⟩
  case bcl => {'exact fun h0 => absurd hnty h0' if nty == 0x20 else 'exact fun _ => (by factF)'}
  case srem => {'exact fun _ => (by factF)' if nty == 0x22 else 'exact fun h0 => absurd (hnty.symm.trans h0) (by decide)'}
  case msum => {'exact fun _ => (by factF)' if nty == 0x24 else 'exact fun h0 => absurd (hnty.symm.trans h0) (by decide)'}
  case outs =>
    settleSel hnty
    settleNorm
    factF
  case null => factF
  case prev =>
    settleNorm
    factD
"""

def split_cases(txt):
    """Case a split theorem on both flags: the script after the unfolding runs once per case."""
    head, tail = txt.split(' List.cons_append, List.nil_append] at h\n', 1)
    tail = tail.replace('settleSel hnty\n    settleNorm\n    factF', 'settleSel hnty hpk hi\n    settleNorm\n    factF')
    lines = tail.rstrip('\n').split('\n')
    lines[0] = lines[0] + ' hpk hi'   # the sym_all line
    assert lines[0].lstrip().startswith('sym_all')
    body = '\n'.join('  ' + l if l else l for l in lines)
    return (head + ' List.cons_append, List.nil_append] at h\n'
            '  by_cases hpk : decode a.pkh1 = 0 <;> by_cases hi : decode a.i2 = 0\n  all_goals\n' + body + '\n')

def merge_cases(txt):
    """Case the merge settle with a grandparent on the spent lock's output index: the second rebuild's two cases."""
    txt = txt.replace(' (hoi : decode f.outIdx = 0)', '')
    txt = txt.replace('of a token with a grandparent, the token at input 0. -/',
                      'of a token with a grandparent, the token at input 0, both cases of the spent lock\'s output index. -/')
    head, tail = txt.split(' List.cons_append, List.nil_append] at h\n', 1)
    tail = tail.rstrip('\n')
    pos = tail
    nA, nB = len(wsA), len(wsB1)
    wpos = 'refine ⟨' + ', '.join(['_'] * nA + ['_'] * nB + ['[]'] * nB) + ',\n'
    wneg = 'refine ⟨' + ', '.join(['_'] * nA + ['[]'] * nB + ['_'] * nB) + ',\n'
    assert wpos in pos, 'witnesses'
    neg = pos.replace(wpos, wneg)
    old_arms = '(by factF), (by factF), (fun h0 => absurd hoi h0),'
    assert old_arms in neg, 'arms'
    neg = neg.replace(old_arms, '(by factF), (fun h0 => absurd h0 hoi), (by factF),')
    assert 'ite_eq_left hoi' in neg
    neg = neg.replace('ite_eq_left hoi', 'ite_eq_right hoi')
    def bullet(t):
        ls = t.split('\n')
        return '\n'.join(['  · ' + ls[0].lstrip()] + ['  ' + l if l else l for l in ls[1:]])
    return (head + ' List.cons_append, List.nil_append] at h\n'
            '  by_cases hoi : decode f.outIdx = 0\n' + bullet(pos) + '\n' + bullet(neg) + '\n')

def idx_cases(txt):
    """Case a settle theorem on the input-index argument; the rest of the script runs once per case."""
    assert '    (hidx : decode a.inIdx = 0) ' in txt or '    (hidx : decode a.inIdx = 0)\n' in txt
    txt = txt.replace('    (hidx : decode a.inIdx = 0) ', '    ').replace('    (hidx : decode a.inIdx = 0)\n', '')
    txt = re.sub(r'\n {4}\n', '\n', txt)
    txt = txt.replace('the token at input 0', 'the token at input 0, a genesis parent or not, either value of the input-index argument')
    txt = txt.replace('settleSel hnty', 'settleSel hnty hty hidx')
    head, tail = txt.split(' List.cons_append, List.nil_append] at h\n', 1)
    lines = tail.rstrip('\n').split('\n')
    body = '\n'.join('  ' + l if l else l for l in lines)
    return (head + ' List.cons_append, List.nil_append] at h\n'
            '  by_cases hidx : decode a.inIdx = 0\n  all_goals\n' + body + '\n')

FHEAD = """import BoltProof.Bridge.Glue.SimpleMulti.Settle

/-!
# The {title}

{doc} Generated by the glue's `gen_settle.py`; regenerate rather than edit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (reached_of_append scLen sc preVersion preHashPrevouts preOutpoint preValue
  preHashOutputs preSighashType encode_eq_one_iff encode_length_eq_nil_iff)

"""
os.makedirs(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Settle', exist_ok=True)
for nty, fname in ((0x20, 'Transfer'), (0x22, 'Split'), (0x24, 'Merge')):
    body = FHEAD.format(title=f'{SETTLE[nty]} settles',
        doc=f'The {SETTLE[nty]} settle (`txoType = 0x{nty+1:x}`, `nextTxoType = 0x{nty:x}`), with and without a grandparent. The parity check (suffix 528) refuses a settle into another mode\'s type (`SimpleMulti/Refute.lean`).')
    for gp in (True, False):
        for ty in (nty + 1,):   # the parity check refuses the other commit types (SimpleMulti/Refute.lean)
            t = gp_thm(ty, nty) if gp else nogp_thm(ty, nty)
            if nty == 0x22: t = split_cases(t.replace('the token at input 0. -/', 'the token at input 0, both split flags in all four cases. -/'))
            if nty == 0x24 and gp: t = merge_cases(t)
            t = idx_cases(t)
            body += t + '\n'
    body += 'end BoltProof.Glue.SimpleMulti\n'
    open(f'{LEAN}/BoltProof/Bridge/Glue/SimpleMulti/Settle/{fname}.lean', 'w').write(body)
print('theorem files written')
