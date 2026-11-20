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
ARMS = [(1908, 2354), (2500, 2518), (3072, 3491), (3623, 3640), (1392, 2624), (2624, 3740), (3742, 4465)]
UNFOLD = C.unfold(423, 5000, keep=ARMS)
def balanced(s, i):
    d = 0; k = i
    while True:
        if s[k] == '(': d += 1
        elif s[k] == ')':
            d -= 1
            if d == 0: return s[i:k+1]
        k += 1
def zero_map(name):
    """The zero pads the probe names (`<name>.zeros.txt`, written by extract_settle_inputs.py), in file order: the
    order matters, since a longer name is listed before its prefix (`w✝³⁴` before `w✝³`)."""
    out = {}
    for line in open(f'{SP}/{name}.zeros.txt', encoding='utf-8'):
        if line.strip():
            w, n = line.split()
            out[w] = f'zeros {int(n)}'
    assert out, (name, 'no zero pads')
    return out
def clean(s, zmap):
    for w, z in zmap.items(): s = s.replace(w, f'({z})')
    s = F.rename(s)
    s = re.sub(r'T\[(\d+)\]\?\.getD \[\]', r'(item T \1)', s)
    return s
MODES = [  # (probe, nty hex, spent ty hex, extra hypotheses, mode word)
    ('F1_settle21', 0x20, 0x21, [], 'transfer'),
    ('F7_settle23', 0x22, 0x23, [], 'split'),
    ('F8_settle25', 0x24, 0x25, [], 'merge'),
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
nB1 = len(re.findall(r'abbrev rebuildB_1_fact\d+', reg))
assert 'rebuildB_2_' not in reg, 'the second rebuild has one case (the merge flag on) since the outputIndexN removal'
stB1 = re.search(r'def rebuildB_1_stack .*?:=\n  (.*)\n', reg).group(1)
# item 0 of rebuildB_1_stack: `(t1 ++ (gpOutB))`, this lineage's grandparent first. (Until the outputIndexN removal a
# second case put the other lineage's first when the spent lock's index byte was not zero.)
first = balanced(stB1, 0)
inner = first[1:-1]
assert inner.startswith('t1 ++ '), inner[:20]
gpB1 = inner[len('t1 ++ '):]
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
theorems case on the order flag `pkh1`. No theorem fixes the input-index argument or the second split flag `i2`:
since the outputIndexN removal the settle reads neither (they only set the new tokens' index bytes), and none
assumes anything of the parent either (only the prologue's issuer guard reads it). This file holds the vocabulary and the normalisers. Generated by the glue's `gen_settle.py` from the folded-design probes; regenerate rather
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
    T = open(f'{SP}/{probe}.gateT.txt', encoding='utf-8').read()
    T = clean(T, zmap)
    assert T.startswith('(') and T.endswith(')'); T = T[1:-1]
    gpat = '[1] :: f.gp :: [] :: f.parent ::'
    assert T.count(gpat) == 1, ('guard flag', nty, T.count(gpat))
    T = T.replace(gpat, '[1] :: f.gp :: encode (if decode f.parent = 0 then 1 else 0) :: f.parent ::')
    tpat = f':: f.parent :: [{ty}] :: f.ogp ::'
    assert T.count(tpat) == 1, ('spent type', nty, T.count(tpat))
    T = T.replace(tpat, ':: f.parent :: f.ty :: f.ogp ::')
    # the new token's type push is followed by its parent outpoint push: no index byte (the arguments themselves,
    # `a.inIdx` among them, are still on the stack)
    assert f'[1, {nty}] ++ 36 :: ' in T and f'[1, {nty}] ++ [1, ' not in T and 'outIdx' not in T, ('index byte', nty)
    gates.append((nty, word))
    out.append(f'/-- The stack under the gate flag (suffix 1391) for a {word} settle (`nextTxoType = 0x{nty:x}`): the new token\'s varint, the mode flags, the bound, the pay-to-proof template, the scriptCode\'s pushes, the preimage\'s fields, the lock fields, the arguments, the pieces. -/')
    out.append(f'abbrev gateT_{nty:x} (f : Fields) (a : Args) (S : List Bytes) : List Bytes :=\n  {T}\n')
    of = open(f'{SP}/{probe}.outs.txt', encoding='utf-8').read()
    lhs = of[of.index('Hash.hash256 (') + len('Hash.hash256 '):]
    lhs = balanced(lhs, 0)[1:-1]
    assert lhs.endswith(' ++ a.chg'), lhs[-40:]
    body = clean(lhs[:-len(' ++ a.chg')], zmap)
    assert f'[1, {nty}] ++ [1, ' not in body and '[1, 34] ++ [1, ' not in body and 'inIdx' not in body and 'a.i2' not in body, ('index byte', nty)
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
        out.append('/-- The split settle\'s first token output: the remainder `bal - balCommit` to the first commitment. -/')
        out.append(f'abbrev splitOutA (f : Fields) (a : Args) : Bytes :=\n  {outA}\n')
        out.append('/-- The split settle\'s second token output: the committed balance to the second commitment. -/')
        out.append(f'abbrev splitOutB (f : Fields) (a : Args) : Bytes :=\n  {outB}\n')
        out.append('/-- The outputs of a split settle before the change blob: the two token outputs, in the order `pkh1` selects\n(the bytes leave the flag to the spender; the honest spend has it empty). -/')
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
out.append(f'/-- The alt-stack items the first rebuild leaves for the second: the rebuilt unlocking script and 144 zero bytes. -/')
out.append(f'abbrev altA1 (t0 : Bytes) (T : List Bytes) ({wA} : Bytes) : Bytes :=\n  {altA1}\n')
out.append(f'abbrev altA2 ({wA} : Bytes) : Bytes :=\n  {altA2}\n')
out.append('/-- The other grandparent outpoint the second rebuild derives (the merge flag on). -/')
out.append(f'abbrev gpOutB_1 (t1 t0 a1 a2 : Bytes) (T : List Bytes) ({" ".join(wsB1)} : Bytes) : Bytes :=\n  {gpB1}\n')
factsA = ' ∧\n      '.join(f'rebuildA_fact{i} (preOutpoint a.pre) (gateT f a S) {wA}' for i in range(nA))
wB1 = ' '.join(wsB1)
argsB = f'(gpOutA (preOutpoint a.pre) (gateT f a S) {wA}) (preOutpoint a.pre) (altA1 (preOutpoint a.pre) (gateT f a S) {wA}) (altA2 {wA}) (gateT f a S)'
factsB1 = ' ∧\n        '.join(f'rebuildB_1_fact{i} {argsB} {wB1}' for i in range(nB1))
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
  /-- a split or merge settle reads the carried balance (suffix 779–794, 933–947) -/
  balCommitLo : a.nty ≠ [0x20] → 0 ≤ decode f.balCommit
  /-- a split settle keeps a non-negative remainder -/
  splitRem : a.nty = [0x22] → 0 ≤ decode f.bal - decode f.balCommit
  /-- a merge settle keeps the sum within the bound -/
  mergeSum : a.nty = [0x24] → decode f.bal + decode f.balCommit ≤ maxBalance
  /-- the settled token (two for a split), then the change blob, hash to `hashOutputs` -/
  outputs : Hash.hash256 (settleOuts f a ++ a.chg) = preHashOutputs a.pre
  /-- the first rebuild's facts on the stack at the gate: the grandparent rebuilt from the pieces and hashed
  against `gp`, its balances anchored, the widths its `OP_NUM2BIN`s fixed; the second rebuild's facts under the
  merge flag; `hashPrevouts` over this outpoint, the rebuilt grandparents' outpoints (this lineage's first) and
  the funding outpoint -/
  rebuild : ∃ ({wA} {wB1} : Bytes),
    ({factsA}) ∧
    (castToBool (item (gateT f a S) 2) = true →
      {factsB1}) ∧
    Hash.hash256 (preOutpoint a.pre ++
      (if castToBool (item (gateT f a S) 2) = true then
        gpOutA (preOutpoint a.pre) (gateT f a S) {wA} ++ gpOutB_1 {argsB} {wB1}
        else gpOutA (preOutpoint a.pre) (gateT f a S) {wA}) ++ a.fund) = preHashPrevouts a.pre
  issuer : GuardF f → f.issuer = a.pk ∧ a.nty ≠ [0x25] ∧ a.nty ≠ [0x27]
  owner : Hash.hash160 a.pk = f.pkh
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()

""")
names = re.findall(r'^(?:abbrev|def) (\w+)', reg, re.M)
names = [n for n in names if n.endswith('_stack') or '_fact' in n]
gnames = [f'gateT_{n:x}' for n, _ in gates] + ['gateT'] + [f'settleOuts_{n:x}' for n in outs] + ['settleOuts', 'splitOutA', 'splitOutB', 'gpOutA', 'altA1', 'altA2', 'gpOutB_1']
NORM = ('decode_lit, Nat.reduceLT, Int.reduceToNat, Int.toNat_natCast, Int.pred_toNat, decode_encode, castToBool_encode_ite, '
        'decide_eq_true_eq, ge_iff_le, encode_eq_one_iff, encode_length_eq_nil_iff, num2bin_nil_16, num2bin_nil_20, num2bin_nil_33, '
        'num2bin_nil_36, num2bin_nil_144, Option.some.injEq, encode_two, encode_three, encode_four, List.append_assoc, List.cons_append, '
        'List.nil_append, List.singleton_append, ' + ', '.join(names) + ', item, Pieces72.stack, List.getElem?_cons_succ, '
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
    gateT_20, gateT_22, gateT_24, settleOuts_20, settleOuts_22, settleOuts_24, splitOutA, splitOutB,
    eq_self_iff_true, ↓reduceIte, $extras,*]))

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
prefix clauses and the settle outputs as in `EnforcedSettle`, the 144 pieces empty (the null arm, suffix
3742–4464) and `hashPrevouts` over this outpoint and the funding outpoint. -/
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
    extra = []
    hyps = ' '.join(f'({h} : {p})' for h, p in extra)
    hnames = ' '.join(h for h, _ in extra)
    doc = (f'A {word} settle (`txoType = 0x{ty:x}`, `nextTxoType = 0x{nty:x}`)' if COMMIT[ty] == word else
           f'A {COMMIT[ty]} commit (`txoType = 0x{ty:x}`) settled as a {word} (`nextTxoType = 0x{nty:x}`)')
    return f"""/-- {doc} of a token with a grandparent, the token at input 0. -/
theorem settle_{ty:x}_{nty:x} {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{f : Fields}} {{a : Args}}
    {{S A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)
    (hpre : castToBool a.pre = true) (hvar : List.take 1 (List.drop 104 a.pre) = [0xfd])
    (hty : f.ty = [0x{ty:x}]) (hnty : a.nty = [0x{nty:x}]) (hgp : ¬ decode f.gp = 0) {hyps}
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
  sym_all h hvar hty hnty hgp {hnames}
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
    refine ⟨{', '.join(['_'] * len(wsA) + (['_'] if nty == 0x24 else ['[]']) * len(wsB1))},
      (by factF), {'(by factF)' if nty == 0x24 else 'trivial'}, (by factD)⟩
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
    (hty : f.ty = [0x{ty:x}]) (hnty : a.nty = [0x{nty:x}]) (hgp0 : decode f.gp = 0) {hyps}
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
  sym_all h hvar hty hnty hgp0 {hnames}
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
    """Case a split theorem on the order flag `pkh1`: the script after the unfolding runs once per case."""
    head, tail = txt.split(' List.cons_append, List.nil_append] at h\n', 1)
    tail = tail.replace('settleSel hnty\n    settleNorm\n    factF', 'settleSel hnty hpk\n    settleNorm\n    factF')
    lines = tail.rstrip('\n').split('\n')
    lines[0] = lines[0] + ' hpk'   # the sym_all line
    assert lines[0].lstrip().startswith('sym_all')
    body = '\n'.join('  ' + l if l else l for l in lines)
    return (head + ' List.cons_append, List.nil_append] at h\n'
            '  by_cases hpk : decode a.pkh1 = 0\n  all_goals\n' + body + '\n')

def any_idx(txt):
    """The docstring of a settle theorem: it covers a genesis parent or not and every input-index argument (nothing
    reads it). The spent type's hypothesis also selects the gate stack's `f.ty`."""
    txt = txt.replace('settleSel hnty', 'settleSel hnty hty')
    txt = re.sub(r' +\n', '\n', txt)
    return txt.replace('the token at input 0', 'the token at input 0, a genesis parent or not, either value of the input-index argument')

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
        doc=f'The {SETTLE[nty]} settle (`txoType = 0x{nty+1:x}`, `nextTxoType = 0x{nty:x}`), with and without a grandparent. The parity check (suffix 526) refuses a settle into another mode\'s type (`SimpleMulti/Refute.lean`).')
    for gp in (True, False):
        for ty in (nty + 1,):   # the parity check refuses the other commit types (SimpleMulti/Refute.lean)
            t = gp_thm(ty, nty) if gp else nogp_thm(ty, nty)
            if nty == 0x22: t = split_cases(t.replace('the token at input 0. -/', 'the token at input 0, both orders of the split flag. -/'))
            t = any_idx(t)
            body += t + '\n'
    body += 'end BoltProof.Glue.SimpleMulti\n'
    open(f'{LEAN}/BoltProof/Bridge/Glue/SimpleMulti/Settle/{fname}.lean', 'w').write(body)
print('theorem files written')
