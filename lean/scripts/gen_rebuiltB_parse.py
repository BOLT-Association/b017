import os as _os, re
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
# gen_rebuiltB_parse.py: the second rebuild's parse (RebuiltBParse.lean), token lemmas (AnchorB.lean) and
# widths (GpWeldB.lean), each the first rebuild's file read through the item map: the second rebuild reads the
# first piece set (item 62 + j = psA.p j, where the first rebuild reads item 137 + j = psB.p j), takes the two
# alt-stack items the first rebuild left (`a1`, the rebuilt key tail, and `a2`, the 150 empty pushes) in place of
# its key literal and `w46`, and sits two deeper on the stack (`(t1 :: t0 :: T)` for `(t0 :: T)`). Both of its
# cases (`rebuildB_1_*`, `rebuildB_2_*`) have the same bytes up to the width variables' names, so everything is
# stated for case 1 and case 2 is a `rfl` cast. Regenerate rather than edit the three files.
HERE = _os.path.dirname(_os.path.abspath(__file__))
R = open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Regions.lean').read()
def body(name):
    i = R.index('abbrev ' + name + ' ')
    return R[i:].split('\n')[1].strip()
def matchparen(t, j):
    d = 0
    for k in range(j, len(t)):
        if t[k] == '(': d += 1
        elif t[k] == ')':
            d -= 1
            if d == 0: return k
    raise Exception

def mapitem(n):
    n = int(n)
    return n - 75 if n >= 137 else n
def mapcons(n):  # (t0 :: T)[n] -> (t1 :: t0 :: T)[m]
    n = int(n)
    return n + 1 if n - 1 < 137 else n + 1 - 75

FACTMAP = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 12: 11}
WNAMES = ['w10', 'w11', 'w12', 'w13', 'w14', 'w17', 'w18', 'w19', 'w20', 'w23']

def transform(t):
    # the w46 fact becomes the alt-stack width hypothesis (and the key tail's width joins it)
    t = t.replace('(h11 : rebuildA_fact11 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)',
                  '(ha2 : a2.length = 150) (ha1 : a1.length ≤ 414)')
    t = t.replace('(h11 : rebuildA_fact11 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)',
                  '(ha2 : a2.length = 150) (ha1 : a1.length ≤ 414)')
    t = t.replace('(h11 : rebuildA_fact11 ARGS)', '(ha2 : a2.length = 150)')
    t = t.replace('(h12 : rebuildA_fact12 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)',
                  '(h11 : rebuildA_fact12 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)')
    t = t.replace('(t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes)', 'PARAMS')
    t = t.replace('t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46', 'ARGS')
    t = t.replace('t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46', 'GARGS')
    t = t.replace('{t0 : Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes}', '{t1 t0 a1 a2 : Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 : Bytes}')
    t = t.replace('{t0 : Bytes} {T : List Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes}', '{t1 t0 a1 a2 : Bytes} {T : List Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 : Bytes}')
    # the call sites of the widths: the empty pushes' and key tail's widths in place of the w46 fact
    t = t.replace('h3 h9 h11 (scA0_length_lt', 'h3 h9 ha2 (scA0_length_lt')
    t = t.replace('h5 h6 h7 h8 h11 hpn h15 h14', 'h5 h6 h7 h8 ha2 ha1 hpn h15 h14')
    t = t.replace('h2 h11 h (scA2_length_lt', 'h2 ha2 h (scA2_length_lt')
    t = t.replace('h2 h11 h hpn2 h15 h14', 'h2 ha2 ha1 h hpn2 h15 h14')
    t = t.replace('widthA_ver GARGS h12', 'widthA_ver GARGS h11')
    # the first rebuild names the grandparent; the second the other grandparent
    t = t.replace('rw [rebuildA_fact1_eq, gateT_item36] at h1', 'rw [rebuildA_fact1_eq, gateT_item41] at h1')
    t = t.replace('(htxid : txid G = List.take 32 f.gp)', '(htxid : txid G = List.take 32 f.ogp)')
    t = t.replace('a well-formed transaction whose txid is the spent token\'s\ngrandparent', 'a well-formed transaction whose txid is the spent token\'s\nother grandparent')
    t = t.replace('have h46 : w46.length = 150 := by\n    have := num2bin_length _ _ _ h11\n    rw [this]; decide', 'have h46 : a2.length = 150 := ha2')
    t = t.replace('have hw46 : w46.length = 150 := by rw [num2bin_length _ _ _ h11]; decide', 'have hw46 : a2.length = 150 := ha2')
    t = re.sub(r'rebuildA_fact(\d+)', lambda m: 'rebuildB_1_fact%d' % FACTMAP[int(m.group(1))], t)
    t = re.sub(r'item (T|\(gateT f a S\)) (\d+)', lambda m: 'item %s %d' % (m.group(1), mapitem(m.group(2))), t)
    t = re.sub(r'\(t0 :: T\)\[(\d+)\]\?', lambda m: '(t1 :: t0 :: T)[%d]?' % mapcons(m.group(1)), t)
    t = re.sub(r'gateT_item(\d+)', lambda m: 'gateT_item%d' % mapitem(m.group(1)), t)
    t = t.replace('a.psB', 'a.psA')
    t = t.replace('w46', 'a2')
    t = t.replace('GARGS', 't1 t0 a1 a2 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23')
    for old, new in [('rebuiltA', 'rebuiltB1'), ('scA0', 'scB0'), ('scA2', 'scB2'), ('lkA', 'lkB'), ('gpTxA', 'gpTxB'),
                     ('WidthsA', 'WidthsB'), ('widthA_', 'widthB_'), ('decode_rebuiltB1', 'decode_rebuiltB'),
                     ('secondInA', 'secondInB'), ('secondOutA', 'secondOutB'), ('LockWidthsA', 'LockWidthsB'),
                     ('gpFieldsA', 'gpFieldsB'), ('lockWidthsA_gate', 'lockWidthsB_gate'), ('widthsA_gate', 'widthsB_gate'),
                     ('gp_eq_gpTxB', 'gp_eq_gpTxB'), ('gpTxB_token', 'gpTxB_token'), ('scB0_length_lt', 'scB0_length_lt')]:
        t = t.replace(old, new)
    t = t.replace('gp_eq_gpTxA', 'gp_eq_gpTxB').replace('gpTxA_token', 'gpTxB_token')
    return t

P = '(t1 t0 a1 a2 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 : Bytes)'
A = 't1 t0 a1 a2 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23'
PA = '(t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes)'
AA = 't0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46'

# ---- the parse: from the template, over the second rebuild's facts (case 1, generic width names) -------------
def bfact(n):  # case-1 fact body with generic width names
    return re.sub(r'(w\d\d)c1\b', r'\1', body('rebuildB_1_fact%d' % n))
f3 = bfact(3)
pre = 'num2bin (encode ((List.length ('
assert f3.startswith(pre)
j = len(pre) - 1; k = matchparen(f3, j); SC0 = f3[j + 1:k]
f2 = bfact(2)
pre2 = 'castToBool (encode (if decode ((item T 107)) = 0 then 0 else 1)) = true → num2bin (encode ((('
assert f2.startswith(pre2), f2[:200]
j2 = len(pre2) - 1; k2 = matchparen(f2, j2); SC2 = f2[j2 + 1:k2]
assert SC2.endswith('++ a1'), SC2[-40:]

IN0 = "(item T 135 ++ ((253 :: List.take (((List.length w17 : Nat) : Int) - 1).toNat w17) ++ (scB0 ARGS ++ item T 108)))"
IN2 = "((t1 :: t0 :: T)[109]?.getD [] ++ ((253 :: List.take (((List.length w14 : Nat) : Int) - 1).toNat w14) ++ (scB2 ARGS ++ (t1 :: t0 :: T)[82]?.getD [])))"
IN1 = "(item T 79 ++ (encode ((item T 78).length : Int) ++ (item T 78 ++ item T 77)))"
O0 = "(item T 30 ++ (item T 0 ++ lkB T))"
O1 = "(item T 30 ++ (item T 12 ++ (item T 66 ++ [136, 172])))"
O2 = "((t1 :: t0 :: T)[32]?.getD [] ++ ((t1 :: t0 :: T)[14]?.getD [] ++ ((t1 :: t0 :: T)[67]?.getD [] ++ [136, 172])))"
O3 = "(item T 64 ++ ([25] ++ item T 63))"
lay = []
for x in (0, 1):
    for y in (0, 1):
        ins = "(%s ++ (%s ++ %s))" % (IN0, IN2, IN1) if y else "(%s ++ %s)" % (IN0, IN1)
        outs = "(%s ++ (%s ++ (%s ++ %s)))" % (O0, O1, O2, O3) if x else "(%s ++ (%s ++ %s))" % (O0, O1, O3)
        cin = 3 if y else 2; cout = 4 if x else 3
        h65 = "¬ decode (item T 65) = 0" if x else "decode (item T 65) = 0"
        h107 = "¬ decode (item T 107) = 0" if y else "decode (item T 107) = 0"
        desc = {(0, 0): 'neither optional arm', (1, 0): 'a second proof output', (0, 1): 'a second token input',
                (1, 1): 'a second token input and a second proof output'}[(x, y)]
        lay.append("""/-- The rebuilt other grandparent field by field, with %s. -/
theorem rebuiltB1_%d%d PARAMS (h65 : %s) (h107 : %s) :
    rebuiltB1 ARGS =
      item T 136 ++ ([%d] ++ (%s ++ ([%d] ++ (%s ++ item T 62)))) := by
  simp only [rebuiltB1, scB0, scB2, lkB, secondInB, secondOutB, h65, h107, encode_zero, castToBool_nil,
    castToBool_encode_one, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append,
    encode_two, encode_three, encode_four']
""" % (desc, x, y, h65, h107, cin, ins, cout, outs))

t = open(_os.path.join(HERE, 'rebuilt_tmpl.lean')).read()
# drop the first rebuild's own byte definition and hash equation: RebuiltB.lean has the second rebuild's
head_end = t.index('/-- The unlocking script the first rebuild assembles')
defs_start = t.index('/-- The bytes the first rebuild hashes')
t = t[:defs_start] + t[head_end:]
t = t.replace('LAYOUTS', '\n'.join(lay))
t = t.replace('SC0BYTES', SC0).replace('SC2BYTES', SC2)
t = transform(t)
t = t.replace('PARAMS', P).replace('ARGS', A)
# the layout theorems' flags
t = t.replace('by_cases h140 : decode (item T 65) = 0 <;> by_cases h182 : decode (item T 107) = 0',
              'by_cases h65 : decode (item T 65) = 0 <;> by_cases h107 : decode (item T 107) = 0')
t = re.sub(r'\bh140\b', 'h65', t); t = re.sub(r'\bh182\b', 'h107', t)
t = t.replace('rebuiltB_00 ' + A + ' h65 h107', 'rebuiltB_00 ' + A + ' h65 h107')
# imports, header and the shared helpers
t = t.replace('import BoltProof.Bridge.Glue.SimpleMulti.Regions\nimport BoltProof.Bridge.Glue.Refine.Parse\n',
              'import BoltProof.Bridge.Glue.SimpleMulti.Rebuilt\nimport BoltProof.Bridge.Glue.SimpleMulti.RebuiltB\n')
t = t.replace("theorem castToBool_encode_one : castToBool (encode 1) = true := by decide\ntheorem encode_four' : encode 4 = [4] := by decide\n\n", '')
hdr_start = t.index('/-!'); hdr_end = t.index('-/', hdr_start) + 2
t = t[:hdr_start] + """/-!
# The second rebuild's bytes, parsed

The second rebuild (suffix 2715–3896, a merge settle's) hashes the other lineage's grandparent, assembled from
the first piece set and the spend's own fields, and compares the hash with the token's `otherGrandparent`
(`rebuildB_k_fact1`). This file is `Rebuilt.lean` for those bytes: the layout for each optional arm
(`rebuiltB1_00` … `rebuiltB1_11`, the flags at items 65 and 107), the two unlocking scripts (`scB0`, `scB2`), the
token's lock (`lkB`, items 67–76 with the spend's issuer push and suffix), the parsed transaction (`gpTxB`) and
its widths (`WidthsB`), and the parse (`decode_rebuiltB`). The first rebuild's key literal and 150 empty pushes
are here the alt-stack items `a1` and `a2` it left. Both cases of the second rebuild have these bytes up to the
width variables' names (`rebuiltB2_eq`). Generated by the glue's `gen_rebuiltB_parse.py`; regenerate rather
than edit.
-/""" + t[hdr_end:]
t = t.replace('/-- The unlocking script the first rebuild assembles for the grandparent\'s first input: 150 empty pushes,\nthe grandparent spend\'s own arguments, its preimage with the settled token\'s lock, its `OP_PUSH_TX` key. -/',
              '/-- The unlocking script the second rebuild assembles for the other grandparent\'s first input: the 150 empty\npushes (`a2`), the spend\'s own arguments, its preimage with the settled token\'s lock, the key tail (`a1`). -/')
t = t.replace('/-- The unlocking script of the grandparent\'s optional second token input, from the pieces at depths 156–181. -/',
              '/-- The unlocking script of the other grandparent\'s optional second token input, from the pieces at depths 81–106. -/')
t = t.replace('/-- The commit token\'s lock in the rebuilt grandparent: the pieces at depths 142–151, then the spend\'s own\nissuer push and suffix. -/',
              '/-- The commit token\'s lock in the rebuilt other grandparent: the pieces at depths 67–76, then the spend\'s own\nissuer push and suffix. -/')
t = t.replace('/-- The rebuilt grandparent as `decodeTx` reads it', '/-- The rebuilt other grandparent as `decodeTx` reads it')
t = t.replace('/-- The widths the parse of the rebuilt grandparent reads. -/', '/-- The widths the parse of the rebuilt other grandparent reads. -/')
t = t.replace('/-- **The first rebuild, parsed**: the bytes it hashes read as `gpTxB`. -/', '/-- **The second rebuild, parsed**: the bytes it hashes read as `gpTxB`. -/')
t = t.replace('/-- The version\'s width, from the run (fact 12). -/', '/-- The version\'s width, from the run (fact 11). -/')
t = t.replace('/-- The first input\'s varint, from the run (facts 3, 9 and 11): the length word the rebuild measured, below\nthe two-byte bound. -/',
              '/-- The first input\'s varint, from the run (facts 3 and 9) and the width of the empty pushes: the length word the\nrebuild measured, below the two-byte bound. -/')
t = t.replace('/-- The second token input\'s varint, from the run (facts 2 and 11), below the two-byte bound. -/',
              '/-- The second token input\'s varint, from the run (fact 2) and the width of the empty pushes, below the two-byte\nbound. -/')
# case 2 is case 1 with the widths renamed
IP = '{t1 t0 a1 a2 : Bytes} {T : List Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 : Bytes}'
iffs = '\n'.join('theorem rebuildB_2_fact%d_iff %s : rebuildB_2_fact%d %s ↔ rebuildB_1_fact%d %s := Iff.rfl' % (n, IP, n, A, n, A)
               for n in range(12))
t = t.replace('end BoltProof.Glue.SimpleMulti', """/-- The second case's bytes and facts are the first case's, the width variables renamed. -/
theorem rebuiltB2_eq %s : rebuiltB2 %s = rebuiltB1 %s := rfl

%s

end BoltProof.Glue.SimpleMulti""" % (P, A, A, iffs))
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/RebuiltBParse.lean', 'w').write(t)

# ---- the token lemmas and the widths, from the first rebuild's files ----------------------------------------------
an = open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Anchor.lean').read()
i0 = an.index('/-- The grandparent token\'s fields as the first rebuild\'s pieces name them')
i1 = an.index('/-- A script shorter than the lock is no token. -/')
j0 = an.index('/-- The parsed grandparent\'s token: its first output, and no other. -/')
j1 = an.index('/-- **The anchor is the settled balance.**')
an_b = transform(an[i0:i1] + an[j0:j1])
an_b = an_b.replace('as the first rebuild\'s pieces name them', 'as the second rebuild\'s pieces name them')
an_b = an_b.replace('/-- The parsed grandparent\'s token', '/-- The parsed other grandparent\'s token')
an_b = an_b.replace('/-- The grandparent token\'s pieces at their push widths. -/', '/-- The other grandparent token\'s pieces at their push widths. -/')
an_b = an_b.replace('PARAMS', P).replace('ARGS', A)
anchorB = """import BoltProof.Bridge.Glue.SimpleMulti.RebuiltBParse
import BoltProof.Bridge.Glue.SimpleMulti.Anchor

/-!
# The rebuilt other grandparent's token

`Anchor.lean` for the second rebuild: the other grandparent's commit token is the pieces at depths 67–76 with the
spend's own issuer push and suffix (`lkB`), the fungible lock of `gpFieldsB` at the pieces' widths (`lkB_eq`), so
the parsed other grandparent's first output is that token and its other outputs are not tokens (`gpTxB_token`).
Generated by the glue's `gen_rebuiltB_parse.py`; regenerate rather than edit.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated

""" + an_b + "\nend BoltProof.Glue.SimpleMulti\n"
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/AnchorB.lean', 'w').write(anchorB)

gw = open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/GpWeld.lean').read()
k0 = gw.index('/-- The first input\'s unlocking script is under the two-byte varint bound')
k1 = gw.index('/-- The second piece set at the widths of the fields the first rebuild reads it as')
k2 = gw.index('theorem lockWidthsA_gate')
k3 = gw.index('end BoltProof.Glue.SimpleMulti')
gw_b = transform(gw[k0:k1] + gw[k2:k3]).replace('PARAMS', P).replace('ARGS', A)
weldB = """import BoltProof.Bridge.Glue.SimpleMulti.AnchorB
import BoltProof.Bridge.Glue.SimpleMulti.GpWeld

/-!
# The second rebuild's widths, from the run and the pieces

`GpWeld.lean` for the second rebuild: `decode_rebuiltB` reads the other grandparent under `WidthsB`, derived here
from the run's facts (the version, the scripts' varints, given the scripts are under 65536 bytes), the spend's
own fields (the token value, the lock-length varint, the proof template), the two alt-stack items' widths and the
first piece set's widths (`HonestPiecesB a.psA`). `gp_eq_gpTxB` then identifies a real other grandparent with the
parsed one. Generated by the glue's `gen_rebuiltB_parse.py`; regenerate rather than edit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (sc scLen)

""" + gw_b + "\nend BoltProof.Glue.SimpleMulti\n"
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/GpWeldB.lean', 'w').write(weldB)
print('ok')
