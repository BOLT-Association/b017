import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re, sys
DIR=WORK + '/'
R=LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Regions.lean'
s=open(R).read()
def body(name):
    i=s.index('abbrev '+name+' ')
    return s[i:].split('\n')[1].strip()
def matchparen(t,j):
    d=0
    for k in range(j,len(t)):
        if t[k]=='(':d+=1
        elif t[k]==')':
            d-=1
            if d==0: return k
    raise Exception
f1=body('rebuildA_fact1')
assert f1.startswith('Hash.hash256 (')
j=f1.index('(')
k=matchparen(f1,j)
X=f1[j+1:k]
assert f1[k+1:].strip()=='= List.take 32 ((item T 35))', f1[k+1:]
f3=body('rebuildA_fact3')
pre='num2bin (encode ((List.length ('
assert f3.startswith(pre)
j=len(pre)-1
k=matchparen(f3,j)
SC=f3[j+1:k]
f2=body('rebuildA_fact2')
pre2='castToBool (encode (if decode ((item T 175)) = 0 then 0 else 1)) = true → num2bin (encode ((('
assert f2.startswith(pre2), f2[:200]
j2=len(pre2)-1
k2=matchparen(f2,j2)
SC2=f2[j2+1:k2]
assert SC2.endswith('[171, 173, 104])'), SC2[-50:]
P='(t0 : Bytes) (T : List Bytes) (w8 w9 w10 w11 w12 w15 w16 w17 w18 w19 w42 : Bytes)'
A='t0 T w8 w9 w10 w11 w12 w15 w16 w17 w18 w19 w42'

IN0="(item T 202 ++ ((253 :: List.take (((List.length w15 : Nat) : Int) - 1).toNat w15) ++ (scA0 ARGS ++ item T 176)))"
IN2="((t0 :: T)[176]?.getD [] ++ ((253 :: List.take (((List.length w12 : Nat) : Int) - 1).toNat w12) ++ (scA2 ARGS ++ (t0 :: T)[150]?.getD [])))"
IN1="(item T 148 ++ (encode ((item T 147).length : Int) ++ (item T 147 ++ item T 146)))"
O0="(item T 29 ++ (item T 0 ++ lkA T))"
O1="(item T 29 ++ (item T 12 ++ (item T 136 ++ [136, 172])))"
O2="((t0 :: T)[30]?.getD [] ++ ((t0 :: T)[13]?.getD [] ++ ((t0 :: T)[136]?.getD [] ++ [136, 172])))"
O3="(item T 134 ++ ([25] ++ item T 133))"
lay=[]
for x in (0,1):
  for y in (0,1):
    ins = "(%s ++ (%s ++ %s))"%(IN0,IN2,IN1) if y else "(%s ++ %s)"%(IN0,IN1)
    outs = "(%s ++ (%s ++ (%s ++ %s)))"%(O0,O1,O2,O3) if x else "(%s ++ (%s ++ %s))"%(O0,O1,O3)
    cin = 3 if y else 2; cout = 4 if x else 3
    h140 = "¬ decode (item T 135) = 0" if x else "decode (item T 135) = 0"
    h182 = "¬ decode (item T 175) = 0" if y else "decode (item T 175) = 0"
    desc = {(0,0):'neither optional arm',(1,0):'a second proof output',(0,1):'a second token input',(1,1):'a second token input and a second proof output'}[(x,y)]
    lay.append("""/-- The rebuilt grandparent field by field, with %s. -/
theorem rebuiltA_%d%d PARAMS (h140 : %s) (h182 : %s) :
    rebuiltA ARGS =
      item T 203 ++ ([%d] ++ (%s ++ ([%d] ++ (%s ++ item T 132)))) := by
  simp only [rebuiltA, scA0, scA2, lkA, secondInA, secondOutA, h140, h182, encode_zero, castToBool_nil,
    castToBool_encode_one, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append,
    encode_two, encode_three, encode_four']
"""%(desc,x,y,h140,h182,cin,ins,cout,outs))
t=open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'rebuilt_tmpl.lean')).read()
t=t.replace('LAYOUTS','\n'.join(lay))
t=t.replace('XBYTES',X).replace('SC0BYTES',SC).replace('SC2BYTES',SC2)
t=t.replace('PARAMS',P).replace('ARGS',A)
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Rebuilt.lean','w').write(t)
print(len(t))
