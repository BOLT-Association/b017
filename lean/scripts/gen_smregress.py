import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
# gen_smregress.py: appends the refinement-application guards to SimpleMulti/Regress.lean.
P=LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Regress.lean'
s=open(P).read()
marker='/-! ## The refinement applies to the real spends'
if marker in s:
    s=s[:s.index(marker)]+'\nend BoltProof.Bridge.Glue.SimpleMulti\n'
N='by native_decide'
def n(k): return ', '.join([N]*k)
WF='⟨%s⟩'%n(11)
AWF='⟨%s⟩'%n(8)
TXWF='⟨%s⟩'%n(6)
HP='⟨%s⟩'%n(23)
def I(v,i): return '(Vec.inputD %s %d)'%(v,i)
def F(v,i): return '(smFieldsD %s %d)'%(v,i)
def A(v,i): return '(smArgsD %s %d)'%(v,i)
def res(v,i): return 'Residual P %s.tx %d %s.amt %s %s'%(I(v,i),i,I(v,i),F(v,i),A(v,i))
def gpreal(G):
    return ('⟨%s, %s, hnsp, hptxid, of_isTokenAt (%s),\n      fun p hp => of_isProofAt (of_outpointAll (p := fun q => isProofAt (absTx %s).outputs (q.vout + 1)) (%s) p hp),\n      of_balsNonneg (%s)⟩'%(TXWF,N,N,G,N,N))
out='''
/-! ## The refinement applies to the real spends

For each honest spend the theorems cover, every decidable hypothesis of the refinement is checked on the vector's
data, so `Accepts` follows from the residual assumptions alone: `Residual` for each token input, and of the real
grandparents only what no evaluation decides (second-preimage freedom of their serialisation and the primitives'
id). The scope assumptions `HonestPiecesB`, the index arguments and the rest of `GpRealF` and `GpRealB` hold of the
honest lifecycles. -/

def dummyFields : Fields := ⟨[], [], [], [], [], [], [], [], [], [], []⟩
def dummyArgs : Args := ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], piecesOf [], piecesOf []⟩
def smFieldsD (v : Vec) (i : Nat) : Fields := ((smArgs v i).map (·.1)).getD dummyFields
def smArgsD (v : Vec) (i : Nat) : Args := ((smArgs v i).map (·.2.1)).getD dummyArgs
def txD (v : Vec) : Tx := (txOf v).getD ⟨0, [], [], 0⟩

instance (b : Bytes) : Decidable (SmbType b) := by unfold SmbType; exact inferInstance
'''
def basic(name, v, doc, melt=False):
    pre_only = '(fun h => absurd h (%s))'%N
    ha = pre_only if melt else '(fun _ => %s)'%AWF
    hn = pre_only if melt else '(fun _ => %s)'%N
    return '''
/-- %s -/
theorem %s_refines (P : Prims Bytes) (hres : %s) :
    Accepts P .fungible (spendOf %s.tx 0 %s %s none none none) :=
  simpleMulti_refines_basic P _ 0 _ _ _ [] %s.scriptSig %s %s (%s) %s (%s) (%s) (%s) (%s)
    ⟨%s⟩ (%s) (%s) %s (%s) (%s) (%s) hres (%s) (%s)
'''%(doc,name,res(v,0),I(v,0),F(v,0),A(v,0),I(v,0),WF,ha,N,hn,N,N,N,N,n(2),N,N,TXWF,N,N,N,N,N)
out+=basic('a_commit1','smb_honest_a_commit1','The first transfer commit of lifecycle A.')
out+=basic('a_settle1','smb_honest_a_settle1','The first transfer settle of lifecycle A, a token without a grandparent.')
out+=basic('a_splitCommit','smb_honest_a_splitCommit','The split commit of lifecycle A.')
out+=basic('b_melt','smb_honest_b_melt','The melt of lifecycle B.', melt=True)
def settle_gp(name, v, G, doc):
    return '''
/-- %s -/
theorem %s_refines (P : Prims Bytes) (hres : %s)
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx (txD %s)))
    (hptxid : P.txid (absTx (txD %s)) = Sighash.txid (txD %s)) :
    Accepts P .fungible (spendOf %s.tx 0 %s %s none (some (txD %s)) none) :=
  simpleMulti_refines_settle_gp P _ 0 _ _ _ [] %s.scriptSig (txD %s) %s %s (%s) (%s) (%s) (%s) (%s) (%s)
    (%s) (%s) (%s) %s (%s) (%s) (%s) hres
    ⟨%s,
      %s, %s,
      fun p hp => of_decide_eq_true (of_outpointAll (p := fun q => decide (decode %s.i5 = (q.vout : Int) + 1)) (%s) p hp)⟩
    (%s) (%s)
'''%(doc,name,res(v,0),G,G,G,I(v,0),F(v,0),A(v,0),G,I(v,0),G,WF,AWF,N,N,N,N,N,N,N,N,N,TXWF,N,N,N,gpreal('(txD %s)'%G),HP,N,A(v,0),N,N,N)
out+=settle_gp('a_settle2','smb_honest_a_settle2','smb_honest_a_commit1','The second transfer settle of lifecycle A, which rebuilds the first commit.')
out+=settle_gp('a_splitSettle','smb_honest_a_splitSettle','smb_honest_a_commit2','The split settle of lifecycle A, which rebuilds the second commit.')
v='smb_honest_b_mergeCommit'
out+='''
/-- The merge commit of lifecycle B, at its first token input, given the second's run. -/
theorem b_mergeCommit_refines (P : Prims Bytes) (hres : %s) (hres' : %s) :
    Accepts P .fungible (spendOf %s.tx 0 %s %s
      (some (%s, ⟨(inputAt %s.tx 1).prevHash, (inputAt %s.tx 1).prevIndex⟩)) none none) :=
  simpleMulti_refines_merge_commit P _ 0 _ _ _ [] %s.scriptSig 1 _ _ _ [] %s.scriptSig %s %s %s %s
    (%s) (%s) (%s) (%s) (%s) (%s) (%s) (%s) (%s) (%s) %s (%s) (%s) (%s) (%s) (%s) hres hres' (%s) (%s) (%s) (%s)
'''%(res(v,0),res(v,1).replace('Residual P %s.tx 1'%I(v,1),'Residual P %s.tx 1'%I(v,0)),I(v,0),F(v,0),A(v,0),F(v,1),I(v,0),I(v,0),I(v,0),I(v,1),WF,AWF,WF,AWF,N,N,N,N,N,N,N,N,N,N,TXWF,N,N,N,N,N,N,N,N,N)
v='smb_honest_b_mergeSettle'; G='smb_honest_b_commit1'; GB='smb_honest_b_lineageB_commit1'
out+='''
/-- The merge settle of lifecycle B, which rebuilds both lineages' commits. -/
theorem b_mergeSettle_refines (P : Prims Bytes) (hres : %s)
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx (txD %s)))
    (hptxid : P.txid (absTx (txD %s)) = Sighash.txid (txD %s))
    (hptxidB : P.txid (absTx (txD %s)) = Sighash.txid (txD %s)) :
    Accepts P .fungible (spendOf %s.tx 0 %s %s none (some (txD %s)) (some (txD %s))) :=
  simpleMulti_refines_merge_settle P _ 0 _ _ _ [] %s.scriptSig (txD %s) (txD %s) %s %s (%s) (%s) (%s) (%s) (%s)
    (%s) %s (%s) (%s) (%s) hres
    ⟨%s,
      %s, %s,
      fun p hp => of_decide_eq_true (of_outpointAll (p := fun q => decide (decode %s.i5 = (q.vout : Int) + 1)) (%s) p hp)⟩
    ⟨%s, hptxidB, of_isTokenAt (%s), %s, of_isProofAt (%s)⟩ (%s) (%s)
'''%(res(v,0),G,G,G,GB,GB,I(v,0),F(v,0),A(v,0),G,GB,I(v,0),G,GB,WF,AWF,N,N,N,N,N,N,TXWF,N,N,N,gpreal('(txD %s)'%G),HP,N,A(v,0),N,N,N,N,N,N,N)
out+='\nend BoltProof.Bridge.Glue.SimpleMulti\n'
s=s.replace('\nend BoltProof.Bridge.Glue.SimpleMulti\n', out)
open(P,'w').write(s)
print('ok')
