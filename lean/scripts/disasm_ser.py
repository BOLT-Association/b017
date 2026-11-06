import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re,sys
src=open(LEAN + '/BoltProof/Bridge/Generated/Chunks.lean').read()
ns=sys.argv[1]
blk=src[src.index('namespace BoltProof.Bridge.Generated.'+ns+'\n'):src.index('end BoltProof.Bridge.Generated.'+ns+'\n')]
defs=re.findall(r'^def (c\d+\w*) : List Nat := \[([^\]]*)\]', blk, re.M)
OP={0:'0',0x4c:'PUSHDATA1',0x4d:'PUSHDATA2',0x4e:'PUSHDATA4',0x4f:'1NEGATE',0x63:'IF',0x64:'NOTIF',0x67:'ELSE',0x68:'ENDIF',0x69:'VERIFY',0x6a:'RETURN',0x6b:'TOALT',0x6c:'FROMALT',0x6d:'2DROP',0x6e:'2DUP',0x6f:'3DUP',0x70:'2OVER',0x71:'2ROT',0x72:'2SWAP',0x73:'IFDUP',0x74:'DEPTH',0x75:'DROP',0x76:'DUP',0x77:'NIP',0x78:'OVER',0x79:'PICK',0x7a:'ROLL',0x7b:'ROT',0x7c:'SWAP',0x7d:'TUCK',0x7e:'CAT',0x7f:'SPLIT',0x80:'NUM2BIN',0x81:'BIN2NUM',0x82:'SIZE',0x87:'EQUAL',0x88:'EQUALVERIFY',0x8b:'1ADD',0x8c:'1SUB',0x91:'NOT',0x92:'0NOTEQUAL',0x93:'ADD',0x94:'SUB',0x95:'MUL',0x96:'DIV',0x97:'MOD',0x9a:'BOOLAND',0x9b:'BOOLOR',0x9c:'NUMEQUAL',0x9d:'NUMEQUALVERIFY',0x9e:'NUMNOTEQUAL',0x9f:'LESSTHAN',0xa0:'GREATERTHAN',0xa1:'LTE',0xa2:'GTE',0xa3:'MIN',0xa4:'MAX',0xa5:'WITHIN',0xa8:'SHA256',0xa9:'HASH160',0xaa:'HASH256',0xab:'CODESEP',0xac:'CHECKSIG',0xad:'CHECKSIGVERIFY'}
def dis(bs):
    out=[];i=0
    while i<len(bs):
        b=bs[i]
        if 1<=b<=75:
            d=bs[i+1:i+1+b]; out.append('<'+(''.join('%02x'%x for x in d) if len(d)<=8 else '%dB'%len(d))+'>'); i+=1+b
        elif b==0x4c:
            n=bs[i+1]; out.append('<PD1 %dB>'%n); i+=2+n
        elif b==0x4d:
            n=bs[i+1]+256*bs[i+2]; out.append('<PD2 %dB>'%n); i+=3+n
        elif 0x51<=b<=0x60: out.append(str(b-0x50)); i+=1
        else: out.append(OP.get(b,'?%02x'%b)); i+=1
    return ' '.join(out)
a,b=int(sys.argv[2]),int(sys.argv[3])
for n,body in defs:
    s=int(re.match(r'c(\d+)',n).group(1))
    if a<=s<b:
        bs=[int(x,0) for x in body.split(',') if x.strip()]
        print(n, ':', dis(bs) if len(bs)<400 else '(%d bytes)'%len(bs))
