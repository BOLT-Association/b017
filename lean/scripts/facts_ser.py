import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import sys,re
txt=open(sys.argv[1]).read()
# take the first goal block after the last 'sym_all' info
i=txt.find('he : EnvOK env')
blk=txt[i:]
j=blk.find('⊢')
blk=blk[:j]
lines=blk.split('\n')
items=[];cur=None
for l in lines:
    if re.match(r'^\S',l):
        if cur: items.append(cur)
        cur=l
    else:
        cur+='\n'+l
if cur: items.append(cur)
for it in items:
    if re.match(r'^(hact|hin|w✝|S A|k t|r :|f :|a :|C :|cs :|env|he |hr :|h :)',it): continue
    print(it)
