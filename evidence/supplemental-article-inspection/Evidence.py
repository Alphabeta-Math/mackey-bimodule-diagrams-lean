import collections,hashlib,json,re
from pathlib import Path
d=json.load(open('context.json'))
p=Path(d['input']['directory'])
def hashfile(f):
 return hashlib.sha256(f.read_bytes()).hexdigest()
s=json.loads((p/'state.json').read_text())
prior=json.loads((p/'evidence/supervised-registered-proof-audit.json').read_text())['proofs']
summary=collections.Counter()
for i in d['plan']['items']:
 id=i['id']
 proof=p/f'Proofs/{id}.lean'
 olean=p/f'.lake/build/lib/lean/Proofs/{id}.olean'
 evidence=p/f'evidence/{id}-compile.json'
 audit=p/f'evidence/{id}-axioms.lean'
 r=json.loads(evidence.read_text())
 t=d['translations'][id]
 src=proof.read_text()
 errors=[]
 if not (d['proved'][id]==s['proved'][id]==r['source_sha256']==hashfile(proof)): errors.append('source hash')
 if r.get('olean_sha256') != hashfile(olean): errors.append('olean hash')
 if not(r['ok'] and r['build']['code']==0 and r['axioms']['code']==0): errors.append('exit codes')
 if t['type'].strip() not in src or (i['kind']=='definition' and t['value'].strip() not in src):errors.append('review source')
 out=r['axioms']['output'].strip()
 m=re.fullmatch(fr"'{id}' depends on axioms: \[(.*)\]",out,re.S)
 axioms=[x.strip() for x in m.group(1).split(',')] if m and m.group(1) else []
 if not (m or out==f"'{id}' does not depend on any axioms"): errors.append(f'unknown audit {out}')
 if not set(axioms)<= {'propext','Classical.choice','Quot.sound'}:errors.append('unapproved axioms')
 if 'no choice' in str(i['portal']).lower() and 'Classical.choice' in axioms: print('choice wording',id)
 if set(axioms)!=set(prior[id]['axioms']):errors.append('differences to prior axioms')
 if f'import Proofs.{id}' not in audit.read_text() or f'#print axioms {id}' not in audit.read_text(): errors.append('audit input')
 if errors: print(id,errors)
 summary[tuple(axioms)]+=1
print(summary)
