import json,re,pathlib
s=json.load(open('context.json'))['translation']['type']
d,g=s.split('\neval left = ',1)
p=re.split(r'\n(?=let )',d)
lines=[]
for x in p:
 x='private abbrev '+x[4:]
 x=re.sub(r'\bMackeyDiagrams\.', '', x)
 lines.append(x)
head='import MackeyDiagrams\nimport Proofs.EvaluationWithOneProjection\n\nset_option maxHeartbeats 2000000\n\n'
support='namespace CaseFiveTwoTermsProof\nopen MackeyDiagrams\nnoncomputable section\n\n'+'\n\n'.join(lines)+'\n\n'+pathlib.Path('helpers.lean').read_text()+'\nend\nend CaseFiveTwoTermsProof\n'
pathlib.Path('Support.lean').write_text(support)
pathlib.Path('Check.lean').write_text(head+support+'\n'+pathlib.Path('checktail.lean').read_text())
if pathlib.Path('proof.txt').exists():
 pathlib.Path('Final.lean').write_text(head+support+'\ntheorem CaseFiveRequiresTwoTerms : (\n'+s+'\n) :=\n'+'('+pathlib.Path('proof.txt').read_text().rstrip()+')\n\n#print axioms CaseFiveRequiresTwoTerms\n')
