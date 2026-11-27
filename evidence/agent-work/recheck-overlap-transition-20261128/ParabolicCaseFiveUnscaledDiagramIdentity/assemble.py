s=open('Support.lean').read()
t=open('endpoint.txt').read()
p=open('Proof.txt').read()
open('Candidate.lean','w').write('import MackeyDiagrams\nimport Proofs.ParabolicCaseFiveCoefficientOneExpansion\n\nset_option maxHeartbeats 2000000\n\n'+s+'\nopen MackeyDiagrams CaseFiveUnscaled\n\ntheorem ParabolicCaseFiveUnscaledDiagramIdentity : (\n'+t+'\n) :=\n'+p+'\n#print axioms ParabolicCaseFiveUnscaledDiagramIdentity\n')
