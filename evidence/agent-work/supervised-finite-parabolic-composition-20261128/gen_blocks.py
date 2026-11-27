import json,pathlib,textwrap
c=json.load(open('context.json'))
s=c['translation']['type']
base=s[:s.index('let embed :=')]
defs=[]
for name,typ,body in [
('P','',base.splitlines()[0].split(' := ')[1]),
('Finitary','',base.splitlines()[1].split(' := ')[1]),
('blockSym','(D : Finset Nat) : Subgroup P', 'MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ D))'),
('blockProduct','{m : Nat} (D : Fin m → Finset Nat) : Subgroup P', 'iSup (fun i => blockSym (D i))'),
('Parabolic','(S : Subgroup P) : Prop',base.split('let Parabolic')[1].split('=>\n',1)[1].split('let conjugate')[0].rstrip().strip()),
('conjugate','(s : P) (S : Subgroup P) : Subgroup P','Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s)) S'),
]:
 defs.append(f'private abbrev {name} {typ} :=\n  {body}\n')
for name,typ,start,end in [
 ('Cosets','(H A B : Subgroup P) : Type','let Cosets := fun (H A B : Subgroup P) =>\n','let classOf'),
 ('classOf','(H A B : Subgroup P) (r : H) : Cosets H A B','let classOf := fun (H A B : Subgroup P) (r : H) => ','\nlet OrderedSection'),
 ('OrderedSection','(H A B : Subgroup P) (r : Cosets H A B → H) : Prop','let OrderedSection := fun (H A B : Subgroup P) (r : Cosets H A B → H) =>\n','\nlet sumBasis'),
]:
 if name=='Cosets': defs.append('private abbrev inside (H A : Subgroup P) := Subgroup.comap (Subgroup.subtype H) A\n')
 defs.append(f'private abbrev {name} {typ} :=\n'+textwrap.indent(textwrap.dedent(s.split(start)[1].split(end)[0]),'  ')+'\n')
p=pathlib.Path(c['input']['directory'])
join=(p/'Proofs/FiniteParabolicJoinOfFamily.lean').read_text()
parts=join[join.index('  have ofFamily'):join.index('  -- Proposition 7.1 uses swaps')]
parts=textwrap.dedent(parts).replace('have ofFamily','private theorem ofFamily',1).replace('have singletonSym','private theorem singletonSym',1).replace('have pad {','private theorem pad {',1)
parts=parts.replace('  let _ : Fintype κ :=','  classical\n  let _ : Fintype κ :=').replace('  obtain ⟨n, B, hne, hd, hc, rfl⟩ := hH','  classical\n  obtain ⟨n, B, hne, hd, hc, rfl⟩ := hH')
defs.append('private abbrev parabolicOn (X : Finset Nat) (H : Subgroup P) : Prop :=\n'+textwrap.indent(textwrap.dedent(join.split('fun X H =>\n')[1].split('let parabolic')[0]),'  ')+'\n')
pathlib.Path('Blocks.lean').write_text('import MackeyDiagrams\nimport Proofs.MackeyDecompositionWithParabolicRepresentatives\nimport Proofs.ModuleTensorUniversalProperty\n\nset_option maxHeartbeats 2000000\n\nnamespace FiniteParabolicCompositionSupport\n\n'+'\n'.join(defs)+'\n'+parts)
