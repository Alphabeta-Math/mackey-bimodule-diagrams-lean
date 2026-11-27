import json,re,textwrap
s=json.load(open('context.json'))['translation']['type']
names=[
 ('embed','{S T : Subgroup P} (s : P) (h : conjugate s S ≤ T) : MackeyDiagrams.ConjEmbedding S T'),
 ('inverseEmbed','{S T : Subgroup P} (s : P) (h : T ≤ conjugate s S) : MackeyDiagrams.ConjEmbedding T S'),
 ('Span','(K H : Subgroup P) : Type'),
 ('pairWord','{K H L : Subgroup P} (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H) : MackeyDiagrams.Word K H'),
 ('spanBasis','{K H : Subgroup P} (S : Span K H) : MackeyDiagrams.Biset K H'),
]
parts=[]
for name,ty in names:
 st=s.index('let '+name+' :=')
 end=s.index('\nlet ',st)
 val=s[st:end].split('=>\n',1)[1]
 parts.append('private abbrev '+name+' '+ty+' :=\n'+val)
open('Span.tail','w').write('\n\n'.join(parts)+'\n')
