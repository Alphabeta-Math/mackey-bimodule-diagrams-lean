import functools
import hashlib
from urllib.parse import quote
from ParseInspection import *

rev=d['input']['mathlib']
leanrev=__import__('os').environ['LEAN_GITHASH']
lib=p/'.lake/packages/mathlib'
lean=Path(__import__('os').environ['LEAN_SYSROOT'])/'src/lean'
previous={r['id']:r for r in json.load(open(p/'proof-graph.json'))['graph']['routes']}
approaches=dict(x.split('\t',1) for x in Path('Approaches.tsv').read_text().splitlines())
results=reads(sorted(Path().glob('Inspect[0-3].out')))
results.update(reads(sorted(Path().glob('Isolated*.out'))))
connection_refs=reads([Path('Connections.out')])
assert set(results)==set(planned)==set(approaches)==set(d['proved'])

hashfile=functools.cache(lambda f:hashlib.sha256(f.read_bytes()).hexdigest())
def modpath(mod):
 return Path(*mod.split('.')).with_suffix('.lean')

@functools.cache
def modulefile(mod):
 roots=[p,lib,lean]
 prefix=mod.split('.')[0].lower()
 roots.extend(sorted((p/'.lake/packages').glob('*')) if prefix in {'batteries','qq','aesop','importgraph','plausible'} else [])
 for root in roots:
  path=root/modpath(mod)
  if path.is_file():
   return path

@functools.cache
def schedule_sources(id):
 return {a for b in planned[id]['deps'] for a in {b}|schedule_sources(b)}

def desc_roles(roles):
 if 'statement' in roles and roles-{'statement'}:
  return 'Endpoint type and proof'
 if roles=={'statement'}:
  return 'Endpoint type'
 if 'body' in roles:
  return 'Proof body'
 if 'helper body' in roles:
  return 'Local proof'
 return 'Type of local proof data'

gen=re.compile(r'(^_private\.|\bmatch_\d|\.match_|\.eq_(?:def|unfold|\d+)(?:\.|$)|\.splitter|\._|\.proof_\d|\.noConfusion|\.recOn|\.casesOn|\.brecOn|\.below|\.injEq|\.sizeOf_spec|(?:^|\.)inst[A-Z])')
generic=re.compile(r'(^|\.)(raw|coe|carrier|val|property|toFun|hom|mk|rec|comp|id|map|map_id|map_comp|app|left|right|symm|trans)$')
mathlib_generic=re.compile(r'^(?:[a-z]+_(?:add|mul|one|zero)|(?:add|mul|one|zero|smul)_[a-z]+|[a-z]+_assoc|[a-z]+_comm)$')
token=re.compile(r'(?:[\w₀-₉]+\.)*[\w₀-₉]+(?:\x27+)?')

def words(line):
 return token.findall(line)

@functools.cache
def sourcelines(f):
 return f.read_text().splitlines()

def role_suffix(c):
 return c.split('.')[-1]

@functools.cache
def declline(f,c,lineno):
 lines=sourcelines(f)
 if 0<lineno<=len(lines):
  return lineno,lines[lineno-1].strip()
 return 0,''

def location(mod,c,line,use):
 f=modulefile(mod)
 assert f, (mod,c)
 sel,_=declline(f,c,line)
 if mod.startswith('Mathlib.'):
  assert f.is_relative_to(lib)
  uri=f'https://github.com/leanprover-community/mathlib4/blob/{rev}/{f.relative_to(lib)}'
  revision=rev
 elif f.is_relative_to(lean):
  uri=f'https://github.com/leanprover/lean4/blob/{leanrev}/src/lean/{f.relative_to(lean)}'
  revision=leanrev
 else:
  uri=f.as_uri()
  revision='working-tree; source-sha256:'+hashfile(f)
 return dict(module=mod,declaration=c,revision=revision,url=uri+(f'#L{sel}' if sel else ''),use=use)

def usage_lines(path, endpoint):
 lines=sourcelines(path)
 if planned[endpoint]['kind']=='definition':
  statement=d['translations'][endpoint]['type'].strip()
  src='\n'.join(lines)
  pos=src.find(statement)
  end=src[:pos+len(statement)].count('\n')+1
  code=lines[end:]
 else:
  statement=d['translations'][endpoint]['type'].strip()
  src='\n'.join(lines)
  pos=src.find(statement)
  begin=src[:pos].count('\n')
  end=src[:pos+len(statement)].count('\n')+1
  code=lines[:max(0,begin-1)]+lines[end:]
 return [s.strip() for s in code if s.strip() and not s.strip().startswith(('--','/-','import ','open ','namespace ','set_option ','section','noncomputable section'))]

def match_index(lines, refs):
 exact=collections.defaultdict(list)
 tail=collections.defaultdict(list)
 for l in lines:
  for tok in set(words(l)):
   exact[tok].append(l)
   tail[tok.rsplit('.',1)[-1]].append(l)
 counts=collections.Counter(role_suffix(c) for _,c,_ in refs)
 for mod,c,no in refs:
  short=role_suffix(c)
  if c in exact:
   yield (mod,c,no), (3,exact[c])
  elif counts[short]==1 and short in tail:
   options=[l for l in tail[short] if any(t==short or c.endswith('.'+t) for t in words(l))]
   if options:
    yield (mod,c,no), (2,options)

def usable(mod,c,line):
 return line and mod.startswith(('MackeyDiagrams.','Mathlib.','WattsFoundation.','Proofs.')) and modulefile(mod) and not gen.search(c)

def action_line(lines):
 lines=[r.split(' -- ',1)[0].strip() for r in lines]
 lines=[s for s in lines if len(s)<183 and not re.search(r'\b(?:exact|apply|rw|refine|simpa|have|let|simp|obtain|change|rcases|rwa)\s*$',s)]
 def rank(l):
  return (
   0 if re.search(r'\b(?:exact|apply|simpa|refine|rw|rwa|simp)\b',l) else 1,
   len(l)
  )
 return min(lines,key=rank,default='').strip()

# Direct suppliers of the endpoint adapters, plus a short trace into the recorded
# supporting results where the proof of the adapter depends on those results.
manual_connections={
 'EilenbergWatts':{
  'ReviewedOriginalWattsConnection':'Direct proof term. Its universally quantified arbitrary-ring type matches the reviewed endpoint after reducing Bimodule at the action type.',
  'WattsFoundation.General.originalWattsWithEvaluation':'The connection uses this equivalence over arbitrary unital R and S with the same lifted module-carrier universe and the reviewed preservation property.',
  'WattsFoundation.General.originalTensorPure_universal':'Supplies uniqueness of the outer-linear extension of each balanced map, at the exact tensor object of the equivalence.',
  'WattsFoundation.General.originalTensorPure_map':'Supplies the formula on pure tensors for each source-module map.',
  'WattsFoundation.General.originalTensorPure_bimoduleMap':'Supplies the pure-tensor component formula on each bimodule morphism.',
  'WattsFoundation.General.originalWatts_inverse_forget':'Identifies the inverse functor after forgetting right actions with evaluation at the lifted regular module.',
  'WattsFoundation.General.originalWatts_inverse_right':'Computes the right action under the strict evaluation equality as the image of the lifted right multiplication.',
  'WattsFoundation.General.originalAssocNatIso_pure':'Computes the natural composition comparison on the two nested pure tensors.',
  'WattsFoundation.General.originalCompositeBimodule_right':'Identifies the right action on a pure element of the composite bimodule.',
  'WattsFoundation.General.originalRegularBimodule_right':'Computes the right action on the lifted regular bimodule by multiplication.',
  'WattsFoundation.General.originalRegularTensorNatIso_pure':'Computes the regular-bimodule tensor identity on pure tensors.'
 },
 'SmallProjectiveGeneratorCorrespondence':{
  'ReviewedSmallGeneratorConnection':'Direct proof term at the exact reviewed Hom universes and both sets of generator hypotheses.',
  'SmallGeneratorBridge.equivalenceOfSmallProjectiveGenerator':'Applied at P and Q with projectivity, separation and preservation of Type v discrete colimits by the corresponding additive Hom functor. Provides IsEquivalence of each module-valued Hom functor.',
  'ReconstructionFromSmallProjectiveGenerator':'Indirect through the generator bridge. Requires bijectivity of the explicit direct-sum comparison on every family. The bridge proves that premise from coproduct preservation and obtains the inverse and both natural isomorphisms.',
  'SmallGeneratorBridge.exactEvaluationEquivalence':'Transports the preserving functors through the generator equivalences and repackages the Watts inverse along the natural comparison at P.',
  'SmallGeneratorBridge.exactEvaluationEquivalence_forget':'Provides the equality of functors after forgetting the right action, including the object casts used in the statement.',
  'SmallGeneratorBridge.exactEvaluation_left_right':'Computes the transported action of the two opposite endomorphism rings at a Hom element.',
  'SmallGeneratorBridge.exactEvaluation_map':'Computes the action on a natural transformation by postcomposition with its component at P.',
  'SmallGeneratorBridge.evaluationTransportIso_natural':'Indirect through abstractEvaluationIso. Identifies the naturality square for the two evaluations with the installed Hom equivalences.',
  'SmallGeneratorBridge.evaluationTransportIso_intertwines':'Indirect through exactEvaluation_right. Identifies the action of a lifted regular right multiplication with postcomposition by the given endomorphism of P under the comparison.',
  'SmallGeneratorBridge.regularToHom_right':'Indirect through the regular comparison underlying evaluation transport. Computes the action of right multiplication on the Hom image of the generator.',
  'WattsFoundation.General.originalWattsWithEvaluation':'Indirect through abstractEquivalence. Its inverse at the two opposite endomorphism rings and universes v and 0 is composed with functor transport.'
 }
}

def add_recorded_connections(id, available):
 conn=manual_connections.get(id)
 if not conn:
  return
 refs={c:(mod,loc) for rs in [results[id],*connection_refs.values()] for (mod,c,loc) in rs['c'] if loc and mod.startswith('WattsFoundation.')}
 # This lemma is reached deeper via GeneratorPreimageAction and was audited separately.
 refs['SmallGeneratorBridge.regularToHom_right']=('WattsFoundation.GeneratorRegularActions',12)
 have={s['declaration'] for s in available}
 for c,use in conn.items():
  if c not in have:
   mod,loc=refs[c]
   available.append(location(mod,c,loc,use))

def joined(names):
 if len(names)<=1:return ''.join(names)
 return ', '.join(names[:-1])+' and '+names[-1]

def referenced_modules(v):
 return {mod[7:] for mod,c,line in v['c'] if mod.startswith('Proofs.') and mod[7:] in planned and usable(mod,c,line)}

all_used={id:referenced_modules(v) for id,v in results.items()}

@functools.cache
def actual_sources(id):
 return {s for dep in all_used[id] for s in {dep}|actual_sources(dep)}

routes={}
for id,item in planned.items():
 v=results[id]
 receipt=json.load(open(p/f'evidence/{id}-compile.json'))
 recorded=receipt['axioms']['output']
 m=re.search(r'depends on axioms: \[([\s\S]*?)\]',recorded)
 expected=[s.strip() for s in m[1].split(',') if s.strip()] if m else []
 actual=[s.strip() for s in v['axioms'][2:-1].split(',') if s.strip()]
 assert set(actual)==set(expected) and not set(actual)-{'propext','Classical.choice','Quot.sound'}, (id,actual,recorded)
 assert id not in v['unknown'], (id,v['unknown'])
 assert receipt['ok'] and receipt['build']['code']==receipt['axioms']['code']==0
 assert receipt['olean_sha256']==hashfile(p/f'.lake/build/lib/lean/Proofs/{id}.olean')
 source=p/f'Proofs/{id}.lean'
 assert d['proved'][id]==receipt['source_sha256']==hashfile(source)
 axsource=p/f'evidence/{id}-axioms.lean'
 assert f'import Proofs.{id}' in axsource.read_text() and f'#print axioms {id}' in axsource.read_text()
 assert d['translations'][id]['type'].strip() in source.read_text()
 if item['kind']=='definition':
  assert d['translations'][id]['value'].strip() in source.read_text()
 refs={k:roles for k,roles in v['c'].items() if usable(*k)}
 previous_by_name={(s['module'],s['declaration']):s for s in previous[id]['available']}
 explicit=dict(match_index(usage_lines(source,id),refs))
 internal=[k for k in refs if k[0].startswith('Proofs.') and k[0][7:] in planned]
 used=all_used[id]
 assert used<=schedule_sources(id),(id,used-schedule_sources(id))
 deps=[dep for dep in item['deps'] if dep in used]

 def score(k):
  mod,c,line=k
  roles=refs[k]
  direct='body' in roles or 'helper body' in roles
  isproject=mod.startswith(('MackeyDiagrams.','WattsFoundation.'))
  prev=(mod,c) in previous_by_name
  level=explicit.get(k,(0,[]))[0]
  f=modulefile(mod)
  _,definition=declline(f,c,line)
  theorem=bool(re.search(r'\b(?:lemma|theorem)\b',definition))
  quoted_term=action_line(explicit.get(k,(0,[]))[1])
  if not direct and not prev and (not isproject or generic.search(c)):
   return 0
  if generic.search(c) and not prev and not theorem:
   return 0
  if mathlib_generic.match(c) and not prev:
   return 0
  if level==0 and not prev:
   return 0
  return (10*int(prev)+5*level+4*int(theorem)+3*int('body' in roles)+2*int(bool(quoted_term))+int('statement' in roles))

 def choose(k):
  mod,c,line=k
  roles=refs[k]
  manual=manual_connections.get(id,{}).get(c)
  if manual:
   return location(mod,c,line,manual)
  used_as=desc_roles(roles)
  localline=action_line(explicit.get(k,(0,[]))[1])
  prev=previous_by_name.get((mod,c))
  suffix=''
  if mod.startswith('Proofs.'):
   sid=mod[7:]
   if sid not in item['deps']:
    parents=[s for s in item['deps'] if sid in schedule_sources(s)]
    suffix=' The scheduled plan already reaches this supplier through '+joined(parents)+'.'
  if localline:
   use=f'{used_as} uses `{localline}`.'+suffix
  elif prev and not mod.startswith('Proofs.'):
   use=used_as+'. '+prev['use']
  elif mod.startswith('Proofs.') and c==mod[7:]:
   label=planned[c]['title'].rstrip('.')
   use=used_as+' uses the registered '+('definition' if planned[c]['kind']=='definition' else 'theorem')+' for '+label[0].lower()+label[1:]+'.'+suffix
  else:
   use=used_as+' calls the checked declaration from '+mod+'.'+suffix
  return location(mod,c,line,use)

 project=[]
 math=[]
 for k in refs:
  if score(k):
   (math if k[0].startswith('Mathlib.') else project).append(k)
 project.sort(key=lambda k:(-score(k),k))
 math.sort(key=lambda k:(-score(k),k))
 core=[k for k in [*project,*math] if (k[0],k[1]) in previous_by_name]
 explicit_relevant=[k for k in project if score(k)>=12][:6]+[k for k in math if score(k)>=14][:5]
 manual_matches={
  'OrdinaryMackeyDecomposition': {'Rep.ofModuleMonoidAlgebra','Rep.toModuleMonoidAlgebra','Rep.indFunctor','Rep.resFunctor','Representation.IndV.mk','DoubleCoset.eq'},
  'LeftUpReidemeisterCurl': {'MackeyDiagrams.Diagram.mergeUp_splitUp','MackeyDiagrams.Diagram.ordinaryCup_traceCap','MackeyDiagrams.Biset.insertLeftUnit_leftUnit'},
  'TransportToMackeyRepresentative': {'DoubleCoset.eq','Subgroup.relIndex_map_map_of_injective'},
 }
 supplementation=[k for k in refs if k[1] in manual_matches.get(id,set())]
 selected=list(dict.fromkeys([*internal,*supplementation,*core,*explicit_relevant]))
 if not selected:
  selected=project[:3]+math[:4]
 available=[choose(k) for k in selected]
 add_recorded_connections(id,available)

 type_only=sorted({k[1] for k in internal if refs[k]=={'statement'}})
 in_type_and_proof=sorted({k[1] for k in internal if 'statement' in refs[k] and refs[k]-{'statement'}})
 notes=[approaches[id]]
 if type_only and id!='EilenbergWatts':
  notes.append('The statement uses '+joined(type_only)+' for its types.')
 if in_type_and_proof:
  notes.append('Both the statement and the proof refer to '+joined(in_type_and_proof)+'.')
 dropped=[dep for dep in item['deps'] if dep not in deps]
 if dropped and id not in {'EilenbergWatts','SmallProjectiveGeneratorCorrespondence','BimoduleTensorBicategoryCoherence','FiniteParabolicBimoduleBicategory'}:
  imports={l.strip().split(' ',1)[1] for l in sourcelines(source) if l.startswith('import ')}
  for x in dropped:
   via=[y for y in routes if y in used and x in actual_sources(y)]
   if not via:
    via=[y for y in planned if y in used and x in actual_sources(y)]
   if via:
    notes.append(x+' enters indirectly through '+joined(via)+'.')
  independent=[x for x in dropped if x not in actual_sources(id)]
  imported=[x for x in independent if 'Proofs.'+x in imports]
  other=[x for x in independent if x not in imported]
  if imported:
   notes.append(joined(imported)+(' remains an import only.' if len(imported)==1 else ' remain imports only.'))
  if other:
   notes.append('The checked construction closes the steps scheduled for '+joined(other)+'.')
 axioms=(', '.join(actual) if actual else 'none')
 notes.append(f'The current source and compiled artifact match the native receipt, and the imported declaration has axioms [{axioms}]. '+(p/f'evidence/{id}-compile.json').as_uri())
 routes[id]=dict(id=id,deps=deps,available=available,approach=' '.join(notes),proofHash=d['proved'][id])

remaining=set(routes)
done=[]
while remaining:
 ready=[id for id in routes if id in remaining and not all_used[id]&remaining]
 assert ready,remaining
 done.extend(ready)
 remaining.difference_update(ready)
graph={'routes':[routes[id] for id in done],'repairs':[]}
Path('proposal.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n')
print(len(done),sum(len(r['available']) for r in routes.values()),sum(len(r['deps']) for r in routes.values()))
print('empty available', [id for id,r in routes.items() if not r['available']])
