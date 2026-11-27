import collections,json,re,sys
from pathlib import Path
d=json.load(open('context.json'))
p=Path(d['input']['directory'])
planned={i['id']:i for i in d['plan']['items']}
def reads(files):
 results={}
 for f in files:
  for l in f.open():
   data=l.rstrip('\n').split('\t')
   if data[0]=='start':
    _,id,mod,a=data
    results[id]=result={'axioms':a,'c':{},'locals':collections.defaultdict(set),'unknown':set(),'all_roots':set()}
   elif data[0]=='ref' and len(data)==7:
    _,kind,root,sect,mod,c,line=data
    result['all_roots'].add(root)
    if mod=='Proofs.'+id or root!=id and mod=='':
     if c!=id:
      result['locals'][c].add('statement' if sect=='type' and root==id else 'proof')
     continue
    if not line.isdigit():continue
    key=(mod,c,int(line))
    entry=result['c'].setdefault(key,set())
    if root==id and sect=='type':entry.add('statement')
    elif root==id:entry.add('body')
    elif sect=='type': entry.add('helper type')
    else:entry.add('helper body')
   elif data[0]=='novalue':
    result['unknown'].add(data[1])
 return results

if __name__=='__main__':
 results=reads(sorted(Path().glob('Inspect[0-3].out')))
 print('seen',len(results))
 for id,v in results.items():
  deps={c:locs for (mod,c,line),locs in v['c'].items() if c in planned and mod=='Proofs.'+c}
  extra=set(deps)-set(planned[id]['deps'])
  if extra:print('EXTRA',id, {k:deps[k] for k in extra})
  if id in v['unknown']: print('OPAQUE',id)
  if __import__('os').environ.get('DETAIL'):
   print(id,'INTERNAL', {k:sorted(list(l)) for k,l in deps.items()}, 'DROPPED',sorted(set(planned[id]['deps'])-set(deps)), 'LOCALS', list(v['locals'])[:14])
