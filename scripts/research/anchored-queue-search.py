"""Bounded independent audit of AnchoredQueue's compact ordinary merge.

Seeds: 31, 173, 20261007, 601; 10,000 histories per seed; at most nine
fresh events and fourteen transitions. This is search evidence, not a proof.
The live-record representation and three-way survival predicates mirror
eUpdate/eMerge; enqueue values equal their fresh birth identities so the
query distinguishes every surviving order. Unary coordinates are compared
using their equivalent ancestor-first, larger-delta-first birth-chain order.

Only ordinary merges with one greatest common ancestor are executed.
Multiple-base attempts are counted and skipped; recursive virtual merging
is outside this harness. Each allocated snapshot is checked by exhaustive
FIFO scheduling, retaining causal enqueue/enqueue, dequeue/dequeue and
own-birth/dequeue edges. The specification never reads coordinates.
Two deliberately corrupted projections must be rejected before searching.
Run with Python 3; stdout is the reproducible JSON result.
"""

import random,functools,json

def pathkey(p):return tuple(-d for d in p)+(-10**12,)
def sort(s):return tuple(sorted(s,key=lambda x:pathkey(x[1])))
def merge(l,a,b):
 li={x[0] for x in l};ai={x[0] for x in a};bi={x[0] for x in b}
 return sort([x for x in a if x[0] in bi or x[0] not in li]+[x for x in b if x[0] not in li and x[0] not in ai])
def accepts(E,events,vis,target):
 deps={b:frozenset(a for a,c in vis if c==b and (events[a][0]==events[b][0] or events[a][0]=='e' and events[b]==('d',a))) for b in E}
 @functools.lru_cache(None)
 def go(done,q):
  if len(done)==len(E):return q==target
  for e in E-done:
   if not deps[e]<=done:continue
   typ,arg=events[e]
   if typ=='e':nq=q+(e,)
   elif arg not in q:nq=q
   elif q and q[0]==arg:nq=q[1:]
   else:continue
   if go(done|{e},nq):return True
  return False
 return go(frozenset(),())
# Negative controls: corrupted projection forgets a fresh enqueue; reversing causal enqueues.
assert not accepts({1},{1:('e',(1,))},set(),())
assert not accepts({1,2},{1:('e',(1,)),2:('e',(1,1))},{(1,2)},(2,1))
# Deleted common-ancestor node must not resurrect; concurrent child must survive deleted anchor.
a=(1,(1,));c=(3,(1,2))
assert merge((a,),(),(a,))==()
assert merge((a,),(),(a,c))==(c,)
assert merge((),(),(a,))==(a,)
counts={'trials':0,'snapshots':0,'ordinary_merges':0,'multi_base_skips':0,'dequeues':0,'enqueues':0,'noninitial_gca_merges':0,'continued_updates_after_merge':0}
for seed in [31,173,20261007,601]:
 rng=random.Random(seed)
 for trial in range(10000):
  versions=[((),frozenset(),frozenset({0}))];heads=[0,0,0];events={};vis=set();mint=0;mergedheads=set();trace=[]
  for tick in range(14):
   r=rng.randrange(3)
   if rng.random()<.4:
    v=heads[r];w=heads[rng.randrange(3)]
    if v==w:continue
    common=versions[v][2]&versions[w][2]
    maximal=[x for x in common if not any(x!=y and x in versions[y][2] for y in common)]
    if len(maximal)!=1:counts['multi_base_skips']+=1;continue
    g=maximal[0];s=merge(versions[g][0],versions[v][0],versions[w][0]);E=versions[v][1]|versions[w][1]
    new=len(versions);anc=versions[v][2]|versions[w][2]|{new};versions.append((s,E,frozenset(anc)));heads[r]=new;mergedheads.add(new)
    counts['ordinary_merges']+=1;counts['noninitial_gca_merges']+=g!=0;trace.append(('merge',r,v,w,g,new))
   else:
    if mint>=9:continue
    mint+=1;v=heads[r];s,E,anc=versions[v]
    if s and rng.random()<.5:
     op=('d',s[0][0]);ns=tuple(x for x in s if x[0]!=op[1]);counts['dequeues']+=1
    else:
     tail=s[-1] if s else (0,());p=tail[1]+(mint-tail[0],);op=('e',p);ns=sort(s+((mint,p),));counts['enqueues']+=1
    events[mint]=op;vis|={(a,mint) for a in E};nE=E|{mint};new=len(versions);versions.append((ns,frozenset(nE),anc|{new}));heads[r]=new
    counts['continued_updates_after_merge']+=v in mergedheads;trace.append(('apply',r,mint,op,v,new))
   counts['snapshots']+=1
   S,EE,_=versions[heads[r]];target=tuple(x[0] for x in S)
   if not accepts(EE,events,vis,target):
    print(json.dumps({'counter':True,'seed':seed,'trial':trial,'trace':trace,'events':events,'vis':list(vis),'target':target,'counts':counts}));raise SystemExit
  counts['trials']+=1
print(json.dumps({'counter':False,'seeds':[31,173,20261007,601],'max_events':9,'ticks_per_trial':14,'negative_controls':2,'merge_controls':3,'counts':counts}))
