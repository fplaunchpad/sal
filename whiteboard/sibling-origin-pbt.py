"""
Sibling-linked tombstone-free RGA — immutable between-origins WITH CARRIED PATHS
(ghost state), the faithful extension of RGA_Tombstone_Free.

Each node carries, immutably:  L, R  (left/right origin ids)  and
  pathL = [L, L.L, L.L.L, ... , 0]      (left-origin spine, nearest first)
  pathR = [R, R.R, ... , END]           (right-origin spine)
On read/merge with live set V:
  effL(u) = first id of pathL(u) that is in V  (else START)     -- climb dead
  effR(u) = first id of pathR(u) that is in V  (else END)
Order = deterministic topo sort of { effL(u) -> u -> effR(u) }, newest-first;
emit live.  The paths make the state SELF-CONTAINED: a dead origin is resolved
by climbing its carried spine — exactly RGA's path, on both sides.
"""
from itertools import permutations
from collections import defaultdict
import random
START, END = 0, -1

def naive_fold(ops):
    doc=[]
    for op in ops:
        if op[0]=='ins':
            _,x,a=op; doc.insert(0 if (a==START or a not in doc) else doc.index(a)+1, x)
        else:
            _,d=op
            if d in doc: doc.remove(d)
    return doc

# ---- state: id -> (L, R, pathL, pathR) ; live = keys ----
# pathL = [u.L, u.L.L, ...]  (left spine, nearest first, implicit ...->START)
# pathR = [u.R, u.R.R, ...]  (right spine, implicit ...->END)
def integrate(state):
    """EXPAND each survivor's carried paths into ghost nodes with their origins;
    keep ghosts as positioned intermediates; topo-sort; caller emits live."""
    succ=defaultdict(set); nodes={START,END}
    def add(a,b): succ[a].add(b); nodes.add(a); nodes.add(b)
    for u,(L,R,pL,pR) in state.items():
        nodes.add(u)
        # left spine: (pL ends in START=0) ... -> pL[1] -> pL[0] -> u
        prev=u
        for g in pL:
            add(g,prev); prev=g
        # right spine: u -> pR[0] -> pR[1] -> ... (pR ends in END=-1)
        prev=u
        for h in pR:
            add(prev,h); prev=h
    indeg={n:0 for n in nodes}
    for a in succ:
        for b in succ[a]:
            if b in indeg: indeg[b]+=1
    order=[]; ready=[n for n in nodes if indeg[n]==0]; seen=set()
    while ready:
        if START in ready:
            n=START; ready.remove(START)
        else:
            ready.sort(key=lambda n:(n==END, -(n)))   # newest-id first, END last
            n=ready.pop(0)
        if n in seen: continue
        seen.add(n); order.append(n)
        for v in succ[n]:
            if v in indeg:
                indeg[v]-=1
                if indeg[v]==0: ready.append(v)
    return order

def st_read(state):
    live=set(state)
    return [u for u in integrate(state) if u in live]

def st_insert(state,x,a,read_now):
    if a==START or a not in read_now:
        L,pos=START,0
    else:
        L,pos=a,read_now.index(a)+1
    R=read_now[pos] if pos<len(read_now) else END
    pL=[L]+ (state[L][2] if L in state else [])
    pR=[R]+ (state[R][3] if R in state else [])
    state[x]=(L,R,pL,pR)

def st_delete(state,d): state.pop(d,None)

def run(ops,base=None):
    st=dict(base) if base else {}
    for op in ops:
        rd=st_read(st)
        if op[0]=='ins': st_insert(st,op[1],op[2],rd)
        else: st_delete(st,op[1])
    return st

def merge_state(Lst,Ast,Bst):
    idsL,idsA,idsB=set(Lst),set(Ast),set(Bst)
    surv=(idsL&idsA&idsB)|(idsA-idsL)|(idsB-idsL)
    origins={}
    for s in (Lst,Ast,Bst):
        for k,v in s.items(): origins.setdefault(k,v)
    return {u:origins[u] for u in surv}         # carried paths make it self-contained

def merge_read(Lst,Ast,Bst): return st_read(merge_state(Lst,Ast,Bst))

# ---- loOn ----
def commute(o1,o2):
    if o1[0]=='del' and o2[0]=='del': return True
    if o1[0]=='ins' and o2[0]=='del':
        _,x,a=o1;_,d=o2; return a!=d and x!=d
    if o1[0]=='del' and o2[0]=='ins': return commute(o2,o1)
    _,x,a=o1;_,y,b=o2; return a!=b and a!=y and b!=x

def is_ra(all_ops,causal,target):
    before={(i,j) for (i,j) in causal if not commute(all_ops[i],all_ops[j])}
    for perm in permutations(range(len(all_ops))):
        pos={op:k for k,op in enumerate(perm)}
        if all(pos[i]<pos[j] for (i,j) in before) and \
           naive_fold([all_ops[k] for k in perm])==target: return True
    return False

def gen(rng,live0,nid,nops):
    ops,live=[],list(live0)
    for _ in range(nops):
        if live and rng.random()<0.35:
            d=rng.choice(live); ops.append(('del',d)); live.remove(d)
        else:
            a=rng.choice([0]+live) if live else 0
            x=nid[0]; nid[0]+=1; ops.append(('ins',x,a)); live.append(x)
    return ops,live

def within(gs):
    b=set()
    for seq in gs:
        for i in range(len(seq)):
            for j in range(i+1,len(seq)): b.add((seq[i],seq[j]))
    return b

def sweep_single(trials,seed):
    rng=random.Random(seed); nf=drop=nc=n=0
    for _ in range(trials):
        nid=[1]; s0,l0=gen(rng,[],nid,rng.randint(1,3))
        a,_=gen(rng,l0,nid,rng.randint(1,3)); b,_=gen(rng,l0,nid,rng.randint(1,3))
        if len(s0)+len(a)+len(b)>8: continue
        n+=1; Ls=run(s0); As=run(a,Ls); Bs=run(b,Ls)
        m=merge_read(Ls,As,Bs)
        if m!=merge_read(Ls,Bs,As): nc+=1; continue
        if set(m)!=set(merge_state(Ls,As,Bs)): drop+=1
        allops=s0+a+b; nL,nA=len(s0),len(a)
        gL=list(range(nL));gA=list(range(nL,nL+nA));gB=list(range(nL+nA,len(allops)))
        before=within([gL,gA,gB])|{(i,j) for i in gL for j in gA+gB}
        if not is_ra(allops,before,m): nf+=1
    print(f"[single path] seed {seed}: {n} merges | noncomm={nc} dropped={drop} NOT-A-FOLD={nf}")

def sweep_multi(trials,seed):
    rng=random.Random(seed); nf=div=n=0
    for _ in range(trials):
        nid=[1]; s0,l0=gen(rng,[],nid,rng.randint(1,2)); Ls=run(s0)
        a,_=gen(rng,l0,nid,rng.randint(1,2)); b,_=gen(rng,l0,nid,rng.randint(1,2))
        As=run(a,Ls); Bs=run(b,Ls); M1=merge_state(Ls,As,Bs)
        if st_read(M1)!=st_read(merge_state(Ls,Bs,As)): div+=1; continue
        l1=st_read(M1)
        c,_=gen(rng,l1,nid,rng.randint(1,2)); d,_=gen(rng,l1,nid,rng.randint(1,2))
        Cs=run(c,M1); Ds=run(d,M1); M2=merge_state(M1,Cs,Ds)
        if st_read(M2)!=st_read(merge_state(M1,Ds,Cs)): div+=1; continue
        allops=s0+a+b+c+d
        if len(allops)>8: continue
        n+=1; base=0; g=[]
        for grp in (s0,a,b,c,d): g.append(list(range(base,base+len(grp)))); base+=len(grp)
        gs,ga,gb,gc,gd=g
        before=within(g)|{(i,j) for i in gs for j in ga+gb+gc+gd}|{(i,j) for i in ga+gb for j in gc+gd}
        if not is_ra(allops,before,st_read(M2)): nf+=1
    print(f"[multi  path] seed {seed}: {n} merges | divergences={div} NOT-A-FOLD={nf}")

if __name__=='__main__':
    Ls=run([('ins',1,0)]); As=run([('ins',2,1),('ins',4,0),('del',1)],Ls); Bs=run([('ins',3,1)],Ls)
    print("countermodel merge:",merge_read(Ls,As,Bs)," (want [4,3,2])")
    print("delete-order [b a c] del a:",st_read(run([('ins',1,0),('ins',2,0),('ins',3,1),('del',1)]))," (want [2,3])")
    print("interior del  1 2 3 ; del 2:",st_read(run([('ins',1,0),('ins',2,1),('ins',3,2),('del',2)]))," (want [1,3])")
    L2=run([('ins',1,0)]);A2=run([('ins',10,1),('ins',11,10)],L2);B2=run([('ins',20,1),('ins',21,20)],L2)
    print("concurrent runs   :",merge_read(L2,A2,B2))
    print("-"*60)
    for sd in (1,2,3): sweep_single(6000,sd)
    for sd in (7,8,9): sweep_multi(8000,sd)
