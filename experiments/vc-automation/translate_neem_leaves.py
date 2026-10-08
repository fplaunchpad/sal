import re
p='experiments/vc-automation/InductiveLeaves.lean';s=open(p).read();src=open('_references/neem_fstar_repo/code/interface/App_mrdt.fsti').read();src=re.sub(r'//[^\n]*','',src)
arity={'eq':2,'merge':3,'do':2}
def term(t,i):
 if t[i]=='(':
  a,j=term(t,i+1);assert t[j]==')',(t[j:],a);return '('+a+')',j+1
 x=t[i];i+=1
 if x in arity:
  args=[]
  for _ in range(arity[x]):
   a,i=term(t,i);args.append(a)
  if x=='eq':return '('+args[0]+' = '+args[1]+')',i
  return '('+{'merge':'D.merge','do':'D.step'}[x]+' '+' '.join(args)+')',i
 return x,i

def trans(e):
 e=re.sub(r'\beq\b', 'eq',e)
 t=re.findall(r"\w+'?\??|\S",e);out=[];i=0
 while i<len(t):
  if t[i]=='eq':
   a,i=term(t,i);out.append(a)
  else:out.append(t[i]);i+=1
 e=' '.join(out)
 e=re.sub(r"distinct_ops (\w+'?) (\w+'?)",r'D.distinct \1 \2',e)
 e=re.sub(r'get_rid (\w+)',r'\1.2.1',e);e=re.sub(r'fst (\w+)',r'\1.1',e)
 e=re.sub(r'(Fst_then_snd|Either)\? \( rc (\w+) (\w+) \)',r'(D.order \2 \3 = .\1)',e)
 e=e.replace('/ \\', '∧').replace('\\ /','∨').replace('< >','≠').replace('= ! =','≠').replace('~','¬').replace('= = >','→')
 e=re.sub(r'exists (\w+) \.',r'∃ \1,',e)
 return e
names=['inter_right_base_2op','inter_left_base_2op','inter_right_2op','inter_left_2op','inter_lca_2op','ind_right_2op','ind_left_2op','inter_right_base_1op','inter_left_base_1op','inter_right_1op','inter_left_1op','inter_lca_1op','ind_left_1op','ind_right_1op']
new='\n-- Remaining frozen-event schemata: exact F* requires/ensures, no strengthening.\n'
for n in names:
 m=re.search(r'val '+n+r' (.*?)\n\s*: Lemma \(requires (.*?)\)\s*\(ensures (.*?)\)\s*(?=val|\(\*|$)',src,re.S)
 if not m:raise Exception(n)
 hdr,req,ens=m.groups();bind=[]
 for vs,ty in re.findall(r'\(([^:]+):([^)]*)\)',hdr):bind.append('('+vs.strip()+' : '+('D.State' if ty.strip()=='concrete_st' else 'Op D.AppOp')+')')
 new+='def '+n+' : Prop := ∀ '+' '.join(bind)+',\n  '+trans(req)+' →\n  '+trans(ens)+'\n\n'
# Print only derived schemata; compare against InductiveLeaves.lean.
print(new)
