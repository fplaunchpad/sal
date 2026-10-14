import json
from pathlib import Path
import argparse
p=argparse.ArgumentParser(description='Render checked current measurements for the manuscript')
p.add_argument('measurement',type=Path)
p.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
a=p.parse_args(); root=a.out; root.mkdir(parents=True,exist_ok=True)
full=json.loads(a.measurement.read_text()); data=full.get('paper_rows',full.get('paper_rows_21'))
names={
'grow-only-set-three-carriers':r'Grow-only set\cite{shapiro2011comprehensive}',
'counter':r'Counter\cite{neem}',
'flat-grow-only-map':r'Grow-only map\cite{shapiro2011comprehensive}',
'lww-register':r'LWW register\cite{shapiro2011comprehensive}',
'rga':r'RGA\cite{Roh}',
'ordinary-or-set-paper-example':r'OR-set\cite{neem}',
'efficient-or-set':r'Efficient OR-set\cite{neem}',
'mvr':r'Multivalue register\cite{shapiro2011comprehensive}',
'embed-rga':r'Embedded RGA\cite{Roh}',
'sided-embed-rga':r'Sided RGA\cite{Roh,FugueMax}',
'peritext-embed-rga':r'Peritext (boundaries)\cite{Peritext}',
'sided-peritext-core':r'Sided Peritext (core)\cite{Peritext}',
'sided-peritext-rich-core':r'Sided Peritext\cite{Peritext}',
'anchored-queue-paper-variant':r'Anchored queue\cite{Roh,Peepul}',
'fugue-max':r'FugueMax\cite{FugueMax}',
'balegas-bounded-counter':r'Bounded counter\cite{BalegasBoundedCounter}',
'enable-wins-flag':r'Enable-wins flag\cite{neem}',
'disable-wins-flag':r'Disable-wins flag\cite{neem}',
'tree-move':r'Tree move (replay)\cite{TreeMove}',
'aegis-sheet':r'AegisSheet (intent model)\cite{AegisSheet}',
'notion-core':r'Notion core\cite{NotionCRDTBlog}',
'remove-wins-set':r'Remove-wins set\cite{neem}',
'set-wins-map':r'Set-wins multimap\cite{neem}',
'optional-register':r'Optional register\cite{neem}',
'add-wins-priority-queue':r'Priority queue (Sal variant)\cite{PriorityQueue2023}'
}
# Conceptual progression: scalar/collection operations, policies and rights,
# identified sequences, then composed structured documents. Keep variants adjacent.
order = [
 'counter', 'grow-only-set-three-carriers', 'flat-grow-only-map',
 'lww-register', 'mvr', 'optional-register',
 'enable-wins-flag', 'disable-wins-flag',
 'ordinary-or-set-paper-example', 'efficient-or-set', 'remove-wins-set',
 'set-wins-map', 'add-wins-priority-queue', 'balegas-bounded-counter',
 'anchored-queue-paper-variant', 'rga', 'embed-rga', 'sided-embed-rga',
 'fugue-max', 'tree-move', 'peritext-embed-rga', 'sided-peritext-rich-core',
 'aegis-sheet', 'notion-core',
]
assert set(data) <= set(order), 'Missing complexity order for a measured row'
names = {k: names[k] for k in order}
no_i={'grow-only-set-three-carriers','counter','flat-grow-only-map','lww-register','ordinary-or-set-paper-example','efficient-or-set','enable-wins-flag','disable-wins-flag'}
no_i.update({'set-wins-map','add-wins-priority-queue'})
no_e=(no_i-{'lww-register'})|{'remove-wins-set'}
rc={'ordinary-or-set-paper-example','efficient-or-set','enable-wins-flag','disable-wins-flag'}
lines=[r'\begin{table}[t]',r'\caption{Verified configurations, ordered by conceptual complexity, and current Lean source footprint. MRDT and Spec count definition dependencies; VCs and Bridge count proof-support dependencies, including theorem statements, helper definitions, and certificate wiring. Shared framework libraries are excluded.}',r'\label{tab:implementation}',r'\centering',r'\small',r'\setlength{\tabcolsep}{3pt}',r'\begin{tabular}{@{}>{\raggedright\arraybackslash}p{0.48\linewidth}rrrrccc@{}}',r'\toprule',r'Configuration & MRDT & Spec & VCs & Bridge & I & E & $\rcrel\ne\varnothing$ \\',r'\midrule']
assert set(data)<=set(names), 'Missing display metadata for a measured row'
rc.update({'remove-wins-set','set-wins-map','optional-register','add-wins-priority-queue'})
for k in names:
 if k not in data: continue
 row=data[k]['loc']; nums=[f'{row[x]:,}' for x in ['implementation','specification','vc','bridge']]
 lines.append(names[k].replace(r'\cite',r'~\cite')+' & '+' & '.join(nums)+f" & {'--' if k in no_i else 'Y'} & {'--' if k in no_e else 'Y'} & {'Y' if k in rc else '--'} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\par\smallskip',r'\begin{minipage}{\linewidth}',r'\footnotesize',r'I: a nontrivial datatype-specific issuance guard. E: an execution-scoped history bridge, rather than conformance of every implementation fold. These execution facts are proved from reachability, not supplied as unproved invariants. The final column concerns the application-operation policy; an empty policy does not remove origin, visibility, or invariant-scoped ordering constraints. All rows have ordinary and recursive-base results.',r'\par\smallskip',r'Sided RGA adapts the two-sided tree of Fugue with an RGA-derived sibling order; it is distinct from FugueMax. The priority queue uses the Sal retained-increment variant, with empty, membership, priority and maximum queries plus derived local maximum removal; it makes no atomic global-extraction claim.',r'\par\smallskip',r'Counts exclude blank lines, comments, tests, and shared framework code. Each row assigns source lines once, in column order; Bridge includes the remaining execution and issuance proof support. Dependencies reused across rows are counted in each row, so column sums are not project totals. The artifact supplies the source roots, hashes, and counting script.',r'\end{minipage}',r'\end{table}']
(root/'implementation_table.tex').write_text('\n'.join(lines)+'\n')

md=['| Configuration | Def. | Spec | VC support | Bridge/execution support | I | E | Nontrivial rc |','|---|---:|---:|---:|---:|:---:|:---:|:---:|']
for k in names:
 if k not in data: continue
 row=data[k]['loc']; md.append('| '+k+' | '+' | '.join(str(row[x]) for x in ['implementation','specification','vc','bridge'])+' | '+' | '.join(['–' if k in no_i else '✓','–' if k in no_e else '✓','✓' if k in rc else '–'])+' |')
(root/'table.md').write_text('\n'.join(md)+'\n')
def compress(points):
 byfile={}
 for f,n in points: byfile.setdefault(f,[]).append(n)
 out={}
 for f,ns in sorted(byfile.items()):
  ranges=[]
  for n in sorted(set(ns)):
   if ranges and n==ranges[-1][1]+1: ranges[-1][1]=n
   else: ranges.append([n,n])
  out[f]=ranges
 return out
compact={k:full[k] for k in ['method','git_head','deduplicated_concrete_total','deduplicated_shared_dependency_total','source_sha256']}
compact['direct_vc_dependency_roots']=full.get('direct_vc_dependency_roots',[])
compact['configuration_count']=len(full.get('configuration_rows',full.get('rows_23',{})))
compact['paper_row_count']=len(data)
compact['paper_rows']={k:{'roots':v['roots'],'loc':v['loc'],'source_ranges':{role:compress(points) for role,points in v['exclusive_code_lines'].items()}} for k,v in data.items()}
compact['shared_source_ranges']=compress(full['shared_code_lines'])
(root/'current-counts.json').write_text(json.dumps(compact,indent=2)+'\n')
print(f"Rendered {len(data)} paper rows from {compact['configuration_count']} checked configurations.")
