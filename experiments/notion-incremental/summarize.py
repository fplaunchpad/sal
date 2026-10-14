#!/usr/bin/env python3
"""Summarize recorded repeats without mixing setup costs into measurements."""
import collections,json,pathlib,statistics,sys
root=pathlib.Path(__file__).resolve().parent
records=[json.loads(line) for line in (pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else root/'observations.jsonl').read_text().splitlines()]
groups=collections.defaultdict(list)
for r in records:
 if r['kind']=='benchmark':groups[r['mode'],r['size'],r['engine']].append(r)
summary={'correctness':next((r for r in records if r['kind']=='correctness'),None),'measurement':'milliseconds; median of independently recorded repeats; memory is counts/serialized archive proxy, not heap','benchmarks':[]}
for (mode,size,engine),rows in sorted(groups.items()):
 summary['benchmarks'].append({'mode':mode,'size':size,'engine':engine,'repeats':len(rows),**{k:statistics.median(r[k] for r in rows) for k in ['updateMs','queryMs','mergeMs','mergedQueryMs']},'memoryProxy':rows[0]['memory'],'work':rows[0]['work'],'mergeStateWork':rows[0]['mergeStateWork'],'metadata':rows[0]['metadata']})
display_groups=collections.defaultdict(list)
for r in records:
 if r['kind']=='display-benchmark':display_groups[r['mode'],r['size']].append(r)
if display_groups:
 summary['displayBenchmarks']=[{'mode':mode,'size':size,'repeats':len(rows),'createdBlocks':rows[0]['createdBlocks'],'retainedRows':rows[0]['retainedRows'],**{key:statistics.median(row[key] for row in rows) for key in ['treeQueryMs','foldQueryMs']}} for (mode,size),rows in sorted(display_groups.items())]
heap_groups=collections.defaultdict(list)
for r in records:
 if r['kind']=='retained-heap':heap_groups[r['mode'],r['size'],r['engine']].append(r)
if heap_groups:
 summary['measurement']='Retained heapUsed byte deltas after three GC passes; isolated process per engine/repeat; prepared workload retained outside interval; runtime/GC noise remains'
 summary['heapBenchmarks']=[{'mode':mode,'size':size,'engine':engine,'repeats':len(rows),'medianBytes':statistics.median(row['retainedHeapDelta'] for row in rows),'minBytes':min(row['retainedHeapDelta'] for row in rows),'maxBytes':max(row['retainedHeapDelta'] for row in rows),'nodeVersion':rows[0]['nodeVersion'],'platform':rows[0]['platform'],'architecture':rows[0]['architecture'],'transactions':rows[0]['transactions'],'blocks':rows[0]['blocks']} for (mode,size,engine),rows in sorted(heap_groups.items())]
native_groups=collections.defaultdict(list)
for r in records:
 if r['kind']=='native-benchmark':native_groups[r['mode'],r['size']].append(r)
if native_groups:
 summary['measurement']='Native timer nanoseconds converted to milliseconds, reported separately from complete JSON/IPC roundtrip; median of recorded repeats; preparation and wire decode outside core timer'
 summary['nativeCorrectness']=next((r for r in records if r['kind']=='native-correctness'),None)
 summary['nativeMetadataControl']=next((r for r in records if r['kind']=='native-metadata-control'),None)
 summary['nativeBenchmarks']=[{'mode':mode,'size':size,'repeats':len(rows),'updateTransactions':rows[0]['updateTransactions'],'lateArrivals':rows[0]['lateArrivals'],'nativeMs':{key:statistics.median(row['native'][key] for row in rows)/1e6 for key in ['updateElapsedNs','queryElapsedNs','mergeElapsedNs','mergedQueryElapsedNs']},'roundTripMs':{key:statistics.median(row['roundTrip'][key] for row in rows) for key in ['updateMs','queryMs','mergeMs','mergedQueryMs']},'updateStats':rows[0]['updateStats'],'mergeStats':rows[0]['mergeStats']} for (mode,size),rows in sorted(native_groups.items())]
print(json.dumps(summary,indent=2))
