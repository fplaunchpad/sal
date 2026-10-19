#!/usr/bin/env python3
"""Executable gate for the block-merge design (docs/notion-merge-block-design.md).

Fetches or reads the seven hash-pinned demo modules, builds one working copy per
variant (the demo, the design, the slice-following and anchor-absorb
candidates and controls;
see design-patch/patch.py),
and runs in each, with the RA check preloaded:

  gate.mjs              the recorded bugs N-001 to N-005, reissued as requests
  litmus.mjs            merge litmus histories (a) to (i), all schedules
  network-search.mjs    persistent replicas, partial causal delivery (seed 27002)
  offline-search.mjs    offline split/merge bursts, conservation (seed 17102)
  campaign.mjs          complete-exchange search 17002 and 17005, sequential 17004
  structural.mjs        complete-exchange split/merge conservation (seed 17003)

The search harnesses are the committed files of experiments/notion-correctness,
copied unchanged except one line of campaign.mjs: its calibration assertion
that the demo's two bold bugs reproduce becomes a no-op, because the gate
reports those counts instead. The demo working copy also runs the committed
calibration scripts, which must exit successfully.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXP = ROOT.parent
sys.path.insert(0, str(ROOT / 'design-patch'))
import patch  # noqa: E402

CAMPAIGN_CALIBRATION = "if(mode!=='sequential')assert(counts.failures['bold:missed']>0&&counts.failures['bold:outside']>0);"
CAMPAIGN_REPLACEMENT = "// Calibration assertion of the demo's bold bugs removed: the gate reports these counts."

FULL_JOBS = {
    'gate': ['gate.mjs'],
    'litmus': ['litmus.mjs'],
    'network-27002': ['network-search.mjs', '27002', '100', '80'],
    'offline-17102': ['offline-search.mjs', '17102', '12', '110', 'structural'],
    'campaign-17002': ['campaign.mjs', 'search', '17002', '250'],
    'campaign-17005': ['campaign.mjs', 'search', '17005', '100'],
    'sequential-17004': ['campaign.mjs', 'sequential', '17004', '60'],
    'structural-17003': ['structural.mjs'],
}
QUICK_JOBS = {**FULL_JOBS,
    'network-27002': ['network-search.mjs', '27002', '8', '80'],
    'offline-17102': ['offline-search.mjs', '17102', '3', '110', 'structural'],
    'campaign-17002': ['campaign.mjs', 'search', '17002', '12'],
    'campaign-17005': ['campaign.mjs', 'search', '17005', '8'],
    'sequential-17004': ['campaign.mjs', 'sequential', '17004', '6'],
}
MODES = ['absorb', 'skip', 'removed', 'sliceFollow', 'sliceFollowAnchor']
# The specification mode each variant is meant to implement.
OWN_MODE = {'skip': 'skip', 'skip-remove-independently': 'skip',
            'slice-following': 'sliceFollow', 'slice-remove-independently': 'sliceFollow', 'anchor-absorb': 'sliceFollow'}
# The litmus column of hand-derived finals each variant is checked against
# (litmus.mjs): `expected` (absorb) unless listed.
LITMUS_COLUMN = {'skip': 'skip', 'skip-remove-independently': 'skip', 'slice-following': 'slice',
                 'slice-remove-independently': 'slice', 'anchor-absorb': 'anchor'}
CALIBRATION = ['original-regressions.mjs', 'regressions.mjs', 'controls.mjs', 'network-controls.mjs', 'offline-regression.mjs']


def fetch(manifest, cache):
    cache.mkdir(parents=True, exist_ok=True)
    for m in manifest['modules']:
        target = cache / m['file']
        if not target.exists():
            subprocess.run(['curl', '-fsSL', m['url'], '-o', str(target)], check=True)


def workdir(base, variant, sources):
    w = base / variant
    w.mkdir()
    (w / 'package.json').write_text('{"type":"module"}\n')
    for name, text in patch.apply(variant, sources).items():
        (w / name).write_text(text)
    for f in (EXP / 'notion-correctness').glob('*.mjs'):
        shutil.copyfile(f, w / f.name)
    shutil.copyfile(EXP / 'notion-oracle' / 'positional-spec.mjs', w / 'positional-spec.mjs')
    shutil.copyfile(EXP / 'notion-oracle' / 'regressions.mjs', w / 'original-regressions.mjs')
    campaign = (w / 'campaign.mjs').read_text()
    if campaign.count(CAMPAIGN_CALIBRATION) != 1:
        raise ValueError('campaign.mjs calibration line not found exactly once')
    (w / 'campaign.mjs').write_text(campaign.replace(CAMPAIGN_CALIBRATION, CAMPAIGN_REPLACEMENT))
    for f in ROOT.glob('*.mjs'):
        shutil.copyfile(f, w / f.name)
    return w


def run_job(w, name, argv):
    report = w / f'ra-{name}.json'
    env = {**os.environ, 'RA_REPORT': str(report)}
    start = time.time()
    r = subprocess.run(['node', '--import', './ra-hook.mjs', *argv], cwd=w, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = {'argv': argv, 'exit': r.returncode, 'seconds': round(time.time() - start, 1)}
    if r.returncode != 0:
        out['stderr'] = r.stderr[-3000:]
    try:
        out['output'] = json.loads(r.stdout)
    except json.JSONDecodeError:
        out['stdout'] = r.stdout[-2000:]
    out['ra'] = json.loads(report.read_text()) if report.exists() else None
    if name.startswith('network') and r.returncode == 0:
        (w / f'{name}-output.json').write_text(r.stdout)
    return name, out


def texts_of(blocks):
    if isinstance(blocks, list) and all(isinstance(b, list) for b in blocks):
        return [''.join(c.get('text', '') if isinstance(c, dict) else str(c) for c in b) for b in blocks]
    return blocks


def finding_kinds(findings):
    kinds = {}
    for f in findings:
        k = f['result'].get('signature') if 'result' in f else 'text-loss'
        kinds[k] = kinds.get(k, 0) + 1
    return kinds


def compact(name, out, own):
    """Keep counts, findings and RA summaries at a committable size: per-trial
    traces, per-run litmus logs and bulk archives are dropped; for each
    disagreement category of the variant's own specification mode, the
    smallest archive is kept when it has at most 40 transactions."""
    out = dict(out)
    o = out.get('output')
    if isinstance(o, dict):
        o = dict(o)
        if 'traces' in o:
            o['traceCount'] = len(o.pop('traces'))
        if 'failureStates' in o:
            o['failureStateCount'] = len(o.pop('failureStates'))
        if name == 'litmus':
            o['results'] = [{**e, 'base': [{k: v for k, v in b.items() if k != 'log'} for b in e['base']]} for e in o['results']]
        if name == 'gate':
            o['cases'] = [{**c, **{k: texts_of(c[k]) for k in ['expected', 'actual'] if k in c}} for c in o['cases']]
        if name.startswith(('offline', 'structural')) and isinstance(o.get('findings'), list) and 'findingCount' not in o:
            o['findingCount'] = len(o['findings'])
            if name.startswith('structural'):
                o['findingKinds'] = finding_kinds(o['findings'])
            o['findings'] = o['findings'][:2]
        if name.endswith('shrink'):
            for f in o.get('findings', []):
                d = f.get('disagreement') or {}
                if len(d.get('transactions') or []) > 40:
                    d['transactions'] = None
        out['output'] = o
    r = out.get('ra')
    if isinstance(r, dict):
        r = dict(r)
        kept = {}
        for category, items in (r.get('failures', {}).get(own) or {}).items():
            if items:
                # An already compacted file holds one archive per category.
                x = dict(items if isinstance(items, dict) else items[0])
                if x.get('transactions') and len(x['transactions']) > 40:
                    x['transactions'] = None
                kept[category] = x
        r['failures'] = {own: kept}
        if r.get('orderInversionExample'):
            r['orderInversionExample'] = {k: v for k, v in r['orderInversionExample'].items() if k != 'transactions'}
        out['ra'] = r
    return out


def summarise(variant, jobs):
    row = {'variant': variant, 'ownMode': OWN_MODE.get(variant, 'absorb')}
    ra = {'archives': 0, **{mode: {} for mode in MODES}, 'orderInversions': 0, 'replayExceptions': 0,
          'shape': {'archives': 0, 'branching': 0, 'maxChildren': 0, 'disagreements': {}},
          'deletesCrossing': [0, 0], 'deletesSingle': [0, 0]}
    for name, j in jobs.items():
        r = j.get('ra')
        if not r or name.endswith('shrink'):
            continue
        ra['archives'] += r['archives']
        ra['orderInversions'] += r['orderInversions']
        ra['replayExceptions'] += r['replayExceptions']
        if 'shape' in r:
            ra['shape']['archives'] += r['shape']['archives']
            ra['shape']['branching'] += r['shape']['branching']
            ra['shape']['maxChildren'] = max(ra['shape']['maxChildren'], r['shape']['maxChildren'])
            for mode, d in r['shape'].get('disagreements', {}).items():
                acc = ra['shape']['disagreements'].setdefault(mode, {'branching': 0, 'chain': 0})
                for k in acc:
                    acc[k] += d.get(k, 0)
        for mode in MODES:
            for k, v in r['modes'][mode].items():
                ra[mode][k] = ra[mode].get(k, 0) + v
        if 'deletes' in r:
            for kind, key in [('crossing', 'deletesCrossing'), ('single', 'deletesSingle')]:
                ra[key][0] += r['deletes'][kind]['checked']
                ra[key][1] += r['deletes'][kind]['agree']
    row['ra'] = ra
    local = {}
    for name in ['network-27002', 'offline-17102', 'campaign-17002', 'campaign-17005', 'sequential-17004']:
        o = (jobs.get(name) or {}).get('output') or {}
        c = o.get('counts', {})
        if name.startswith('offline'):
            local[name] = {'localFailures': c.get('localFailures'), 'conservationFailures': c.get('conservationFailures'),
                           'exceptions': c.get('exceptions'), 'locals': c.get('locals'), 'receives': c.get('receives')}
        else:
            local[name] = {'failures': c.get('failures'), 'mergePasses': (c.get('passes') or {}).get('merge')}
    st = (jobs.get('structural-17003') or {}).get('output') or {}
    kinds = st['findingKinds'] if 'findingKinds' in st else finding_kinds(st.get('findings', []))
    local['structural-17003'] = {'states': (st.get('counts') or {}).get('states'), 'failures': kinds}
    row['harness'] = local
    g = (jobs.get('gate') or {}).get('output') or {}
    row['regressions'] = {c['name']: {'holds': c.get('contractHolds'), 'precondition': c.get('preconditionReached'),
                                      'controlsHold': all(x['holds'] for x in c.get('controls', {}).values()) if c.get('controls') else None}
                          for c in g.get('cases', [])}
    row['sensitivity'] = g.get('sensitivity')
    lit = (jobs.get('litmus') or {}).get('output') or {}
    row['litmus'] = lit.get('summary')
    column = LITMUS_COLUMN.get(variant, 'expected')
    key = {'expected': 'finalFailures', 'skip': 'finalSkipFailures', 'slice': 'finalSliceFailures', 'anchor': 'finalAnchorFailures'}[column]
    if row['litmus']:
        row['litmusOwn'] = {'column': column, 'finalChecks': row['litmus'].get('finalChecks'), 'finalFailures': row['litmus'].get(key)}
    row['exits'] = {name: j['exit'] for name, j in jobs.items()}
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--cache', type=Path, help='directory of the pinned modules (fetched here if absent)')
    p.add_argument('--results', type=Path, default=ROOT / 'results')
    p.add_argument('--variants', nargs='*', default=patch.VARIANTS, choices=patch.VARIANTS)
    p.add_argument('--quick', action='store_true', help='small trial counts, for checking the runner')
    p.add_argument('--jobs', type=int, default=os.cpu_count())
    p.add_argument('--from-results', action='store_true',
                   help='re-trim the per-variant files in --results and regenerate the summary without rerunning')
    a = p.parse_args()
    if a.from_results:
        summary = json.loads((a.results / 'summary.json').read_text())
        rows = []
        for row in summary['variants']:
            v = row['variant']
            jobs = json.loads((a.results / f'{v}.json').read_text())['jobs']
            jobs = {k: compact(k, j, OWN_MODE.get(v, 'absorb')) for k, j in jobs.items()}
            # Files compacted before per-kind structural counts were stored
            # keep two findings; their counts are taken from the summary row.
            st = (jobs.get('structural-17003') or {}).get('output')
            if isinstance(st, dict) and 'findingKinds' not in st:
                st['findingKinds'] = row['harness']['structural-17003']['failures']
            with (a.results / f'{v}.json').open('w') as out:
                json.dump({'variant': v, 'jobs': jobs}, out, indent=1)
                out.write('\n')
            rows.append(summarise(v, jobs))
        summary['variants'] = rows
        with (a.results / 'summary.json').open('w') as out:
            json.dump(summary, out, indent=1)
            out.write('\n')
        print_table(summary)
        return
    manifest_path = EXP / 'notion-oracle' / 'sources.json'
    manifest = json.loads(manifest_path.read_text())
    with tempfile.TemporaryDirectory(prefix='notion-merge-design-') as d:
        base = Path(d)
        cache = a.cache or base / 'cache'
        fetch(manifest, cache)
        _, sources = patch.load_pinned(cache, manifest_path)
        dirs = {v: workdir(base, v, sources) for v in a.variants}
        calibration = {}
        if 'demo' in dirs:
            for script in CALIBRATION:
                r = subprocess.run(['node', script], cwd=dirs['demo'], text=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
                calibration[script] = r.returncode
            if any(calibration.values()):
                raise SystemExit(f'demo calibration failed: {calibration}')
        spec = subprocess.run(['node', 'spec-controls.mjs'], cwd=next(iter(dirs.values())), text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if spec.returncode != 0:
            raise SystemExit('identity specification controls failed:\n' + spec.stderr)
        calibration['spec-controls.mjs'] = json.loads(spec.stdout)
        table = QUICK_JOBS if a.quick else FULL_JOBS
        results = {v: {} for v in dirs}
        with cf.ThreadPoolExecutor(max_workers=a.jobs) as pool:
            futures = {pool.submit(run_job, dirs[v], name, argv): v for v in dirs for name, argv in table.items()}
            for f in cf.as_completed(futures):
                v = futures[f]
                name, out = f.result()
                results[v][name] = out
                print(f'{v:26s} {name:18s} exit {out["exit"]} {out["seconds"]}s', file=sys.stderr)
        # Shrink network histories that disagree with the variant's own specification mode.
        shrink_jobs = []
        for v in dirs:
            ra = results[v].get('network-27002', {}).get('ra')
            if ra and any(ra['modes'][OWN_MODE.get(v, 'absorb')][k] for k in ['stuck', 'conservation', 'placement']):
                shrink_jobs.append(v)
        with cf.ThreadPoolExecutor(max_workers=a.jobs) as pool:
            futs = {pool.submit(run_job, dirs[v], 'shrink', ['ra-shrink.mjs', 'network-27002-output.json', OWN_MODE.get(v, 'absorb')]): v
                    for v in shrink_jobs}
            for f in cf.as_completed(futs):
                name, out = f.result()
                results[futs[f]]['network-27002-shrink'] = out
        a.results.mkdir(parents=True, exist_ok=True)
        suffix = '-quick' if a.quick else ''
        summary = {'design': 'docs/notion-merge-block-design.md', 'quick': a.quick, 'calibration': calibration,
                   'node': subprocess.run(['node', '--version'], text=True, stdout=subprocess.PIPE).stdout.strip(),
                   'sourceManifest': manifest, 'variants': [summarise(v, results[v]) for v in dirs]}
        # A run of some variants keeps the other variants' rows, and the demo
        # calibration when the demo was not rerun, from an existing summary.
        previous = a.results / f'summary{suffix}.json'
        if previous.exists() and set(dirs) != set(patch.VARIANTS):
            old = json.loads(previous.read_text())
            rows = {r['variant']: r for r in old.get('variants', [])}
            rows.update({r['variant']: r for r in summary['variants']})
            summary['variants'] = [rows[v] for v in patch.VARIANTS if v in rows]
            if 'demo' not in dirs:
                summary['calibration'] = {**{k: v for k, v in old.get('calibration', {}).items() if k in CALIBRATION},
                                          **summary['calibration']}
        for v in dirs:
            with (a.results / f'{v}{suffix}.json').open('w') as out:
                json.dump({'variant': v, 'jobs': {k: compact(k, j, OWN_MODE.get(v, 'absorb')) for k, j in results[v].items()}}, out, indent=1)
                out.write('\n')
        with (a.results / f'summary{suffix}.json').open('w') as out:
            json.dump(summary, out, indent=1)
            out.write('\n')
    print_table(summary)


def print_table(summary):
    print('\nCalibration (demo scripts must exit 0; specification controls must pass):', summary['calibration'])
    print('\nRA check against each variant\'s own meaning (own) and agreement with every meaning;')
    print('stuck* = stuck when merged sources leave the list; inv = order inversions; xdel = cross-instance deletes')
    print('agreeing with the positional contract; branch = archives with a slice node of more than one child; maxch = most children')
    print(f'{"variant":26s} {"own":11s} {"archives":>8s} {"agree":>7s} {"stuck":>6s} {"cons":>5s} {"place":>6s} '
          f'{"=absorb":>7s} {"=skip":>7s} {"=slice":>7s} {"=sliceA":>7s} {"stuck*":>7s} {"inv":>6s} {"xdel":>9s} {"branch":>6s} {"maxch":>5s}')
    for row in summary['variants']:
        ra, own = row['ra'], row['ownMode']
        o = ra[own]
        agree = {m: ra.get(m, {}).get('agree', 0) for m in ['absorb', 'skip', 'sliceFollow', 'sliceFollowAnchor']}
        print(f'{row["variant"]:26s} {own:11s} {ra["archives"]:8d} {o.get("agree",0):7d} {o.get("stuck",0):6d} {o.get("conservation",0):5d} '
              f'{o.get("placement",0):6d} {agree["absorb"]:7d} {agree["skip"]:7d} {agree["sliceFollow"]:7d} {agree["sliceFollowAnchor"]:7d} '
              f'{ra["removed"].get("stuck",0):7d} {ra["orderInversions"]:6d} {ra["deletesCrossing"][1]:4d}/{ra["deletesCrossing"][0]:<4d} '
              f'{ra["shape"]["branching"]:6d} {ra["shape"]["maxChildren"]:5d}')
    print('\nLocal positional contract and conservation (harness failure counts)')
    for row in summary['variants']:
        print(f'{row["variant"]:26s}', json.dumps({k: (v.get('failures') if 'failures' in v else v) for k, v in row['harness'].items()}))
    print('\nRecorded bugs (contract holds / precondition of the demo failure reached)')
    for row in summary['variants']:
        cells = ', '.join(f'{k.split(" ")[0]}{"" if "variant" not in k and "form" not in k and "control" not in k else "*"}:'
                          f'{"PASS" if r["holds"] else "FAIL" if r["holds"] is False else "n/a"}'
                          f'{"" if r["precondition"] else "(pre no)"}' for k, r in row['regressions'].items())
        print(f'{row["variant"]:26s} {cells}')
    print('\nLitmus (a)-(i): failures against the variant\'s own column of hand-derived finals, then all counts')
    for row in summary['variants']:
        own = row.get('litmusOwn') or {}
        print(f'{row["variant"]:26s} {own.get("column")}: {own.get("finalFailures")}/{own.get("finalChecks")}', json.dumps(row['litmus']))

if __name__ == '__main__':
    main()
