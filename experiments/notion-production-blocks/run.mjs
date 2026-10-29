/**
 * One search configuration over the production block layer.
 *
 *   NOTION_PRODUCTION_LIBRARY=<export> node run.mjs --texts '["a","b","c"]' \
 *     --profile structure --trials 100 --steps 10 [--partial] [--opened] \
 *     [--replicas 2] [--seeds 1,2] [--reading '{"splitPlacement":"source"}'] \
 *     [--shrink] [--out results/run.json]
 *
 * Prints the trial counts per check and per (check, class); with --shrink,
 * also the shrunk representative of each (check, class). The library is
 * verified before and after.
 */
import { writeJson } from '../../ra-pbt/src/index.js';
import { withVerifiedLibrary } from '../../ra-pbt/instances/notion-production-blocks/index.js';
import { searchConfiguration, shrinkClass, runClassified, renderStep } from './lib.mjs';

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith('--')) throw new Error('unexpected argument ' + a);
    const k = a.slice(2);
    if (['partial', 'opened', 'shrink'].includes(k)) out[k] = true;
    else out[k] = argv[++i];
  }
  return out;
}

const args = parseArgs(process.argv.slice(2));
const cfg = {
  name: 'run',
  texts: JSON.parse(args.texts ?? '["a","b","c"]'),
  profile: args.profile ?? 'structure',
  partial: !!args.partial,
  opened: !!args.opened,
  steps: Number(args.steps ?? 10),
  trials: Number(args.trials ?? 50),
  ...(args.replicas ? { replicas: Number(args.replicas) } : {}),
  ...(args.reading ? { reading: JSON.parse(args.reading) } : {}),
};
const seeds = (args.seeds ?? '1').split(',').map(Number);
const result = await withVerifiedLibrary(async (lib) => {
  const r = searchConfiguration(lib, cfg, seeds);
  if (args.shrink)
    r.shrunk = Object.fromEntries(
      Object.entries(r.first).map(([key, first]) => {
        const [check, cls] = key.split(':');
        const s = shrinkClass(lib, r.options, first.schedule, check, cls).schedule;
        return [key, { rendered: s.steps.map(renderStep), schedule: s, classes: runClassified(lib, r.options, s).classes }];
      }),
    );
  delete r.first;
  return r;
});
console.log(JSON.stringify({ totals: result.totals, trialsByCheck: result.trialsByCheck, trialsByClass: result.trialsByClass }, null, 1));
if (result.shrunk) for (const [k, v] of Object.entries(result.shrunk)) console.log(`${k}: ${v.rendered.join('; ')}`);
if (args.out) writeJson(args.out, result);
