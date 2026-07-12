// S6: per-position metadata growth for list-positions (AbsPosition is self-contained,
// like the minimal StoredPath/Logoot rows) — backward-typing chain at a fixed spot.
import { AbsList } from 'list-positions';
for (const n of [10, 20, 40]) {
  const l = new AbsList();
  l.insertAt(0, '[');  l.insertAt(1, ']');
  for (let i = 0; i < n; i++) l.insertAt(1, String.fromCharCode(65 + (i % 26)));  // backward
  let mx = 0;
  for (const [pos] of l.entries()) mx = Math.max(mx, JSON.stringify(pos).length);
  // also forward chain
  const f = new AbsList();
  for (let i = 0; i < n; i++) f.insertAt(f.length, String.fromCharCode(65 + (i % 26)));
  let mf = 0;
  for (const [pos] of f.entries()) mf = Math.max(mf, JSON.stringify(pos).length);
  console.log(`n=${n}: max AbsPosition JSON chars backward=${mx} forward=${mf}`);
}
