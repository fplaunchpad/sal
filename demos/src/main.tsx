import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import {
  HashRouter,
  Navigate,
  Route,
  Routes,
  Link,
  useParams,
} from "react-router-dom";
import { Playground } from "./harness/Playground";
import { MRDTPlayground } from "./harness/MRDTPlayground";
import type { CRDTSpec } from "./harness/types";
import type { MRDTSpec } from "./harness/mrdt_types";
import { spec as incSpec } from "./crdts/increment_only_counter";
import { spec as pnSpec } from "./crdts/pn_counter";
import { spec as boundedSpec } from "./crdts/bounded_counter";
import { spec as maxRegSpec } from "./crdts/max_register";
import { spec as minRegSpec } from "./crdts/min_register";
import { spec as lwwRegSpec } from "./crdts/lww_register";
import { spec as mvRegSpec } from "./crdts/multi_valued_register";
import { spec as gSetSpec } from "./crdts/grow_only_set";
import { spec as gMultisetSpec } from "./crdts/grow_only_multiset";
import { spec as orSpec } from "./crdts/or_set";
import { spec as lwwElSetSpec } from "./crdts/lww_element_set";
import { spec as lwwMapSpec } from "./crdts/lww_map";
import { spec as maxMapSpec } from "./crdts/max_map";
import { spec as cartSpec } from "./crdts/shopping_cart";
import { spec as pqSpec } from "./crdts/pq_insert_only";
import { spec as adwPqSpec } from "./crdts/add_win_pq";
import { spec as rgaSpec } from "./crdts/rga";
import { spec as peritextSpec } from "./crdts/peritext";
import { spec as mIncSpec } from "./mrdts/increment_only_counter";
import { spec as mPnSpec } from "./mrdts/pn_counter";
import { spec as mGSetSpec } from "./mrdts/grow_only_set";
import { spec as mMvrSpec } from "./mrdts/multi_valued_register";
import { spec as mGMapSpec } from "./mrdts/grow_only_map";
import { spec as mOrSpec } from "./mrdts/or_set";
import { spec as mOrEffSpec } from "./mrdts/or_set_efficient";
import { spec as mRgaSpec } from "./mrdts/rga";
import { spec as mEwfSpec } from "./mrdts/enable_wins_flag";
import "./style.css";

// Heterogeneous registries: each spec has its own Concrete/Op types, so we
// erase them here. Playground consumes the spec as an opaque *Spec<any,any,any>.
type AnyCRDT = CRDTSpec<any, any, any>;
type AnyMRDT = MRDTSpec<any, any, any>;

interface CRDTGroup {
  heading: string;
  specs: AnyCRDT[];
}

const crdtGroups: CRDTGroup[] = [
  { heading: "Counters", specs: [incSpec, pnSpec, boundedSpec] },
  { heading: "Registers", specs: [maxRegSpec, minRegSpec, lwwRegSpec, mvRegSpec] },
  { heading: "Sets", specs: [gSetSpec, gMultisetSpec, orSpec, lwwElSetSpec] },
  { heading: "Maps", specs: [lwwMapSpec, maxMapSpec, cartSpec] },
  { heading: "Priority queues", specs: [pqSpec, adwPqSpec] },
  { heading: "Sequences", specs: [rgaSpec, peritextSpec] },
];

const crdtSpecs: AnyCRDT[] = crdtGroups.flatMap((g) => g.specs);

const mrdtSpecs: AnyMRDT[] = [
  mIncSpec,
  mPnSpec,
  mMvrSpec,
  mGSetSpec,
  mGMapSpec,
  mOrSpec,
  mOrEffSpec,
  mRgaSpec,
  mEwfSpec,
];

function Landing() {
  return (
    <div className="landing">
      <h1>Sal CRDT playgrounds</h1>
      <p>
        Interactive simulators for the CRDTs and MRDTs verified in{" "}
        <a href="https://github.com/fplaunchpad/sal">Sal</a>. CRDTs do two-way
        merge (pick a source and target, target absorbs source); MRDTs do
        three-way merge over a git-style commit DAG with LCA computed from
        the history. Toggle the concrete state to see the lattice layer that
        makes convergence work.
      </p>

      <h2 style={{ marginTop: "1.5rem" }}>CRDTs (two-way merge)</h2>
      {crdtGroups.map((g) => (
        <section key={g.heading}>
          <h3>{g.heading}</h3>
          <ul className="demo-list">
            {g.specs.map((s) => (
              <li key={s.slug}>
                <Link to={`/crdt/${s.slug}`}>{s.name}</Link>
                <p>{s.tagline}</p>
              </li>
            ))}
          </ul>
        </section>
      ))}

      <h2 style={{ marginTop: "1.5rem" }}>MRDTs (three-way merge, history DAG)</h2>
      <section>
        <ul className="demo-list">
          {mrdtSpecs.map((s) => (
            <li key={s.slug}>
              <Link to={`/mrdt/${s.slug}`}>{s.name}</Link>
              <p>{s.tagline}</p>
            </li>
          ))}
        </ul>
      </section>
    </div>
  );
}

function CRDTRoute() {
  const { slug } = useParams();
  const found = crdtSpecs.find((s) => s.slug === slug);
  if (!found) return <Navigate to="/" replace />;
  return (
    <>
      <nav>
        <Link to="/">← all demos</Link>
      </nav>
      <Playground spec={found} />
    </>
  );
}

function MRDTRoute() {
  const { slug } = useParams();
  const found = mrdtSpecs.find((s) => s.slug === slug);
  if (!found) return <Navigate to="/" replace />;
  return (
    <>
      <nav>
        <Link to="/">← all demos</Link>
      </nav>
      <MRDTPlayground spec={found} />
    </>
  );
}

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <HashRouter>
      <Routes>
        <Route path="/" element={<Landing />} />
        <Route path="/crdt/:slug" element={<CRDTRoute />} />
        <Route path="/mrdt/:slug" element={<MRDTRoute />} />
        {/* legacy single-slug routes (phase 1–3 URLs) */}
        <Route path="/:slug" element={<CRDTRoute />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </HashRouter>
  </StrictMode>,
);
