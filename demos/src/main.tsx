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
import { spec as mAdwPqSpec } from "./mrdts/add_win_pq";
import { spec as mEwfSpec } from "./mrdts/enable_wins_flag";
import { spec as mPeritextSpec } from "./mrdts/peritext";
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
  { heading: "Priority queues", specs: [adwPqSpec] },
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
  mPeritextSpec,
  mAdwPqSpec,
  mEwfSpec,
];

function Landing() {
  return (
    <div className="landing">
      <h1>Sal CRDT playgrounds</h1>
      <p>
        Interactive simulators for every CRDT and MRDT verified in{" "}
        <a href="https://github.com/fplaunchpad/sal">Sal</a>, a Lean 4
        framework that proves <strong>replication-aware
        linearizability</strong> (a strict strengthening of the usual
        commutative–associative–idempotent merge story) on a 24-VC schema
        for state-based replicated data types. Every RDT in the framework
        is also instrumented with a{" "}
        <strong>read-side projection</strong> that lifts the user-facing
        semantic claim — "is <code>e</code> in
        the OR-Set?", "is this character bold in Peritext?", "does this
        counter equal <code>incs − decs</code>?" — into a Lean theorem,
        with concrete <em>SPOT</em> tests pinning the headline behaviour
        on small executions.
      </p>
      <p>
        The playgrounds let you exercise those data structures
        operationally:
      </p>
      <ul style={{ marginTop: "0.25rem", marginBottom: "0.75rem" }}>
        <li>
          <strong>CRDTs</strong> — two-way merge between replicas. Issue
          ops at any replica, then pick a source and a target — the
          target absorbs the source. The lattice underneath converges
          regardless of the order you choose.
        </li>
        <li>
          <strong>MRDTs</strong> — three-way merge over a git-style
          commit DAG. Branches diverge, you merge them with the LCA
          computed from history. Toggle the "concrete state" view to see
          the lattice layer driving convergence.
        </li>
      </ul>
      <p>
        Each demo's controls match the operations in the corresponding
        Lean file (look for <code>app_op_t</code> in the linked source);
        the read-side query the simulator displays matches the headline
        theorem in the <code>*_ReadSide.lean</code> companion. Background
        on methodology:{" "}
        <a href="https://github.com/fplaunchpad/sal/blob/main/docs/readside-projections.md">
          read-side projections
        </a>
        ,{" "}
        <a href="https://github.com/fplaunchpad/sal/blob/main/docs/porting-op-based-crdts.md">
          porting op-based CRDTs into Sal
        </a>
        .
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
