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
import type { CRDTSpec } from "./harness/types";
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
import "./style.css";

// Heterogeneous registry: each spec has its own Concrete/Op types, so we erase
// them here. Playground consumes the spec as an opaque CRDTSpec<any, any, any>.
type AnySpec = CRDTSpec<any, any, any>;

interface Group {
  heading: string;
  specs: AnySpec[];
}

const groups: Group[] = [
  {
    heading: "Counters",
    specs: [incSpec, pnSpec, boundedSpec],
  },
  {
    heading: "Registers",
    specs: [maxRegSpec, minRegSpec, lwwRegSpec, mvRegSpec],
  },
  {
    heading: "Sets",
    specs: [gSetSpec, gMultisetSpec, orSpec, lwwElSetSpec],
  },
  {
    heading: "Maps",
    specs: [lwwMapSpec, maxMapSpec, cartSpec],
  },
  {
    heading: "Priority queues",
    specs: [pqSpec, adwPqSpec],
  },
  {
    heading: "Sequences",
    specs: [rgaSpec, peritextSpec],
  },
];

const specs: AnySpec[] = groups.flatMap((g) => g.specs);

function Landing() {
  return (
    <div className="landing">
      <h1>Sal CRDT playgrounds</h1>
      <p>
        Each playground simulates three replicas of a CRDT verified in{" "}
        <a href="https://github.com/fplaunchpad/sal">Sal</a>. Apply operations
        locally per replica, then merge replicas directionally — pick a{" "}
        <em>source</em> and a <em>target</em>, click Merge, and the target
        absorbs the source (source unchanged, just like <code>git merge</code>).
        Toggle the concrete state to see the lattice representation that makes
        convergence work.
      </p>
      {groups.map((g) => (
        <section key={g.heading}>
          <h2>{g.heading}</h2>
          <ul className="demo-list">
            {g.specs.map((s) => (
              <li key={s.slug}>
                <Link to={`/${s.slug}`}>{s.name}</Link>
                <p>{s.tagline}</p>
              </li>
            ))}
          </ul>
        </section>
      ))}
    </div>
  );
}

function DemoRoute() {
  const { slug } = useParams();
  const found = specs.find((s) => s.slug === slug);
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

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <HashRouter>
      <Routes>
        <Route path="/" element={<Landing />} />
        <Route path="/:slug" element={<DemoRoute />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </HashRouter>
  </StrictMode>,
);
