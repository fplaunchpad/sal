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
import { spec as orSpec } from "./crdts/or_set";
import "./style.css";

// Heterogeneous registry: each spec has its own Concrete/Op types, so we erase
// them here. Playground consumes the spec as an opaque CRDTSpec<any, any, any>.
type AnySpec = CRDTSpec<any, any, any>;
const specs: AnySpec[] = [incSpec, pnSpec, orSpec];

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
      <ul className="demo-list">
        {specs.map((s) => (
          <li key={s.slug}>
            <Link to={`/${s.slug}`}>{s.name}</Link>
            <p>{s.tagline}</p>
          </li>
        ))}
      </ul>
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
