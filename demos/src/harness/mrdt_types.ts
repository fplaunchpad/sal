import type { ReactNode } from "react";
import type { OpMeta } from "./types";

/**
 * A state-based MRDT. Merge takes three arguments: the LCA state `l` plus two
 * branch states `a` and `b`. Contrast with `CRDTSpec.merge(a, b)` which has no
 * LCA: MRDTs get causality from the history DAG.
 */
export interface MRDTSpec<Concrete, Abstract, Op> {
  name: string;
  slug: string;
  tagline: string;
  init: Concrete;
  apply(s: Concrete, op: Op, meta: OpMeta): Concrete;
  merge(l: Concrete, a: Concrete, b: Concrete): Concrete;
  abstract(s: Concrete): Abstract;
  renderAbstract(a: Abstract): ReactNode;
  renderConcrete(s: Concrete): ReactNode;
  opForm(props: { state: Concrete; dispatch: (op: Op) => void }): ReactNode;
  formatOp(op: Op, meta: OpMeta): string;
}
