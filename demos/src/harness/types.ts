import type { ReactNode } from "react";

export interface OpMeta {
  ts: number;
  rid: number;
}

/**
 * A CRDT the playground knows how to simulate. The types Concrete, Abstract,
 * and Op are CRDT-specific; the harness treats them as opaque.
 */
export interface CRDTSpec<Concrete, Abstract, Op> {
  /** Display name, e.g. "PN-Counter". */
  name: string;
  /** URL slug, e.g. "pn-counter". */
  slug: string;
  /** One-line pedagogical summary shown at the top of the playground. */
  tagline: string;
  /** Initial state used for a fresh replica. */
  init: Concrete;
  /** Apply a local op. `meta` carries a monotonic timestamp and replica id. */
  apply(s: Concrete, op: Op, meta: OpMeta): Concrete;
  /** Two-way CRDT merge; must be commutative, idempotent, associative. */
  merge(a: Concrete, b: Concrete): Concrete;
  /** Projection onto the user-observable value (what you'd see in production). */
  abstract(s: Concrete): Abstract;
  /** Render the abstract view of a replica. */
  renderAbstract(a: Abstract): ReactNode;
  /** Render the concrete (lattice) view of a replica. */
  renderConcrete(s: Concrete): ReactNode;
  /**
   * Render the op-input form for a replica. Receives the replica's current
   * concrete state so the form can gate ops with preconditions (e.g. Bounded
   * Counter Dec requires balance).
   */
  opForm(props: {
    state: Concrete;
    dispatch: (op: Op) => void;
  }): ReactNode;
  /** Pretty-printer for op history entries. */
  formatOp(op: Op, meta: OpMeta): string;
}
