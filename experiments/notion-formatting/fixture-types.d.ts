/** Type contract for results/demo.json and results/design.json. */
export type ScalarId = {kind: 'start'} | {kind: 'end'} |
  {kind: 'op'; sessionId: string; counter: number};
export interface Anchor {
  id: ScalarId;
  side: 'before' | 'after';
  /** null means the anchor's item is not reachable from START. */
  position: number | null;
}
export interface TraversalItem {
  index: number;
  id: ScalarId;
  origin: ScalarId;
  kind: 'text' | 'split';
  text: string;
  deleted: boolean;
  /** entry is the item's index; exit is its exclusive subtree end. */
  entry: number;
  exit: number;
}
export interface Mark {
  id: ScalarId;
  value: boolean;
  start: Anchor;
  end: Anchor;
  /** Includes split markers and tombstones; resolved filters these later. */
  coveredIndices: number[];
}
export interface ResolvedCharacter {id: ScalarId; text: string; bold: boolean}
export interface Instance {
  id: string;
  traversal: TraversalItem[];
  /** Sorted ascending by (counter, sessionId), independent of input list. */
  operations: Mark[];
  resolved: ResolvedCharacter[];
}
export interface DisplayBlock {block: string; text: string; bits: string}
export interface ReplicaFixture {
  /** Original source-compatible archive, intentionally without ID rewriting. */
  transactions: unknown[];
  display: DisplayBlock[];
  instances: Instance[];
}
export type Display = [text: string, boldBits: string][];
export interface ClientCase {
  name: string;
  evidence: 'measured';
  expected: Display;
  /** A hand-derived rival output that this case must reject. */
  rejected: Display;
  controlsHold: true;
  fixture: ReplicaFixture;
}
export interface RawCase {
  name: string;
  evidence: 'measured';
  expected: [text: string, bold: boolean][];
  rejected: [text: string, bold: boolean][];
  controlsHold: true;
  fixture: Instance;
}
export interface SourceFailure {
  name: string;
  evidence: 'refuted-by-execution';
  expected: Display;
  observed: Display;
  controlsHold: true;
  transaction: unknown;
  fixture: ReplicaFixture;
}
export interface Export {
  schema: 'notion-formatting-fixture-v1';
  cases: ClientCase[];
  rawCases: RawCase[];
  sourceFailures: SourceFailure[];
  summary: {clientCases: number; rawCases: number; sourceFailures: number;
    positiveAndNegativeControls: number};
  /** Unmodified N-002/N-003 cases reissued by the merge-design gate. */
  recordedRegressions: unknown[];
  /** Isolated experiment, never a replacement for the original source cases. */
  candidate: CandidateExport;
}
export interface CandidatePlan {
  value: boolean;
  segments: {textInstanceId: string;
    start: {id: unknown; anchor: 'before'};
    end: {id: unknown; anchor: 'before'}}[];
}
export interface CandidateCase {
  name: string;
  implementation: 'candidate-planner';
  evidence: 'measured';
  expected: Display;
  rejected: Display;
  actual: Display;
  controlsHold: true;
  preparation: {plan: CandidatePlan; selection: unknown[];
    finiteExactCoverage: true; transaction: unknown};
  transactions: unknown[];
}
export interface CandidateExport {
  schema: 'notion-formatting-candidate-v1';
  status: 'finite-tests-only; no general refinement or RA theorem';
  cases: CandidateCase[];
  summary: {sourceAppliedCases: number; positiveAndNegativeControls: number;
    finiteExactCoverageCases: number};
}
