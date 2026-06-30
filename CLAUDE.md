# Project notes for agents

- Before working on any RGA MRDT (anything under `Sal/MRDTs/RGA*`), read
  `AgentNotes.md` at the repo root. It indexes the several RGA design attempts,
  records which one is proved (the tombstone-free path-carrying RGA in
  `Sal/MRDTs/RGA_Splice/RGA_Path_MRDT.lean`), and says which branch each
  unfinished attempt is parked on.

- Review `README.md` on every push and keep it consistent with the actual state
  of the repo. Before pushing, check that the "What's verified" catalog, the RDT
  count, and any file or branch references match what is on the branch being
  pushed (RDTs added, removed, renamed, or moved; sorries closed or opened).
  Update `README.md` in the same push if it has drifted.
