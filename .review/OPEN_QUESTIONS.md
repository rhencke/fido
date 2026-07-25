# Open questions — Claude Code to the reviewer and to Rob

Questions raised from implementation that are **neither** a contract conflict **nor** a human disposition
already tracked elsewhere. It exists so a question lives in Git at the exact ref rather than only in a chat that
does not travel with the repository.

**What belongs here.** Scoping calls, ambiguities in an active authority, and findings that need a second pair
of eyes but do not contradict a protected contract.

**What does not.** A genuine conflict with a protected FCB contract goes through the bootstrap rule — stop at
the boundary, report, the reviewer authors a named amendment, Rob accepts. An open human act (an ADR, a policy
choice, a countersign) belongs in `.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md`. A request for a review
is `.review/REVIEW_REQUEST.md`. This file is none of those and overrides nothing: it is not authority, and
nothing in it licenses work that an authority forbids.

**Every entry states a default.** A question with a recorded default is a disclosure; a question without one is
a blocker I invented for myself. If nobody answers, I do the default and say so in the commit that relies on it.
Answered entries are updated in place with the answer, then deleted once their commit has landed — Git history
is the archive.

---

## Q-01 — May repair-14 implementation begin?

- **Owner:** Rob
- **Blocking:** yes, for code work
- **Question:** The Review 100 repair is complete and pushed. The Phase-B preconditions from the combined
  directive appear satisfied: A001 accepted, its artifact committed, the FCB set generated and installed,
  project libraries reduced to shims, and the manifest-verification precondition retired by A003. The stop in
  Review 100 was scoped to "these commits," which have landed. Is implementation of
  `.review/C4_IMPLEMENTATION_REPAIR_14.md` §2–§12 authorized to begin?
- **ANSWERED 2026-07-25 — Rob: AUTHORIZED.** *Begin `.review/C4_IMPLEMENTATION_REPAIR_14.md` implementation on
  the current `main` head. Do not reset to `9d5246e`. Preserve all out-of-band changes already recorded in
  `.review/NEXT_STEPS.md`. C5 and the post-C4 trim remain forbidden.* Recorded in `NEXT_STEPS.md`,
  `SOURCE_FOREST_STATUS.md` and the FCB Index. **Removed from this file in the first implementation commit
  that relies on it.**
- **Origin:** Review 100 "Stop after these commits"; the combined directive's two-phase gate.

## Q-04 — Is deleting `IndexedProgram` in scope for repair 14?

- **Owner:** reviewer
- **Blocking:** no
- **Question:** The original directive said to keep the `IndexedProgram` deletion decision open "unless repair 14
  proves the wrapper redundant and separately authorizes deletion." If the retained `ElaborationCore` does make
  the wrapper redundant, should this repair delete it, or report the finding and leave it?
- **ANSWERED 2026-07-25 — reviewer: NO, leave `IndexedProgram` in place during repair 14.** Repair 14 is limited
  to the final retained-elaboration boundary; deleting a capability-adjacent wrapper in the same repair would
  enlarge the review surface. If the retained core makes it clearly redundant: record the exact redundancy and
  the affected queries and theorems, keep the wrapper, and propose deletion under a separate explicit contract,
  preferably the post-C4 trim unless a correctness conflict forces it earlier. It may remain only as the exact
  wrapper or projection and must never become a parallel semantic authority. **Removed from this file in the
  first implementation commit.**
- **Origin:** combined directive, Architecture Charter §4 replacement note.

