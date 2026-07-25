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
- **Default if unanswered:** do not begin. Hold at the current head with the authority installed.
- **Origin:** Review 100 "Stop after these commits"; the combined directive's two-phase gate.

## Q-02 — Disposition `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`

- **Owner:** Rob
- **Blocking:** no
- **Question:** A004 was delivered `PROPOSED — Rob disposition required`, and its repairs are implemented. I
  recorded it PROPOSED rather than accepted, because recording a human disposition Rob has not given is the one
  error class this system exists to prevent. Accept, amend, or reject?
- **Default if unanswered:** it stays PROPOSED. The live Index and the Governance register both continue to say
  so, and the Human Review Index keeps `FCB-A004` open.
- **Origin:** Review 100, Proposed FCB Amendment A004; `.review/fcb/amendments/`.

## Q-03 — Reconcile `ADR-0001` / `SR-001` status

- **Owner:** Rob
- **Blocking:** no
- **Question:** The FCB records ADR-0001 as adopted for the current basis; this repository still records
  ADR-0001 and SR-001 as `PROPOSED`. The repair-14 authority §12 lists reconciling them as a duty, but changing
  an ADR's status is an authoring act and I am the Committer. Is ADR-0001 / SR-001 `ACCEPTED FOR CURRENT BASIS`,
  with the reopen trigger at C16 or any earlier target/`uintptr` request?
- **Default if unanswered:** leave both at `PROPOSED` in the repository and state the divergence from the FCB
  explicitly wherever either is cited, rather than silently adopting either reading.
- **Origin:** `.review/C4_IMPLEMENTATION_REPAIR_14.md` §12; FCB Governance ADR register.

## Q-04 — Is deleting `IndexedProgram` in scope for repair 14?

- **Owner:** reviewer
- **Blocking:** no
- **Question:** The original directive said to keep the `IndexedProgram` deletion decision open "unless repair 14
  proves the wrapper redundant and separately authorizes deletion." If the retained `ElaborationCore` does make
  the wrapper redundant, should this repair delete it, or report the finding and leave it?
- **Default if unanswered:** report the finding and **leave the wrapper in place**. A capability-surface refactor
  and a public type deletion are two separately reviewable things; combining them is how a fifteenth candidate
  gets blocked.
- **Origin:** combined directive, Architecture Charter §4 replacement note.

## Q-05 — Is the Human Review Index hand-edited or generator-discovered?

- **Owner:** reviewer
- **Blocking:** no
- **Question:** `FIDO_FCB_HUMAN_REVIEW_INDEX.md` says of itself that it "is regenerated after every accepted
  checkpoint or documentation amendment" and "is not a hand-edited memory substitute," and the campaign's T-18
  rule required it to be discovery-based, never hardcoded. During the Review 100 repair I added two rows to it
  **by hand** (`FCB-A004` and `FIXED-POINT-EXTERNAL-EVIDENCE`). The rows are real open human acts and belong
  there, but either a discovery generator should be producing them or the file's self-description is
  aspirational. Which is intended?
- **Default if unanswered:** continue to hand-maintain it, and treat the self-description as aspirational rather
  than as a rule I am currently satisfying — I will not claim the index is generated.
- **Origin:** self-reported during Review 100; `FIDO_FCB_HUMAN_REVIEW_INDEX.md` preamble.
