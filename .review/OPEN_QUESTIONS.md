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

## Q-08 — Repair 14 left 13 surfaces with no consumer; only some are mine to delete

- **Owner:** reviewer
- **Blocking:** no — nothing is wrong with the frozen candidate's proofs; this is dead weight, not a defect in
  what the theorems claim.
- **Question:** a self-audit after the freeze found two separate residues, which I think deserve opposite
  treatment.
  **(a) Seven pre-existing surfaces the repair ORPHANED.** Deleting the reconstruction root left
  `program_elaboration_eta`, `result_ok_b`, `semantic_ok_flag`, `semantic_ok_flag_of_valid`,
  `elaboration_ok_sig`, `elaboration_result_cases` and `elaborate_failed_ds` with zero consumers. They existed
  only to lift a `pe_result` fact into the whole-elaboration equation `cp_prov` needed; once `cp_prov` went,
  the chain died. None is gated. (I restated `program_elaboration_eta` over the new record shape during the
  repair rather than deleting it — that was the wrong call, since by then its only two consumers were already
  gone.)
  **(b) Six surfaces I ADDED in repair 14 that nothing reads:** `cp_work`, `cp_trace`, `cp_layout`, `cp_plan`,
  `cp_diags` (ungated) and `pe_result_on_core` (which I gated myself, so it inflates the surface count by one).
  I added them to make the retained core's reachability concrete. No theorem, fixture or consumer uses them.
- **Default:**
  **(a) keep, and propose for the post-C4 trim.** This follows the reviewer's explicit `IndexedProgram` scope
  decision verbatim: record the exact redundancy, keep the code, propose deletion under a separate contract
  rather than enlarging repair 14's review surface. Recorded in `.review/NEXT_STEPS.md`.
  **(b) delete — but NOT unilaterally.** I have left them in place because removing them moves the frozen
  candidate `3386c02` to a sixteenth candidate in the middle of an open review, and churning the artifact under
  review is worse than disclosing its contents. Say the word and it is a small, mechanical commit.
- **Counter-argument I want checked:** A001 requires that the public queries which exist ARE projections of the
  retained core — not that new queries be invented. `cp_index`, `cp_facts` and `cp_phase` already satisfy that
  and are used, and the retention theorems prove reachability. But if the reviewer reads A001 as wanting a
  fuller published projection surface, then (b) should be RETAINED and given consumers or gate entries instead
  of deleted. That reading is defensible and I would rather be told than guess.
- **Origin:** self-audit after the repair-14 freeze, prompted by Rob asking whether this channel was being used.

## Q-07 — Note on this file's own discipline

- **Owner:** none — recorded for the reviewer's information, no action sought.
- **Blocking:** no
- **Note:** when Q-01/Q-04 were retired I used a Python `str.replace` without asserting the target matched. It
  silently no-opped, my script printed a success line anyway, and the commit found nothing to commit. Nothing
  was lost, but the failure mode is worth naming: a scripted documentation edit that cannot fail is a scripted
  edit that can silently not happen. Every edit script in this repair now asserts its target is present before
  writing.

