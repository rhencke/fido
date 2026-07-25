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

## Q-07 — Note on this file's own discipline

- **Owner:** none — recorded for the reviewer's information, no action sought.
- **Blocking:** no
- **Note:** when Q-01/Q-04 were retired I used a Python `str.replace` without asserting the target matched. It
  silently no-opped, my script printed a success line anyway, and the commit found nothing to commit. Nothing
  was lost, but the failure mode is worth naming: a scripted documentation edit that cannot fail is a scripted
  edit that can silently not happen. Every edit script in this repair now asserts its target is present before
  writing.

