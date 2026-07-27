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

Q-07 was retired into the implementer operating law in root `CLAUDE.md`; Q-08 was resolved by accepted
amendment `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`. Git history is the archive for both.

---

### Q-09 — the repair-21 directive's own reproducers could not stay verbatim (reviewer; non-blocking)

**Owner:** the reviewer. **Blocks:** no. **Default taken:** respell, and say so where a reader will see it.

The repair-21 directive quotes eight synthetic non-existent repository paths as reproducers, and separately
requires controls that inject those same literals into the ACTIVE REPAIR AUTHORITY and observe D-24 fail. Both
cannot hold: a control proves nothing if the pristine tree already contains what it injects, and the accepted
rule — repair-20 §4.6, restated in repair-21 §3.2.B — says a live authority carries current instructions while
synthetic fixtures live in gate self-tests as temporary test data.

I installed the directive with those eight spellings changed so they no longer parse as live path tokens, and
nothing else altered. The installer's note at the top of the directive says exactly that; the exact literals
are retained once, in the D-24 gate's control table, which is where the accepted rule puts them.

If the reviewer prefers a different resolution — a separate non-authority record of the verbatim text, or a
declared fixture namespace — say so and I will apply it. I did not invent an exemption list or a weaker path
grammar, both of which §12 forbids.
