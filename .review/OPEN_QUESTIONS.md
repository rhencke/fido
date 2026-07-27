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

## Q-M1-01 — a dead exclusion row in `tools/naming-gate.py`

**Owner:** the reviewer. **Blocks:** no.

`EXCLUDED_FILES` still lists a C4 repair directive that no longer exists. The row is inert — the test is
`rel in EXCLUDED_FILES`, so an entry naming an absent file can never match — but nothing in the gate asserts
its own exclusions resolve, so a dead exclusion sits there looking deliberate.

Two readings of the M1 contract disagree about whose work this is. §7 says M1 deletes dead helpers and dead
files and keeps behaviour unchanged, which removing it would. §2 says M1 may not alter a checker beyond the
narrow M1 gate and the active-matrix subject, and a data row is not a comment.

**Default if nobody answers:** leave the row, and record it as an M3 finding. M3 owns tool architecture and
would in any case want the stronger fix, which is that the gate should reject an exclusion resolving to
nothing rather than carrying it silently.

## Q-M1-02 — may M1 trim the accepted checkpoints out of the campaign master plan?

**Owner:** the reviewer. **Blocks:** no.

`.review/SOURCE_FOREST_MASTER_PLAN.md` is 2,405 lines and 75 KB, the largest document under `.review/`. Most
of it is the C0 through C4 checkpoint designs, all accepted and all now described by the code they produced.
Only the C5 and C6 sections describe work that has not happened.

I have not touched it, because the document forbids exactly this in its own opening: "Do not summarize it. Do
not keep only the first checkpoint. Do not omit later checkpoints. Do not rewrite the architecture into a
shorter interpretation." M1 §7 says not to weaken a rule to shorten it, and that instruction is a rule.

Trimming the accepted sections is not what it forbids on a literal reading — it forbids dropping the *later*
checkpoints — but it is close enough that guessing seems wrong on the largest single document in scope.

**Default if nobody answers:** leave it whole, and record it as an M1 finding the freeze reports rather than
acts on.

## Q-M1-03 — the COLLECTION LAW is stated at full length in two places

**Owner:** Rob. **Blocks:** no.

`CLAUDE.md` standing technical law 10 and `ARCHITECTURE.md`'s "The law of this repository" both state the
collection law in full — roughly twenty lines each, saying the same thing in different words. Two copies of
one law is the drift shape M1 exists to remove, and §7 says to keep the more basic owner and make the other
point at it tersely.

I have not done it, for two reasons. `CLAUDE.md` calls `ARCHITECTURE.md` the binding charter, which makes the
charter the owner — but `CLAUDE.md` is the file I read first and always, so moving the law out of it has a
real operational cost that a byte count does not show. And `CLAUDE.md` is Rob's operating-law file rather
than mine to restructure.

`ARCHITECTURE.md`'s copy also carries one sentence the other does not: that this is an architectural review
law backed by audit and code inspection, not a source-scanning gate. Whichever copy survives should keep it.

**Default if nobody answers:** leave both, and record it as an M1 finding the freeze reports rather than acts
on.
