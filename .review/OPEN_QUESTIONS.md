# Open questions — Claude Code to the reviewer and to Rob

## Q-M3-02 — BLOCKING: M3 cannot close its obligations without changing a tool it may not change

owner: **Rob** (an amendment; the reviewer may specify it)
blocks: **YES** — M3's exit condition cannot be met until this is decided
default if nobody answers: **none is available.** This is why work stopped rather than continued.

**The conflict, exactly.** M3 implements nothing by contract §1, so no obligation can name a declared code
surface; all twelve `implementation` cells are honestly `unsupported-boundary`. With every row closed,
`make claims` fails its own self-test:

```text
FAIL  a named implementation surface was renamed: could not construct the scenario
      (no closed row with a locatable declaration to rename)
```

`tools/claim-matrix-gate.py:468 rename_named_surface` needs a closed row whose first `implementation` entry
is a `.v` declaration or a Python `def`/`class`. Its precondition helper `ensure_closed_row` (`:413`) only
guarantees that *some* closed row exists, and returns early without appending `SYNTHETIC_CLOSED` — the row
written for precisely this case, whose docstring says "a documentation checkpoint legitimately has neither".
The helper covers the *builder* scenario with a `require_builder` flag; the *rename* scenario has no
equivalent.

So contract §11 (all twelve obligations closed, all gates green) and contract §9 (M3 may not change a project
tool) are jointly unsatisfiable here. The pre-commit hook runs the same self-test, so a closed matrix cannot
even be committed.

**This is not new, and I have already worked around it once.** At M2 the scenario was constructible only
because one row happened to name a Python `def` in the working-tree inventory tool — and only after that
cell was reordered during M2 Repair so the locatable entry came first. M3 is the first checkpoint where no
honest entry exists at all. I am not fabricating a third workaround.

**What I did instead:** the audit and the M4 plan are complete and committed. The twelve rows are left `open`
with cells that say where the evidence is and why the row is not closed. No Implementation Review is
requested, because requesting one with open obligations is exactly what the do-not-freeze-early rule forbids.

**Options:**

1. **Amend M3's scope to authorize one exact repair** to `tools/claim-matrix-gate.py`: give
   `ensure_closed_row` a `require_declaration` flag mirroring the existing `require_builder`, so the
   synthetic row is appended when no closed row carries a renameable declaration. Small, local, in the
   shape the function already has — and it is `M4-09` work pulled forward by necessity. My recommendation.
2. **Assign the repair to M4** and accept M3 with its obligations open, on the audit and plan as the
   evidence. Honest, but it means accepting a checkpoint whose matrix was never closed.
3. **Tell me an honest `path:symbol` I have missed.** I looked and could not find one; M3 wrote no Rocq and
   no Python.

I did not pick, because every option changes something the contract froze.

## Q-M3-01 — the readable Print-Assumptions gate costs 77 s; the stronger audit costs 1.7 s

owner: **Rob**
blocks: **no** — M3 completes and M4 Waves 1–4 proceed without an answer
default if nobody answers: **change nothing.** `gate/Assumptions.v` keeps all 539 surfaces (540 today, 539
after `M4-08`) and the cold path keeps that cost. `M4-11` stays unauthorized.

**The measurement** (`.review/M3_AUDIT.md` §3.1, two independent runs of
`make prover-log FIDO_PERF_COLD=1`):

```text
rocq c gate/Assumptions.v          77.6 s / 76.9 s     59% of the cold `prover` stage
Fido Audit Assumptions             1.72 s / 1.72 s      1%
cold `make check` total           270.0 s              so the readable gate is 29% of it
```

`gate/Assumptions.v` issues 540 `Print Assumptions` commands, each re-walking one constant's assumption
closure with no sharing between them. The Rocq-native `Fido Audit Assumptions` walks the whole certified
theory once, seeded from every constant, mutual inductive and surviving named assumption — so its guarantee
is **strictly stronger** than the readable gate's, which covers 535 distinct declared surfaces.

**The question is not whether the readable gate is redundant for the machine.** It is not needed for the
machine; the audit subsumes it. It exists so a *human* can read which named surfaces are closed. That is a
real purpose and `CLAUDE.md` makes those surfaces a standing public claim.

**Options, cheapest first:**

1. **Keep it as it is.** 77 s per `.v` edit is the price of a human-readable list. (The default.)
2. **Keep it, move it off the acceptance path.** `make prove` would run the whole-theory audit; the readable
   gate would run in `make audit-fresh` and before a checkpoint freeze. Cheap edit loop; the readable list
   still exists and is still checked, just not on every `.v` edit. Risk: a surface could rot between freezes.
3. **Shrink it to a stated rule.** Gate the public capability/mint/transport surfaces by name and let the
   whole-theory audit cover the rest. Needs the rule written down, or "which surfaces are readable" becomes
   a judgement nobody can check.
4. **Delete it.** Not recommended. The audit's output is one line; the readable gate is what makes the claim
   inspectable, and I would not trade that for 77 s without you saying so.

I did not pick. Option 2 is the one I would argue for if asked, but moving a proof gate off the acceptance
path is exactly the kind of change I should not make on my own judgement.
