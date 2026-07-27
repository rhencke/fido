<!-- INSTALLER'S NOTE — Claude Code is the Committer of this directive, not its Author.

     Installed as the active C4 repair authority. Eight synthetic non-existent repository paths used as
     REPRODUCERS in sections 3 and 5 were respelled so they no longer parse as live repository path tokens
     (for example, a path under a namespace is now written as the name followed by "under" that namespace).
     Nothing else changed: no instruction, obligation, control, count or disposition was altered.

     This was forced by the directive itself. Section 5 requires controls that inject those exact literals
     into the ACTIVE REPAIR AUTHORITY and observe D-24 fail; a control proves nothing if the pristine tree
     already contains what it injects. The accepted rule is the same one this directive restates in 3.2.B —
     a live authority carries current instructions, and synthetic fixtures live in gate self-tests as
     temporary test data.

     Every exact literal is retained, once, in the control table of tools/fcb-reference-gate.py, which is the
     only place the accepted rule allows it. The unaltered directive is the uploaded review artifact.
     Recorded in .review/OPEN_QUESTIONS.md with its default; the reviewer may overrule it. -->

# C4 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 21

## Disposition

**Candidate `964575286acdb3c16df4bb9a11f1194a9418978c` is BLOCKING.**

It becomes the **twenty-second blocked C4 implementation candidate**.

Documentation freeze `d17fbe37d28a71c6f64e166409b494b30287c8b6` is not a separate candidate.

**C4 repair 21 is the sole permitted implementation task.**

C4 is not accepted. C5, M1, M2, M3, M4, post-C4 feature work, broad source cleanup, and proof-module
partitioning remain forbidden until Rob accepts C4.

Accepted Amendment A007 and Governance D-27 remain installed. Do not reinstall, weaken, or implement the
M-series during repair 21.

No new semantic architecture is authorized. This is a gate and live-authority closure repair.

---

# 1. Exact review basis

- Uploaded snapshot: `fido-main - 2026-07-26T222213.600.zip`
- Implementation candidate: `964575286acdb3c16df4bb9a11f1194a9418978c`
- Documentation freeze: `d17fbe37d28a71c6f64e166409b494b30287c8b6`
- Previous blocked candidate: `0ffdc5f7019204a868d75ef709a16fb69a9979d5`
- Active contract after this directive lands: `.review/C4_IMPLEMENTATION_REPAIR_21.md`
- Functional C4 contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`
- Accepted review basis: `.review/REVIEW_BASIS.md`

Use all code, FCB, gates, tests, and documentation from one exact ref. Do not reset or rewrite history.

---

# 2. What repair 20 got right and must not regress

Repair 20 made real progress:

1. A007 and the M-series authority were installed before implementation.
2. The naming gate moved `Local Notation` checking to statement-level parsing.
3. The D-24 manifest gained explicit corpus membership data.
4. The active repair, functional contract, and review basis entered the declared authority corpus.
5. The live FCB directory gained a stowaway-file control.
6. No Rocq source, capability topology, generated Go, or runtime meaning changed.
7. The retained `Compilable.Core`, accepted/rejected capability flow, exact source-local causes, sealed
   `Safe.Program`, and A006 image mint remain intact.
8. Generated `go.mod` and `main.go` remained byte-identical.

Keep every one of those results.

The repair-20 blocker is not that the manifest has no useful structure. The blocker is that its implementation
still defines "repository path" and "live authority set" too narrowly, so several classes of operational reference
remain invisible.

---

# 3. Blocking finding A — D-24 still proves a self-selected subset

## 3.1 Root cause

`tools/fcb-reference-gate.py` still encodes a partial repository-path grammar:

- selected directory roots are hard-coded;
- selected root files are hard-coded;
- owner paths are not required to be canonical repository-relative paths;
- repository-shaped missing paths can be mislabeled as external evidence;
- live-set completeness ignores directories and symlinked directories;
- path identity is compared as text rather than one canonical repository object;
- owner markers use substring matching;
- duplicate live-file table rows with the same role survive.

A gate which chooses which repository namespaces exist cannot prove that every operational path in the repository
is declared. Repair 20 moved authority membership into data, but the path universe remains encoded in Python.

D-24 requires the relation over the whole exact repository authority corpus, not the subset the gate happened to
recognize.

## 3.2 Independently reproduced false greens

All of the following mutations passed the repair-20 D-24 gate and must fail after repair 21.

### A. Unrecognized repository namespaces

Adding these dangling operational paths to the active repair authority did not fail:

```text
NO_SUCH_HOOK under .githooks
a NO_SUCH suffix on the root .dockerignore
NoSuchRoot.v
life.md.NO_SUCH
```

The first two expose missing dot-path coverage. The latter two expose missing root-file coverage.

### B. Existing operational files absent from the manifest

The current authority corpus names existing repository files which have no manifest row, including:

```text
.dockerignore
.editorconfig
.githooks/pre-commit
Collections.v
Compilable.v
Complex.v
Decimal.v
Emit.v
FilePath.v
Float.v
Index.v
Integer.v
ModulePath.v
Names.v
Render.v
Safe.v
Syntax.v
Typing.v
Version.v
PAINFUL_LESSONS.md
go.mod
life.md
main.go
```

Not every prose mention must become operational authority. Each occurrence must be classified. Any actual
instruction, build input, gate input, public source inventory, or required current file must have one typed row.
Non-operational prose should stop naming the path as if it were an instruction.

The gate must discover the class before a human remembers to add it.

### C. Owner path traversal

A manifest row whose owner was changed to:

```text
outside.md reached by parent traversal
```

passed when an outside file with the expected marker was created.

An owner must be one canonical regular file inside the exact repository snapshot. No absolute path, parent
traversal, fallback search, or outside-root resolution is permitted.

### D. Repository path disguised as external evidence

A row for this nonexistent path passed when typed as external evidence:

```text
NO_SUCH_EXTERNALIZED.md under .review
```

A repository-rooted path cannot be exempted from repository resolution by changing its kind or availability.
External evidence must use a separate, non-repository identity form.

### E. Undeclared live FCB subtrees

Both of these passed:

```text
EVIL.md inside a rogue subdirectory of the live FCB set
a rogue symlinked directory inside the live FCB set
```

The current live FCB set is flat. Every immediate entry must be a declared regular non-symlink file. Directories,
symlinked files, symlinked directories, sockets, and all other undeclared entries must fail.

Do not silently introduce recursive live-FCB subdirectories. That would require an explicit FCB change.

### F. Non-canonical duplicate target

Adding another row for:

```text
./ARCHITECTURE.md
```

passed although `ARCHITECTURE.md` already had a row.

Manifest paths and owner paths must use one canonical POSIX repository-relative spelling. Two strings which
resolve to one target are one path and may have only one row.

### G. Owner marker bound by substring

A DUNE marker line which named `dune-project` instead of exact path `dune` passed because the gate tested
substring containment.

The owner marker must bind the exact canonical path token. `dune` is not present merely because
`dune-project` contains those characters.

### H. Duplicate live-file table row

A second `INDEX.md | authority` row in the FCB Index passed when it omitted the owner marker.

The live-file table may contain each path exactly once. Same-role duplicates are still duplicates.

---

# 4. Required D-24 repository-path model

Fix the root abstraction. Do not add more names to another allowlist.

## 4.1 One canonical repository path parser

Define one internal path type or one checked parser used for:

- manifest target paths;
- manifest owner paths;
- authority-corpus membership;
- live-file table paths;
- operational paths found in authority text;
- duplicate-target checks.

A repository path is valid only when all of these hold:

1. UTF-8 text.
2. POSIX separators.
3. Relative to repository root.
4. No leading slash.
5. No leading `./` in stored form.
6. No empty segment.
7. No `.` segment.
8. No `..` segment.
9. No backslash.
10. No NUL.
11. The supplied text equals its canonical normalized spelling.
12. It resolves inside the exact review root.
13. Its resolved target is not reached through a symlink when a regular repository file is required.

Reject malformed paths. Do not normalize bad input and accept it.

Owner paths use the same parser and must resolve to one readable regular file in the exact tree.

## 4.2 Derive the repository inventory from the exact snapshot

The gate must obtain the repository file inventory from the exact mode it is checking:

- **working-tree mode:** tracked files plus untracked nonignored files, fail closed if Git enumeration fails;
- **staged-snapshot mode:** the exported staged tree, with no dependency on the caller's working tree;
- **plain exported snapshot mode:** recursive inventory of the supplied root, excluding only named build residue
  which cannot be part of a committed snapshot.

Do not hard-code the set of repository top-level directories or root files.

Use the inventory to derive:

- all current top-level namespaces;
- all exact current repository paths;
- all candidate exact path tokens which authority prose can name.

## 4.3 Discover operational references in both directions

The gate must prove all directions:

### Manifest to repository

Every repository row:

- has a canonical target path;
- resolves to the correct target kind;
- has one canonical in-repository owner;
- has one exact owner marker on the same line as the exact path token;
- has one valid corpus role.

### Repository authority to manifest

Every operational repository path named anywhere in every authority document:

- has exactly one manifest row;
- uses the canonical target spelling;
- has the correct role and target kind.

At minimum, discovery must include:

1. Exact existing repository paths from the derived repository inventory.
2. Missing paths beginning with any dynamically discovered top-level directory.
3. Missing dot-prefixed repository paths.
4. Explicit root-relative missing paths, written with a dot-slash prefix.
5. Any explicit `repo:path` operational reference form adopted by the corpus.

For root-level missing references, require the authority corpus to use a dot-slash prefix on the file name, or a repo-colon prefix; normalize only for
lookup, not for manifest storage. Add this syntax rule to D-24 implementation prose so a missing root path cannot
be indistinguishable from an ordinary word.

Do not treat every slash-containing phrase as a path. The rule must be exact and tested.

## 4.4 Keep external evidence in a distinct namespace

External evidence rows must not use a repository path identity.

Use a clear external identity form, such as a URI, content digest identity, or an explicit `external:` key.
Whatever exact form is retained:

- it cannot parse as a repository path;
- it cannot begin with a current repository top-level namespace;
- it cannot resolve under the repository root;
- changing a repository path row to `external-evidence` cannot make a missing repository file pass.

Do not move current repository obligations to external evidence to close the gate.

## 4.5 Compare target identity, not unchecked strings

Reject:

- `./ARCHITECTURE.md`;
- `a//b`;
- `a/./b`;
- `a/../b`;
- backslash spellings;
- two rows which resolve to one file;
- owner aliases which resolve to one owner under two names.

One canonical target has one row.

## 4.6 Bind markers to exact path tokens

The marker line must contain the exact canonical path as a delimited token.

A boundary-safe check is acceptable. A structured marker field is also acceptable.

These must differ:

```text
dune
dune-project
```

The first is not proved by the second.

The marker itself remains unique by row ID, and the row's exact path must occur on that same line.

## 4.7 Make the live FCB set closed

For `.review/fcb/current/`:

- every immediate entry is inspected;
- every entry must be a regular non-symlink file;
- every file appears exactly once in the FCB Index live-file table;
- every file has exactly one authority manifest row;
- every table row has exactly one corresponding file;
- duplicate table paths fail even when their roles agree;
- undeclared files, directories, symlinks, and special entries fail.

If a future amendment wants subdirectories, it must define their role and update this law first.

---

# 5. Required D-24 permanent controls

Add controls which exercise the actual production functions and fail for the exact expected reason.

At minimum:

1. Active repair authority contains `NO_SUCH_HOOK under .githooks`.
2. Active repair authority contains `a NO_SUCH suffix on the root .dockerignore`.
3. Active repair authority contains `NO_SUCH_ROOT.v in the root-relative dot-slash form`.
4. An existing unmanifested root `.v` file is named by authority.
5. An existing unmanifested dotfile is named by authority.
6. Manifest owner is `outside.md reached by parent traversal`.
7. Manifest owner is absolute.
8. Repository path `NO_SUCH.md under .review` is labeled external evidence.
9. External evidence resolves inside the repository.
10. Live FCB contains an undeclared regular file.
11. Live FCB contains an undeclared directory.
12. Live FCB contains a symlinked directory.
13. Manifest contains `./ARCHITECTURE.md`.
14. Two rows resolve to the same target.
15. Owner marker names `dune-project` for the `dune` row.
16. FCB Index repeats one path with the same role.
17. FCB Index repeats one path with a different role.
18. A new authority row is added and its dangling path is scanned without Python source changes.
19. A clean external-evidence row remains accepted.
20. A clean root-file row remains accepted.

Each negative control must pin its failure class. An unrelated parse or missing-file failure does not satisfy a
specific control.

Mutation-test the root helpers by disabling:

- repository inventory derivation;
- path canonicality;
- owner-root containment;
- external/repository separation;
- live-directory entry-kind checking;
- exact marker token matching;
- duplicate target identity checking;
- duplicate Index table checking.

The controls must fail when their protecting rule is removed.

No control may skip and still count as passed.

---

# 6. Blocking finding B — current human-act data contradicts the offered candidate

The canonical Human Acts row still says no candidate is offered and names the prior `0ffdc5f...` state, while
`NEXT_STEPS.md` and `REVIEW_REQUEST.md` offer `964575...` for review.

This violates the repository's own current-state ownership rule.

## Required fix

`NEXT_STEPS.md` alone owns mutable candidate identity and checkpoint state.

Rewrite the canonical C4 human-act row to state only the durable human act, equivalent to:

> Review the exact C4 candidate named by `.review/NEXT_STEPS.md`; accept or block it. Only Rob accepts C4.

Its effect remains:

> Until Rob accepts C4, C5 and M1-M4 implementation remain forbidden.

Do not copy a candidate SHA, ordinal, repair number, or "no candidate is offered" state into
`FIDO_FCB_HUMAN_ACTS.tsv`.

Regenerate `FIDO_FCB_HUMAN_REVIEW_INDEX.md` from the canonical row.

Add a fail-closed generator rule that open human-act data may not carry a Git object ID as mutable candidate
state. The owning authority path may be named; the candidate value stays in `NEXT_STEPS.md`.

Classify any legitimate non-candidate digest use before applying the rule. Do not block content digests or
toolchain hashes by an overbroad pattern.

---

# 7. Current-state and authority updates

Install this directive as:

```text
.review/C4_IMPLEMENTATION_REPAIR_21.md
```

Retire Repair 20 authority to Git history. Do not retain two active repair directives.

Update, from one exact ref:

- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_REQUEST.md`;
- `.review/OPEN_QUESTIONS.md`;
- `.review/fcb/current/FIDO_FCB_INDEX.md`;
- `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv`;
- generated `.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md`;
- `.review/fcb/current/FIDO_FCB_REFERENCES.tsv`;
- any D-24 implementation prose changed by canonical root-reference syntax;
- Repair 21 obligation matrix;
- Repair 21 closure audit.

The current state after the authority commit is:

- `964575286acdb3c16df4bb9a11f1194a9418978c` is BLOCKING;
- it is the twenty-second blocked C4 implementation candidate;
- `d17fbe37d28a71c6f64e166409b494b30287c8b6` is its documentation-only freeze;
- Repair 21 is the sole active C4 task;
- C4 is not accepted;
- A001 through A007 remain accepted;
- Governance owns D-01 through D-27;
- A007 M1-M4 remain installed but forbidden before C4 acceptance;
- no C5 or M-series implementation has begun.

No new FCB amendment is needed. Repair 21 implements the already accepted D-24 and D-07 laws. If the governing
law truly prevents the required correct design, stop and report the exact conflict for reviewer-authored
amendment. Do not weaken the law yourself.

---

# 8. What must remain untouched

Do not change unless a direct repair-21 gate dependency requires it and the conflict is reported first:

- `Compilable.Core` representation or public queries;
- accepted/rejected capability topology;
- source-local causal theorem statements;
- `Safe.Program` seal;
- A006 `Emit.Mint.Token`;
- `Emit.Image` carrier topology;
- renderer behavior;
- extraction design;
- OCaml materializer role;
- generated Go bytes;
- supported or rejected program sets;
- diagnostic meaning or order;
- C5 design;
- M1-M4 implementation.

This repair is expected to be Python, manifest, generated FCB view, and current-authority work.

---

# 9. Required whole-system verification

Before freezing the next candidate, run and record:

1. `make names`
2. naming gate working-tree mode
3. naming gate staged-snapshot mode
4. all naming controls and mutation controls
5. `make fcb`
6. all Human Acts controls
7. all D-24 controls and mutation controls
8. live FCB directory closure controls
9. `make claims`
10. closure ledger checks
11. `make prove`
12. whole-theory assumption audit
13. sealed-constructor controls
14. image-mint controls
15. extraction and plugin build
16. OCaml-origin gate
17. `make e2e`
18. generated-output gate
19. generated byte comparison
20. `make regenerate`
21. `make regen-guard`
22. `make fmt`
23. staged exported snapshot through the real hook without `--no-verify`
24. one forced-fresh proof/e2e run rather than only cached verdicts

The closure audit must list:

- exact repository inventory count;
- exact authority count;
- exact manifest row count;
- exact live FCB file count;
- every newly added manifest row;
- every removed false operational reference;
- every negative control and expected reason;
- mutation-test result for each root helper;
- zero mutable candidate SHAs in Human Acts data;
- generated file hashes;
- exact candidate commit.

A green build without the classified counts and adversarial results is not a completion report.

---

# 10. Claim-to-gate matrix

Create `.review/C4_REPAIR_21_OBLIGATION_MATRIX.tsv`.

Each row must include:

```text
obligation_id
claim
owning_authority
implementation
positive_evidence
negative_control
mutation_control
gate
status
```

At minimum include separate rows for:

- R21-D24-CANONICAL-PATH
- R21-D24-INVENTORY
- R21-D24-AUTHORITY-DISCOVERY
- R21-D24-OWNER-CONTAINMENT
- R21-D24-EXTERNAL-SEPARATION
- R21-D24-TARGET-IDENTITY
- R21-D24-EXACT-MARKER
- R21-D24-LIVE-SET
- R21-D24-INDEX-UNIQUENESS
- R21-D07-STATE-OWNERSHIP
- R21-A007-NO-EARLY-IMPLEMENTATION
- R21-GENERATED-BYTES

The claim matrix gate must refuse `requested` review state while any row is absent, duplicate, malformed, open, or
unsupported by its named controls.

Do not let the matrix itself become authority. It is a checked map from accepted obligations to evidence.

---

# 11. Definition of done

Repair 21 is complete only when:

- the D-24 gate derives repository namespaces and exact paths from the exact snapshot;
- no repository namespace is hard-coded as the completeness boundary;
- manifest and owner paths are canonical repository-relative paths;
- owner traversal and outside-root resolution fail;
- repository-shaped missing paths cannot be externalized;
- external evidence uses a separate identity form;
- every operational current repository path has exactly one row;
- every authority is scanned because of data, not Python source edits;
- exact target identity prevents spelling aliases;
- owner markers bind exact path tokens;
- the live FCB directory contains only declared regular files;
- duplicate FCB Index rows always fail;
- all required D-24 controls and mutation controls pass;
- the canonical C4 human act contains no mutable candidate state;
- the generated Human Review Index exactly matches canonical Human Acts data;
- all current authorities state one truth;
- A007 remains installed and unimplemented;
- no Rocq semantic or generated-byte change occurred unless an explicit conflict was first reported;
- full proof, audit, extraction, Docker, OCaml, e2e, regeneration, format, and staged gates are green;
- generated `go.mod` and `.go` files remain byte-identical;
- the candidate is frozen and offered for human review;
- Claude notifies Rob.

---

# 12. Required execution loop

Use:

```text
/loop 3m
```

Continue implementing, attacking, checking, and correcting until all obligations above are complete or a real
contract conflict blocks progress.

Do not stop for:

- routine progress;
- a green intermediate test;
- one fixed mutation while another remains;
- a documentation-only freeze before all controls pass;
- a cached proof or e2e verdict without the required forced-fresh audit;
- a claim that the gate is complete without mutation evidence.

When complete or genuinely blocked, use the notification tool to notify Rob.

If blocked, report:

- exact failed obligation ID;
- smallest reproducer;
- exact code path;
- exact accepted FCB law involved;
- why the required root design cannot satisfy it;
- the precise human decision needed.

Do not invent a weaker path grammar, external-evidence escape, allowlist, or compatibility mode.
