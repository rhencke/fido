# Fido FCB Roadmap

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


The selection rule is strict: choose the lowest-numbered checkpoint whose dependencies are accepted. Do not move a feature earlier because it is interesting. Every row below has one **primary closure checkpoint**: the checkpoint that must make its current admitted meaning, proof surface, fixtures, and production integration complete. Umbrella rows may gain later cases only through the same owner and contract; they are not reassigned. Cross-cutting contracts still apply where cited by the ledger.

## Current boundary

C4 implementation candidate `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` is **BLOCKING** — the eighteenth blocked candidate; `c8ce2d8c6ad1c109c08c44b689b70abbb408ed7a` is its documentation-only freeze, not a separate candidate. FCB Amendments A001 and A005 are accepted. **C4 repair 17 is the sole active C4 work** (`.review/C4_IMPLEMENTATION_REPAIR_17.md`): the returned-object fixtures must carry the retained causal history, the naming gate must stop being false-green for record fields and unreadable text, `Emit.Image` construction must be sealed under Charter §22, the coarse legacy result peer must be deleted, and the corpus must state one truth. Repairs 13 through 16 are historical; none of them is the active work. Accepted amendment `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT` (Governance `D-26`) settles the `Emit.Image` authority boundary that repair 17 must implement: an opaque value-indexed `Emit.Mint.Token` owns the authority while the transport carrier stays reducible. C5 remains dependent on C4 acceptance and is unchanged by A006.

The out-of-band documentation, header and tooling commits after the blocked candidate are not new

FCB Amendment A002 is accepted: the live FCB is Git-canonical under `.review/fcb/current/`; project libraries contain bootstrap shims only. This changes no checkpoint assignment or dependency.

The next permitted sequence is:

`C4 repair 17 → human C4 review → checkpoint-definition Step 0 → C5`.

C5 remains forbidden until C4 is accepted.

## C5 — Machine base

**Dependency:** Accepted C4 opaque static capability retaining the exact successful whole-elaboration object by construction, with total fact/layout/plan queries as projections and no rerun-based provenance.  
**Contracts:** SC-00, SC-01, SC-16, SC-18, SC-21

Freeze the one public `Machine` base, opaque state, starts, labels, results, finite/infinite runs, absorbing final states, and the theorem surface required by later checkpoints. Also carry the already-built source/index/render foundation into the FCB as one sealed prerequisite: C5 audits its lexical and token rows but adds no parser and no second source form. No feature-specific second evaluator.

**Primary closure rows (106):**

```text
GRAM-001–GRAM-018, KEY-01–KEY-25, OP-01–OP-48, SPEC-001–SPEC-006, SPEC-008–SPEC-012, SPEC-144, SPEC-149, SPEC-150, SPEC-159
```

**Latitude rows (5):**

```text
LAT-004–LAT-007, LAT-187
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C6 — Names, slots, places, and first acceptance gates

**Dependency:** C5 accepted.  
**Contracts:** SC-02, SC-03, SC-04, SC-05, SC-08, SC-14, SC-21, SC-22

Land exact binding/use roles, static slots, dynamic places, basic closed runtime values, the first object-store slice, and the expression/use fact boundary needed by constants and variables. Discharge constant-bound and unused-local rejection.

**Primary closure rows (66):**

```text
GRAM-046, GRAM-047, GRAM-050, GRAM-077, GRAM-079–GRAM-088, GRAM-093–GRAM-095, PRE-02, PRE-03, PRE-05, PRE-06, PRE-08–PRE-21, PRE-23–PRE-26, SPEC-019–SPEC-023, SPEC-036–SPEC-041, SPEC-043–SPEC-054, SPEC-058, SPEC-059, SPEC-140, SPEC-X004
```

**Latitude rows (23):**

```text
LAT-022–LAT-028, LAT-059–LAT-070, LAT-077–LAT-079, LAT-X004
```

**Acceptance gates:** `LAT-019, LAT-077`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C7 — Runtime expressions, evaluation order, output, and fatal panic

**Dependency:** C6 accepted.  
**Contracts:** SC-01, SC-02, SC-03, SC-05, SC-08, SC-13, SC-15, SC-17, SC-20, SC-21, SC-22

Implement ordinary expression stepping, exact constants, operator behavior, specified and unspecified evaluation order, output actions, runtime expression faults, and terminal panic observation without yet adding user-function stack behavior.

**Primary closure rows (73):**

```text
GRAM-019–GRAM-043, GRAM-045, GRAM-101–GRAM-104, GRAM-115, GRAM-123–GRAM-130, PRE-31, PRE-34, PRE-37, PRE-38, PRE-41–PRE-43, SPEC-013–SPEC-018, SPEC-062, SPEC-063, SPEC-067, SPEC-081–SPEC-089, SPEC-092, SPEC-093, SPEC-096, SPEC-097, SPEC-122, SPEC-126, SPEC-130, SPEC-133, SPEC-X005
```

**Latitude rows (42):**

```text
LAT-008–LAT-014, LAT-016–LAT-021, LAT-082–LAT-085, LAT-115–LAT-123, LAT-125–LAT-128, LAT-131–LAT-137, LAT-174–LAT-177, LAT-198
```

**Acceptance gates:** `LAT-177`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C8 — Control flow and retained jump continuations

**Dependency:** C7 accepted.  
**Contracts:** SC-03, SC-06, SC-18, SC-21, SC-22

Implement the source zipper for statements, assignment, conditionals, switches, loops, labels, break, continue, goto, and fallthrough. Jump rules consume retained continuations and never recompute them.

**Primary closure rows (41):**

```text
GRAM-078, GRAM-131–GRAM-136, GRAM-139–GRAM-146, GRAM-151–GRAM-155, GRAM-164–GRAM-167, SPEC-098–SPEC-102, SPEC-104–SPEC-108, SPEC-110–SPEC-112, SPEC-117–SPEC-120
```

**Latitude rows (16):**

```text
LAT-138–LAT-148, LAT-154–LAT-157, LAT-172
```

**Acceptance gates:** `LAT-148`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C9 — Functions, closures, multi-results, defer, panic, and recover

**Dependency:** C8 accepted.  
**Contracts:** SC-03, SC-04, SC-05, SC-06, SC-07, SC-09, SC-15, SC-16, SC-17, SC-20, SC-21, SC-22

Implement activations, calls, results, closure capture, defer registration, stack-only panic/recover, nested panic replacement, and named-result behavior.

**Primary closure rows (24):**

```text
GRAM-061–GRAM-066, GRAM-096–GRAM-098, GRAM-114, GRAM-120, GRAM-163, GRAM-168, PRE-40, PRE-44, SPEC-028, SPEC-060, SPEC-066, SPEC-076, SPEC-077, SPEC-116, SPEC-121, SPEC-132, SPEC-145
```

**Latitude rows (15):**

```text
LAT-041–LAT-043, LAT-080, LAT-091, LAT-101, LAT-102, LAT-167–LAT-171, LAT-173, LAT-188, LAT-189
```

**Acceptance gates:** `LAT-171`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C10 — Composite data and typed mutable objects

**Dependency:** C9 accepted.  
**Contracts:** SC-03, SC-04, SC-05, SC-08, SC-10, SC-11, SC-15, SC-20, SC-21

Implement arrays, structs, pointers, slices, maps, composite literals, indexing, slicing, conversions, allocation, aliasing, and composite-data builtins over one typed object store.

**Primary closure rows (49):**

```text
GRAM-051–GRAM-060, GRAM-074, GRAM-075, GRAM-106–GRAM-113, GRAM-117, GRAM-118, PRE-27–PRE-29, PRE-32, PRE-33, PRE-35, PRE-36, PRE-39, SPEC-024–SPEC-027, SPEC-034, SPEC-065, SPEC-071–SPEC-074, SPEC-090, SPEC-094, SPEC-095, SPEC-123, SPEC-124, SPEC-127–SPEC-129, SPEC-131
```

**Latitude rows (28):**

```text
LAT-029–LAT-040, LAT-053–LAT-055, LAT-086–LAT-090, LAT-097–LAT-100, LAT-124, LAT-129, LAT-130, LAT-X001
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C11 — Packages, initialization, starts, and range

**Dependency:** C10 accepted.  
**Contracts:** SC-02, SC-05, SC-06, SC-07, SC-10, SC-11, SC-14, SC-16, SC-17, SC-20, SC-21

Implement closed-world package/import facts, proof-carrying initialization order, exact starts, module boundaries, range over supported domains, iterator-function range, and map-order nondeterminism.

**Primary closure rows (26):**

```text
BOUND-001, BOUND-002, BOUND-X007, GRAM-105, GRAM-156, GRAM-169–GRAM-174, SPEC-064, SPEC-113, SPEC-134–SPEC-139, SPEC-141–SPEC-143, SPEC-X006, SPEC-X008–SPEC-X010
```

**Latitude rows (13):**

```text
LAT-158–LAT-163, LAT-178, LAT-179, LAT-182–LAT-186
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C12 — Methods and interfaces

**Dependency:** C11 accepted.  
**Contracts:** SC-03, SC-04, SC-05, SC-06, SC-07, SC-13, SC-21, SC-22

Implement method declarations and sets, selectors, method expressions and values, interface packing, typed nil, assertions, dispatch, and interface equality from one retained fact authority.

**Primary closure rows (28):**

```text
GRAM-067–GRAM-070, GRAM-099, GRAM-100, GRAM-116, GRAM-119, GRAM-121, GRAM-122, GRAM-147–GRAM-150, PRE-01, PRE-07, SPEC-029–SPEC-033, SPEC-042, SPEC-061, SPEC-068–SPEC-070, SPEC-075, SPEC-109
```

**Latitude rows (20):**

```text
LAT-044–LAT-052, LAT-081, LAT-092–LAT-096, LAT-149–LAT-153
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C13 — Generics and closing substitution

**Dependency:** C12 accepted.  
**Contracts:** SC-03, SC-04, SC-05, SC-13, SC-21, SC-22

Implement type parameters, constraints, instantiation, inference, unification, and the proof that open implementation facts survive closing substitution and drive runtime dispatch.

**Primary closure rows (17):**

```text
GRAM-048, GRAM-049, GRAM-071–GRAM-073, GRAM-089–GRAM-092, PRE-04, SPEC-055–SPEC-057, SPEC-078–SPEC-080, SPEC-160
```

**Latitude rows (20):**

```text
LAT-071–LAT-076, LAT-103–LAT-114, LAT-211, LAT-212
```

**Acceptance gates:** `LAT-049, LAT-085`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C14 — Goroutines, channels, select, and enabledness

**Dependency:** C13 accepted.  
**Contracts:** SC-03, SC-04, SC-05, SC-06, SC-08, SC-10, SC-15, SC-18, SC-20, SC-21

Implement goroutine stacks, send/receive/select, channel state, close, resource-local communication origins, scheduler choice, and constructive enabledness without a scheduler object.

**Primary closure rows (16):**

```text
GRAM-076, GRAM-137, GRAM-138, GRAM-157–GRAM-162, PRE-30, SPEC-035, SPEC-091, SPEC-103, SPEC-114, SPEC-115, SPEC-125
```

**Latitude rows (8):**

```text
LAT-056–LAT-058, LAT-164–LAT-166, LAT-X002, LAT-X003
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C15 — Happens-before, races, and deadlock

**Dependency:** C14 accepted.  
**Contracts:** SC-12, SC-16, SC-18, SC-20, SC-21

Derive event graphs from the one step relation; prove all named channel edges, race detection, finite bad-prefix safety, and exact deadlock classification. Keep racy-run latitude in the model without race history in state.

**Primary closure rows (12):**

```text
MEM-001–MEM-008, MEM-010, MEM-016–MEM-018
```

**Latitude rows (11):**

```text
LAT-214–LAT-220, LAT-224–LAT-227
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C16 — Platform matrix and target model

**Dependency:** C15 accepted.  
**Contracts:** SC-00, SC-17, SC-19, SC-21

Disposition ADR-0004, reopen ADR-0001, and either generalize the target descriptor or reaffirm the single target with exact prices. Add only targets with pinned distributions, profiles, ledger updates, and proof-impact review.

**Primary closure rows (1):**

```text
BOUND-003
```

**Latitude rows (0):**

```text
(none)
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## C17 — Ruthless trim and final authority audit

**Dependency:** C16 accepted.  
**Contracts:** SC-19, SC-21

Delete every superseded special form, wrapper, raw evaluator, duplicate fact path, unused theorem surface, and proof-hostile internal form. Recheck all 459 IN rows, all 32 priced OUT rows, all latitude dispositions, and every fixed point. No new public feature enters.

**Primary closure rows (0):**

```text
(none)
```

**Latitude rows (0):**

```text
(none)
```

**Acceptance gates:** `none`

**Exit condition:** All frozen public additions and theorem statements pass the checkpoint contract; production uses only the new path; paired fixtures and replay gates pass; Rob accepts; affected FCB files regenerate, verify, and commit under `.review/fcb/current/`.

## Priced exclusions

The following 32 closure rows remain `OUT`. They are not assigned to an implementation checkpoint. Their inclusion price is authoritative in the Closure Ledger.

```text
BOUND-X001–BOUND-X006, BOUND-X008, BOUND-X009, GRAM-044, MEM-009, MEM-011–MEM-015, PRE-22, SPEC-007, SPEC-146–SPEC-148, SPEC-151–SPEC-158, SPEC-X001–SPEC-X003, SPEC-X007
```

The following 30 latitude rows are wholly owned by priced `OUT` closure rows and therefore have no implementation checkpoint.

```text
LAT-001–LAT-003, LAT-015, LAT-180, LAT-181, LAT-190–LAT-197, LAT-199–LAT-210, LAT-213, LAT-221–LAT-223
```

## Coverage check

- `IN` closure rows assigned once: **459 / 459**.
- `OUT` closure rows kept priced: **32 / 32**.
- Latitude rows assigned to a primary checkpoint or priced OUT: **231 / 231**.
- Acceptance gates assigned: **7 / 7**.
