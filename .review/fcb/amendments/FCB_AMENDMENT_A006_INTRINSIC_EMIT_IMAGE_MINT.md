# FCB Amendment A006 — Intrinsic Emit.Image Mint

- **ID:** `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`
- **Status:** **ACCEPTED** — human owner Rob, token `FCB-A006-intrinsic-emit-image-mint`
- **Author:** the reviewer (primary ChatGPT Fido review thread)
- **Committer:** Claude Code (applied the amendment; authored nothing in it)
- **Date:** `2026-07-26`
- **Reviewed repository ref:** `c7377b7c0e29925e9c8a97fbefb284c3e512941d`
- **Blocked question resolved:** `.review/OPEN_QUESTIONS.md` Q-08

## New information

The certified transport must kernel-reduce `Emit.transport img`. Opaque module sealing removes the image
projection bodies and makes that reduction fail. Isolated by experiment during repair 17: with
`Module Images : IMAGE` the first witness fails with *"fido materialize: expected a directory-entries list"*;
with `Module Images <: IMAGE` — the same signature, checked, representation not hidden — the identical code
emits correctly. Rocq's `private(matching)` attribute forbids external case analysis; it does not give a
private constructor with externally reducible projections.

Therefore the FCB protects the mint AUTHORITY rather than demanding an impossible combination of a hidden
carrier representation and public kernel reduction.

## Settled rule

`Emit.Image` is a reducible carrier retaining the exact `Safe.Program`, the exact `go.mod` bytes, the exact
`.go` file map, and one opaque `Emit.Mint.Token` indexed by those same exact values. The raw token constructor
is private. `Emit.Mint.issue` is the sole authority-producing operation. The visible image pack constructor is
a reducible carrier constructor, **not** a mint: it cannot authorize foreign bytes without an inhabitant of
the indexed token type. `Emit.of_safe` is the canonical production packer; `Emit.of_safe_at` transports the
same authority along the exact source equality and is not a second mint.

No helper may accept arbitrary bytes plus an independently supplied equality or provenance proof. A postulated
token or predecessor remains outside the certified path and is rejected by the materializer's assumption-closure
guard before any filesystem effect.

## Governance decision added

**D-26 — `Emit.Image` seals authority while its transport carrier remains reducible.** (Exact text in
`FIDO_FCB_GOVERNANCE.md`.)

## Scope

Reopens **only** the `Emit.Image` bullet of Charter §24 within fixed point `ARCH-11`; every other part of that
fixed point is unchanged. Contracts affected: `SC-17`, `SC-21`, `SC-22`. No Closure Ledger row, Latitude Ledger
row, standing Spec-Closure acceptance-gate row, target/toolchain policy, or OCaml trust boundary changes.

**This is a narrow computation-boundary rule.** It does not authorize public raw constructors for
`Compilable.Core`, `Compilable.Program`, `Compilable.Failure`, `Compilable.Facts`, or `Safe.Program`. Those
capabilities remain abstract because no certified transport must reduce their representations.

C4 remains **NOT accepted**; C5, post-C4 features, the broad source cleanup and proof-module partitioning
remain forbidden.
