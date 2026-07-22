# ADR-0001 — Pinned 64-bit target (linux/amd64, Go 1.23)

- **Status:** PROPOSED — pending Rob's review with the C4 candidate. (Not accepted until Rob accepts it.)
- **Date:** 2026-07-22.
- **Scope ledger link:** `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` SR-001.
- **Charter link:** `ARCHITECTURE.md` (ModuleSpec is NOT a TargetConfig); `CLAUDE.md` Standing law §8.

## The restriction, stated directly

Fido pins one exact operational validation target — **linux/amd64, Go 1.23** — and models `int`/`uint` as
concrete 64-bit types. This ADR faces that head-on and separates what is *assumed*, what is *validated*, and
what is *not claimed*. It deliberately says **linux/amd64**, not "64-bit systems": the operational target is
one OS and one architecture, not a portability class.

### 1. Semantic language / constant assumption

- Go language version **1.23**.
- In `Ints`, `int` and `uint` have **64-bit** ranges.
- `int` remains **type-distinct** from `int64`.
- `uint` remains **type-distinct** from `uint64`.

These are semantic facts of the modelled language at the pinned version — `int`/`uint` are their own types
(distinct identity, distinct rendering, distinct conversion behaviour) that happen to carry 64-bit ranges.

### 2. Operational end-to-end validation target

- `GOOS=linux`.
- `GOARCH=amd64`.
- The digest-pinned `golang:1.23-alpine` image.
- Rendered `go.mod` language version `1.23`.

This is the single target against which `GoCompile == go build` is differentially exercised.

### 3. Claims NOT made

- **No** general ABI / memory-layout theorem.
- **No** pointer-size theorem — there is no `uintptr`/pointer in the fragment yet, so pointer width is not a
  claim.
- **No** portability claim across 64-bit architectures (amd64 is the only validated arch; arm64 etc. are not).
- **No** 32-bit claim of any kind.
- **No** claim that all linux/amd64 platform resource limits (filesystem/name/space) are modelled — see
  SR-002.

## Decision analysis

### Why one exact deployment/validation target now

The core project claim is `GoCompile == go build ./...` as an EXACT, differentially-tested property. "Exact"
is only meaningful against a specific toolchain: acceptance, integer-range diagnostics, and rendered `go.mod`
semantics are all pinned to one `cmd/go`. One target makes that claim reproducible and falsifiable; a family
of targets would either dilute the claim to a lowest common denominator or multiply the differential surface
before any consumer needs it.

### Why this is a theorem-domain boundary, not avoidance of hard work

`int`/`uint` at 64 bits is a *choice of the domain over which the theorems are stated*, not a shortcut inside
them. Every integer theorem (range well-formedness, conversion, value denotation, render round-trip) is
proven in full for the concrete widths. Nothing is admitted, approximated, or left `Admitted` on account of
the pin. Widening the domain later is additive (a new target dimension), not a repair of something skipped.

### Why target-parametric int/uint would add a real cross-cutting abstraction now

Making `int`/`uint` width a parameter means threading a target descriptor through `Ints`, every
`ConstInfo`/`convert_const` step, every `VInteger` value, `ValueWF`, and every render/denotation proof — a
descriptor that would appear in dozens of statements whose ONLY current use would be a portability claim Fido
does not make. That is a genuine abstraction with a real proof cost and, today, no consumer. The pin avoids
paying that cost before it buys anything (consistent with "cut representable scope before weakening a proof,"
and with taking the more-correct path only when it earns its keep).

### Which current definitions / proofs / tests depend on 64-bit int/uint

- **Definitions:** `Ints.v` — the ten-member `IntegerType` with `int`/`uint` fixed at the 64-bit
  min/max ranges, kept type-distinct from `int64`/`uint64`.
- **Proofs:** the integer range-well-formedness and conversion/denotation theorems over those ranges; the
  render/decoder round-trips for `int`/`uint` literals and conversions.
- **Tests:** the e2e out-of-range / wrong-type rejection fixtures and the multi-package differential, which
  assume 64-bit `int`/`uint` bounds when checking what `go build` accepts/rejects; the Dockerfile's explicit
  `GOOS`/`GOARCH` assertions.

### What valid Go programs / deployment targets are excluded

- Building/running the generated module on 32-bit targets, on arm64 or other architectures, or on non-linux
  operating systems is outside the validated envelope (the generated Go text is not itself arch-specific, but
  no claim is made about it there).

### Alternatives considered

1. **32-bit only.** Rejected: 64-bit is the mainstream server/CI target and the pinned image's native word
   size; choosing 32-bit would exclude the common case for no benefit.
2. **Target-parameterized semantics** (a target descriptor parameterizing `int`/`uint`). Rejected *for now*:
   real cross-cutting proof cost (above) with no current consumer; revisit when a portability claim or
   pointer/layout work needs it.
3. **Separate per-target theories** (a whole theory per target). Rejected: massive duplication, and it
   multiplies the differential/e2e surface without a driving requirement.
4. **Architecture-independent subset with no int/uint boundary dependence** (avoid `int`/`uint`, use only
   fixed-width types). Rejected: `int`/`uint` are core Go types whose exact modelling (including their
   distinctness from `int64`/`uint64`) is part of faithful coverage; dropping them would make the model less
   faithful, not more portable.

### Why the chosen option is presently better

It yields an exact, reproducible, falsifiable `GoCompile == go build` claim and concrete, fully-proven
`int`/`uint` semantics, with zero premature abstraction — while leaving every widening path open as an
additive future step under its own review.

## Enforcement

- **`Ints` definitions/theorems:** `int`/`uint` = 64-bit ranges, distinct from `int64`/`uint64`.
- **Makefile sealed platform:** the header pins the build platform to linux/amd64 as the 64-bit target the
  theory assumes (an operational pin, explicitly NOT a certified `TargetConfig`).
- **Docker GOOS/GOARCH environment and checks:** the go-e2e stage exports `GOOS=linux GOARCH=amd64` and then
  ASSERTS them (`[ "$goos" = linux ]`, `[ "$goarch" = amd64 ]`, failing the build otherwise), and prints the
  operational pin banner.
- **Digest pin:** `golang:1.23-alpine@sha256:…` fixes the exact toolchain image.
- **e2e boundary witnesses:** the out-of-range/wrong-type rejection fixtures and the whole-tree
  `go build ./...` differential.

## Gap between comments and actual enforcement

None known. The Makefile/`ARCHITECTURE.md` prose describes the pin as an operational restriction (not a
certified `TargetConfig`), and the Dockerfile actually asserts `GOOS`/`GOARCH` and pins the image digest — the
enforcement matches the stated claim. `int`/`uint` widths are enforced in `Ints` itself, not only in prose.
If a future edit relaxes the Docker `GOOS`/`GOARCH` assertions or the digest pin without updating this ADR and
SR-001, that would open a comment-vs-enforcement gap to catch.

## Reconsideration triggers

- A request to support 32-bit.
- A request to support arm64 or another OS.
- Any portable-Go public claim.
- `uintptr`/pointer/layout work that needs a richer target model.
- A toolchain/target image change.
- A proof benefit from a target descriptor that exceeds its cost.
