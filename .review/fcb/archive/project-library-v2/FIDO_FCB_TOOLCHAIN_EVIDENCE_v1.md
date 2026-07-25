# Fido FCB Toolchain Evidence v1

> **Derived reference, not authority.** The code and its gated theorems are the sole authority.  
> **FCB version:** `v1` · **Generated:** `2026-07-24`  
> **Repository basis:** `rhencke/fido@9d5246eedf9e9a3c019b85e9dc65ce9e6f867179` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> Regenerate this document at each checkpoint acceptance. Delete every stale copy from every model library.  
> This library does not accept C4 or authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


This document owns external adequacy evidence only. It does not define Go meaning and does not prove the real Go compiler correct.

## 1. Evidence status

- **Pinned executor report:** `go version go1.23.2 linux/amd64`.
- **Target profile:** `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1`, `CGO_ENABLED=0`.
- **Terminal evidence status:** `PASS-WITH-PENDING-PROVENANCE`.
- **Reason:** the official `go1.23.2.linux-amd64.tar.gz` bytes were not present; fixtures ran from a sandboxed copy of the local distribution.
- **Local distribution manifest SHA-256:** `8cd14d7f0cd1a8afe082b43a94d3396895230021bf11022e0f6742304e6eef48`.
- **Go binary SHA-256:** `caa1b3c015e819aaa1408efe37b2499088bbf986bf30a2883bceab4e07b55b52`.
- **Probe profile SHA-256:** `3719f35247d027aa621b8ccc9a3087b6100986ecb4b1da1a710c847b12527a21`.

## 2. Pinned documents and tool members

| File | Origin/member | Version | SHA-256 | Status |
|---|---|---|---|---|
| go_spec_go1.23.html | Go distribution member | go1.23 | c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389 | PROVENANCE-PENDING |
| go_mem_2022-06-06.html | Go distribution member | go1.23.2 | 366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6 | PROVENANCE-PENDING |
| cmd_go_alldocs_go1.23.2.go | Go distribution member | go1.23.2 | 867ed1a38829a1eb555d3b417b58379dad290910ce87139022c2655661cd28da | PROVENANCE-PENDING |
| cmd_go_gc_language_go1.23.2.go | Go distribution member | go1.23.2 | 03a5ba6792c574baf3aa5ae7f7764b4920a13f1870c5347cfb73eda4f13e5512 | PROVENANCE-PENDING |
| cmd_go_toolchain_select_go1.23.2.go | Go distribution member | go1.23.2 | 26620592f186be645ee5d4e5270e7fbf2b262a6708dc5b9caaaee6d36fa58ea8 | PROVENANCE-PENDING |
| modfile_rule_go1.23.2.go | Go distribution member | go1.23.2 | 21b4ef48e7f8fd9d7f7fe909a06d2f9aac2c6eb1060e753f9a42369be3ab8e47 | PROVENANCE-PENDING |
| go_bin_go1.23.2_linux-amd64.sha256 | Go distribution member hash record | go1.23.2 | caa1b3c015e819aaa1408efe37b2499088bbf986bf30a2883bceab4e07b55b52 | PROVENANCE-PENDING |
| go1.23.2.linux-amd64.tar.gz | https://go.dev/dl/go1.23.2.linux-amd64.tar.gz | go1.23.2 | 542d3c1705f1c6a1c5a80d5dc62e2e45171af291e755d591c5e6531ef63b454e | PROVENANCE-PENDING |

## 3. Sanctioned probe environment

The following profile is the only sanctioned environment for differential fixtures. Unknown keys are not allowed.

```tsv
# FIDO probe environment — the COMPLETE allowed key set (T-9, directive v12). Unknown keys fail the audit.
# kind	key	value
env	GOOS	linux
env	GOARCH	amd64
env	GOAMD64	v1
env	CGO_ENABLED	0
env	GOFLAGS	
env	GOPROXY	off
env	GOTOOLCHAIN	local
env	GOENV	off
env	GOWORK	off
env	GODEBUG	
env	GOTRACEBACK	single
env	LANG	C.UTF-8
env	LC_ALL	C.UTF-8
env	TZ	UTC
env	PATH	{SANDBOX}/go/bin:/usr/bin:/bin
env	GOROOT	{SANDBOX}/go
env	HOME	{SANDBOX}/home
env	TMPDIR	{SANDBOX}/tmp
env	GOCACHE	{SANDBOX}/gocache
env	GOMODCACHE	{SANDBOX}/gomodcache
env	GOPATH	{SANDBOX}/gopath
meta	umask	0022
meta	sandbox_root	.review/spec-closure-campaign/evidence-sandbox
meta	path_normalization	replace absolute sandbox root with {SANDBOX} in all captured output
```

## 4. Captured observations

| Fixture | Mode | Observed status | Stdout summary | Stderr first line | Provenance |
|---|---|---:|---|---|---|
| `fatal_panic` | run | 2 | `(empty)` | `panic: fido-panic` | PROVENANCE-PENDING |
| `fma_branch_observation` | run | 0 | `ordinary=a46ff6fa122c625e\\nfma=a46ff6fa122c625f` | `(empty)` | PROVENANCE-PENDING |
| `lat019_shift_511_accept` | build | 0 | `(empty)` | `(empty)` | PROVENANCE-PENDING |
| `lat019_shift_512_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat019_shift_512_reject` | PROVENANCE-PENDING |
| `lat049_union_method_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat049_union_method_reject` | PROVENANCE-PENDING |
| `lat077_unused_local_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat077_unused_local_reject` | PROVENANCE-PENDING |
| `lat085_empty_type_set_operand_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat085_empty_type_set_operand_reject` | PROVENANCE-PENDING |
| `lat148_duplicate_switch_case_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat148_duplicate_switch_case_reject` | PROVENANCE-PENDING |
| `lat171_shadowed_result_naked_return_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat171_shadowed_result_naked_return_reject` | PROVENANCE-PENDING |
| `lat177_print_struct_reject` | build | 1 | `(empty)` | `# example.com/fido/specclosure/lat177_print_struct_reject` | PROVENANCE-PENDING |
| `println_stderr` | run | 0 | `(empty)` | `fido-latitude` | PROVENANCE-PENDING |

## 5. Observation tuple

The external observation tuple is:

```text
(stdout bytes, stderr projection, exit status)
```

`println` maps to stderr under the pinned target. Fatal panic adequacy checks exit status `2` and the first line `panic: <value>`. Other traceback and runtime noise are excluded from spec theorems and may be used only as pinned-toolchain evidence.

## 6. Platform boundary

No platform beyond go1.23.2 linux/amd64 is covered by this evidence. ADR-0004 remains deferred to C16. Adding a target requires a pinned distribution, its own probe profile, ledger updates, adequacy fixtures, and proof-impact review.

## 7. Margin note

The one-bit `x*y+z` vs `math.FMA` discrepancy doubles as a CPU-feature parlor trick: a pure-Go fingerprint of fused-multiply-add hardware paths. Recorded here for delight; not load-bearing.
