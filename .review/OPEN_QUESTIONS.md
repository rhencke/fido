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
  edit that can silently not happen. Every edit script now asserts its target is present before writing.
- **Second instance, repair 16.** The assert discipline held, but a *different* sloppiness got through: while
  removing an orphaned comment I located it with a positional `rindex` rather than an explicit marker, and it
  silently took the adjacent `bucket_present_of_domain` definition with it. The build caught it immediately, so
  nothing shipped — but the two incidents share a root: **a scripted edit whose target is described by position
  rather than by content.** The rule I am now holding to is that every scripted edit names the exact text it
  replaces and asserts on it, including deletions.

---

## Q-08 — Charter §22's private `Emit.Image` constructor conflicts with the transport's kernel reduction

- **Owner:** the reviewer (mechanism), Rob (final call).
- **Blocking:** **YES** — repair 17 finding 3 and definition-of-done items 13, 14 and 20 cannot be met while
  this stands.
- **Default if nobody answers:** leave the constructor public with the strengthened representation described
  below, keep the conflict recorded here and in `Emit.v`, and do **not** describe `Emit.Image` as sealed
  anywhere. I will not substitute a nearby mechanism on my own.

**The two texts that cannot both hold.**

`FIDO_FCB_ARCHITECTURE_CHARTER.md` §22: *"`Emit.Image` remains because it pins the exact byte snapshot used by
validation and publication. Its constructor is private."* §24 likewise says to seal `Emit.Image` construction.

Standing technical law (CLAUDE.md, `ARCHITECTURE.md`): `Fido Materialize` is the sole transport, and it
decodes the image by applying the certified `Emit.transport` projection to the term and reducing it —
`plugin/materialize.mlg`, `let nf = Reductionops.nf_all env sigma app in decode_transport sigma nf`.

**Why both cannot hold.** A Rocq `Module M : SIG` seal removes the *bodies* of its components. Sealing the
image makes `module_bytes` and `files` opaque constants, so `nf_all` cannot reduce `transport img` past the
projection and the decoder receives a stuck term.

**Evidence (isolated by experiment, not inferred).** With `Module Images : IMAGE` — representation hidden —
`make emit` fails at the first witness:

```text
File "./e2e/Witness.v", line 131: Error: fido materialize: expected a directory-entries list
```

Changing exactly one token to `Module Images <: IMAGE` — the same signature, checked, but the representation
NOT hidden — makes the identical code emit correctly. The hiding is the cause; nothing else differs.

**What I did instead, and what it does not claim.** The representation now retains the exact `Safe.Program` it
was minted from and carries the two exactness proofs, so `provenance` became a projection of that retained
certificate rather than an existential the caller supplied. Every inhabitant therefore publishes exactly the
bytes of the certificate it holds. That strengthens the proof of origin and satisfies the directive's
"do not weaken the current proof of origin", but it does **not** close §22: `MakeImage` is still reachable.
The four forged-image provenance tests were also rewritten to postulate a `Safe.Program` and call the public
`Emit.of_safe`, as the directive requires, and all four still reject before any effect.

**Smallest amendments I can see, for the reviewer to choose between — I am not selecting one.**

1. **Abstract mint token.** Keep the record transparent (so the transport still reduces) and add a field whose
   type is abstract and whose only inhabitant is produced by a sealed `mint : forall sp, Minted sp
   (module_file sp) (file_map sp)`. `MakeImage` stays reachable but cannot be applied to arbitrary bytes —
   the token's indices force them. This is a type-level restriction, not a soundness argument. It does not
   literally make the constructor inaccessible, so §22 would need rewording to "construction is restricted to
   the canonical rendering of a retained `Safe.Program`".
2. **Move the byte production out of the reduced term.** Have `Fido Materialize` obtain bytes without
   kernel-reducing a Rocq projection — a real transport-boundary redesign, and larger than a repair.
3. **Amend §22** to require a retained-certificate representation with exactness proofs (what is implemented
   now) rather than a private constructor, on the ground that the private constructor is unachievable while
   the transport decodes a Rocq term.

**Blocked pending the decision:** repair 17 finding 3, and definition-of-done items 13, 14 and 20.
