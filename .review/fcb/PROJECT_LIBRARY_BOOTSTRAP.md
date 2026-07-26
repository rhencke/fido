# Fido Documentation Bootstrap — Git Is Canonical

This is the only FCB-related file that belongs in a ChatGPT or Claude project library. It is a bootstrap pointer,
not documentation authority.

The sole canonical Fido Conformance Basis lives in the Git repository `rhencke/fido` under:

```text
.review/fcb/current/
```

For any Fido question involving governance, architecture, scope, fixed points, ledgers, acceptance gates,
toolchain evidence, roadmap, checkpoint authoring, model roles, or human-review state:

1. Typing.Resolved one exact repository ref. Use the candidate commit or uploaded repository snapshot specified for the
   task; otherwise use the latest accessible `main`.
2. Fetch `.review/fcb/current/INDEX.md` from that exact ref.
3. Follow it to the FCB Index.
4. Take every document from that one ref; Git's content addressing is the integrity guarantee.
5. Read `.review/NEXT_STEPS.md` from the same ref for the live checkpoint authority.
6. Consult only the documents named by the current Index. Never mix FCB files from different refs.

Do not treat this shim, old project-library files, chat memory, superseded FCB states, or the spec-closure campaign
archive as current FCB authority. If the repository/ref is unavailable or verification fails, stop and tell Rob;
do not guess.

When implementation, theorem topology, proof obligations, repository structure, or new evidence conflicts with
the current FCB, ChatGPT must propose a named coherent amendment and Claude must report the conflict rather than
implementing around it. Only Rob accepts or reopens governing documentation.
