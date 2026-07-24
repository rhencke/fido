Claude Code directive: C4 Implementation Review BLOCKING — exact standard work-member index repair 13

Repository:

rhencke/fido

Required clean baseline and thirteenth blocked C4 candidate:

af7d5d3e23c26850887c4fb178dad5f29c616385

Candidate commit:

review(final): C4 — freeze exact identity and audit candidate

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

Prior blocked C4 candidates:

89b8e54634e7012612a51990756ad29a579c1b0f
1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca
806ce87373e29b6980e5c3d9d274ffa86580449b
af2fc87e7726a4fc68bb9480c53cf64faa83717b
9d4aff5d94d9aac293ff7fb98a7d9fdd59159022
3b4f40e1f14c501fd76333ec8a8cd3e582ed1598
3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc
91e8dbbcd24fc7df678e6b3d68eabb13b686efa1
a2a5b46026cc658f41cb04f6d6cb30a29335671c
a8a44723250edd776c62dbb362d8fab51c21ab8f
3ecf32e3f7b9514070a1025b73231f541990e93c
48c0b31beb547326b058748a4d38c6cc41013009

The documentation-only withdrawn acceptance closeout:

37c9597f0c2161d69196ace737032370d148a6da

is NOT an implementation candidate. It remains superseded in history.

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Accepted review basis:

.review/REVIEW_BASIS.md

Superseded repair-12 authority SHA-256:

8ea26a948e52096e500e4ca830291c4a614980d629114f8307059355b20e3694

Human repair authorization:

C4-standard-work-member-index-repair-13

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 foundation consolidation / ruthless trim:

FORBIDDEN until C4 is accepted.

This is Rob's later explicit authorization to repair the exact standard-collection defect found at the candidate
above. It does not replace or weaken the binding C4 contract, accepted review basis, or standing collection law.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at af7d5d3e23c26850887c4fb178dad5f29c616385.

Repair 12 successfully closed its two assigned defects:

- StepCause_ok_conv_inv now returns a ConversionStep indexed by the exact source TypeSyntax and operand GoExpr
  supplied to the theorem;
- retained_convsuccess_closure and nested_success_bundle preserve that exact source-step identity;
- all four deep valid conversions expose the exact source ConversionStep;
- the stale prog_conv_outcomes / TFun collection rows were removed and replaced with the current C4 objects.

Keep those results.

A new load-bearing foundation defect was exposed by the rewritten collection audit:

ExprWorkForest.ewf_items is described as an ordered list view which is not identity storage, but the production
construction performs a NodeKey identity lookup by scanning that list with List.find.

The exact live path is:

  build_outcome_trace
    -> build_conversion_step
      -> build_conversion_work
        -> forest_member_at
          -> List.find ... (ewf_items forest)

forest_member_at searches ewf_items by NodeKey, uses ewf_keys_nodup to establish uniqueness, and returns the exact
WorkMember. It is called once per conversion while the outcome trace is built.

This makes ewf_items + ewf_keys_nodup a production identity-keyed lookup structure in addition to its legitimate
ordered-sequence role.

That violates the binding collection law:

- identity-keyed roles use a mature finite map;
- list is for ordered/repeated/positional/stack/transport/derived-enumeration roles;
- list + NoDup must not serve as public identity-keyed storage;
- no list scan may serve as a keyed find when a standard map fits.

The collection audit is therefore false when it says:

- ExprWorkForest is only an ordered view and not identity storage;
- no List.find is used for identity/membership storage;
- NoDup is never a carried uniqueness field standing in for a map;
- every identity-keyed collection has a mature standard backing.

This is not merely an audit-wording defect. The List.find is in the production call path and remains after proof
erasure. In a nested expression chain it repeatedly scans the whole retained work list, producing an avoidable
quadratic lookup pattern as the fragment grows.

Repair 13 must replace this hidden list-key authority with an exact standard-map-backed work-member index, or remove
the keyed lookup entirely through an equally exact structural construction. It must keep one immutable AST, one work
discovery, one retained forest object, and one causal outcome path.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_13.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 exact standard work-member index repair 13;
   - binding contract path and exact hash above;
   - accepted review basis path;
   - original C4 baseline;
   - all thirteen blocked candidate SHAs, ending at af7d5d3;
   - 37c9597 is a superseded documentation-only acceptance closeout, not a candidate;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_13.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; work-member index repair active;
   - repair-12 source-step identity results are retained;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-standard-work-member-index-repair-13
   result: BLOCKING at af7d5d3; exact standard work-member index repair 13 active

   Keep the C4 contract path/hash and review basis.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise current-only statement of the defect and required repair.

5. Commit only these authority changes:

   review(repair): C4 — replace list-key lookup with exact work index

No Rocq implementation, gate, generated, Docker, shell, OCaml, architecture, life, ADR, or scope-ledger change may
enter that authority commit.

6. After the authority commit, delete:

   .review/C4_IMPLEMENTATION_REPAIR_12.md

in the first implementation commit. Git history is its archive.

7. Correct historical range metadata:

   - repair-12 was implemented on top of 37c9597;
   - repair-12 range: 37c9597..af7d5d3;
   - repair-13 range: af7d5d3..final repair-13 freeze;
   - 37c9597 is not an implementation candidate.

Do not repeat the repair-12 range as 48c0b31..af7d5d3; the integrated repair-12 current-head amendment explicitly
set 37c9597 as the repair-12 range base.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 ewf_items is used as a NodeKey lookup table

ExprWorkForest retains:

  ewf_items : list (ExprWork input)

and:

  ewf_keys_nodup :
    NoDup (map work_key ewf_items)

forest_member_at accepts a NodeKey and searches:

  List.find
    (fun w => nodekey_eqb (work_key w) k)
    (ewf_items forest)

This is a keyed lookup, not sequential source-order processing.

2.2 forest_member_at is in the production semantic-construction path

This is not a specification-only theorem or fixture helper.

build_conversion_work calls forest_member_at to obtain cw_operand_work.

build_conversion_step calls build_conversion_work.

build_outcome_trace calls build_conversion_step in every conversion branch.

The exact operand WorkMember retained by every production ConversionStep therefore comes through a List.find scan
over ewf_items.

2.3 The list and NoDup field form a hidden identity authority

The code uses:

- the list as keyed storage;
- the NodeKey projection as identity;
- ewf_keys_nodup as uniqueness;
- List.find as lookup.

That is the exact list + NoDup keyed-table pattern forbidden by the standing collection law.

The fact that ewf_items also has a valid order role does not authorize using it as the identity lookup backend.

2.4 The collection audit's List.find statement is false

The audit says no List.find is used for identity/membership storage.

There are two List.find sites in the current theory:

- GoNames.classify over the fixed sixteen-name descriptor enumeration;
- GoCompile.forest_member_at over the retained expression work forest.

The second is a production NodeKey lookup and is a collection defect.

The next audit must enumerate both sites explicitly. It may retain GoNames.classify only with a precise explanation
that it is classification over one fixed closed descriptor, not persistent keyed storage. It must not hide
forest_member_at as a false positive.

2.5 The audit's NoDup statement is false

The audit says NoDup is never a carried uniqueness field standing in for a map.

ExprWorkForest carries ewf_keys_nodup as a record field, and forest_member_at uses the unique NodeKey property to
turn its list search into an exact identity lookup.

After repair, ewf_keys_nodup may remain as a fact about the ordered enumeration and as evidence for building the
standard index. It must no longer be the uniqueness mechanism for a list-backed lookup.

2.6 Repeated conversion lookup is avoidably quadratic

forest_member_at searches ewf_items from the front for each conversion.

For a deeply nested conversion chain, repeated lookups grow quadratically with expression count.

Performance is not the acceptance criterion, but this growth is evidence that the missing identity index is a real
root abstraction, not a prose preference.

2.7 Current status contains stale repair-12 text

At af7d5d3:

- SOURCE_FOREST_STATUS says the repair-12 freeze "will be" the candidate head although the file is in that freeze;
- SOURCE_FOREST_STATUS says no scope change occurred in repair 11 instead of repair 12;
- PROGRESS describes repair 12 as active and says no production change is authorized after the candidate is already
  complete;
- NEXT_STEPS uses 48c0b31 as the repair-12 range base despite the integrated current-head amendment requiring
  37c9597.

Repair 13 must leave all current-state documents factually current.

===============================================================================
3. REQUIRED EXACT WORK-MEMBER INDEX
===============================================================================

Choose the smallest design which removes keyed list lookup while preserving the one-source / one-work-object
architecture.

The preferred design is a standard-map-backed index tied exactly to ewf_items.

A shape equivalent to this is acceptable:

  Record ExprWorkIndex (items : list (ExprWork input)) := {
    ewi_map : NodeKeyMapBase.t (ExprWork input);

    ewi_exact :
      forall k w,
        NodeKeyMapBase.find k ewi_map = Some w
        <->
        In w items /\ work_key w = k;

    ewi_domain :
      forall k,
        NodeKeyMapBase.find k ewi_map <> None
        <->
        exists w, In w items /\ work_key w = k
  }.

Then retain the exact index in or immediately beside the exact forest object:

  ExprWorkForest input
    contains/depends on
      ewf_items
      ewf_index : ExprWorkIndex ewf_items

The exact names and layout are your choice.

Rules:

- use GoIndex.NodeKeyMapBase / FMapAVL or another already-approved standard finite map;
- the ordered list remains the source/per-file-order authority;
- the map is the exact identity lookup index derived from that same list;
- the list and map must be tied by dependent fields or exact bidirectional laws;
- a foreign map must not be pairable with the forest;
- build the index once from ewf_items, not by a second AST traversal;
- no silent overwrite;
- use ewf_keys_nodup / per-step freshness to prove each add is fresh;
- a missing entry for a proven member is unrepresentable through the total query;
- no fallback to empty or arbitrary work;
- no parallel independently discovered work set.

An equivalent structural design is allowed if it carries each conversion's exact operand WorkMember during the one
forest construction and performs no keyed list scan at all.

If an identity lookup remains, it must use the standard map.

If no standard collection can express the dependent value safely, document the exact mismatch and report an
ARCHITECTURAL CONFLICT. Do not keep List.find.

===============================================================================
4. REQUIRED TOTAL MEMBER QUERY
===============================================================================

Replace forest_member_at with a total map-backed query or direct structural projection.

An acceptable public interface is equivalent to:

  work_member_at :
    forall forest k,
      WorkKeyPresent forest k ->
      { wm : WorkMember forest | work_key (proj1_sig wm) = k }.

Or, preferably for conversion work:

  operand_work_member :
    forall forest current ts x,
      current is a retained conversion member ->
      WorkMember forest

with exact operand-ref/key/source proofs.

The total query must prove:

- the result is a member of the exact ewf_items;
- its key is the requested key;
- its ExprRef is the exact carried conversion operand ExprRef;
- its occurrence and expression are the exact source operand occurrence/expression;
- uniqueness follows from the standard map plus exact index relation;
- no equal-key fresh ExprWork can substitute.

No List.find, find on a derived list, existsb scan, or recursive list-key search may occur in this query's production
call closure.

===============================================================================
5. REQUIRED CONVERSION PATH
===============================================================================

Keep the accepted causal architecture.

The live path must become:

  build_outcome_trace
    -> build_conversion_step
      -> build_conversion_work
        -> exact retained work index query
          -> standard NodeKeyMapBase.find

Requirements:

- build_conversion_work consumes the operand ExprRef already carried by ew_conv;
- query the work index at node_ref_key (erase_ref operand_ref), not a separately guessed source value;
- recover one exact WorkMember from the index;
- preserve cw_operand_ref_eq / cw_operand_expr / cw_operand_role / cw_operand_key;
- build_conversion_step proves that exact member belongs to the current processed suffix;
- the outcome trace reads the operand result through that exact SuffixMember;
- one convert_const;
- no semantic rescan;
- no reminted refs;
- no source const_info recursion;
- no second work-index build.

The exact source-step identity added in repair 12 must remain unchanged.

===============================================================================
6. REQUIRED INDEX CONSTRUCTION
===============================================================================

Build the index once.

Preferred pattern:

1. build ewf_blocks / ewf_items once from ci_blocks / ci_visit;
2. fold ewf_items once into NodeKeyMapBase;
3. prove freshness from ewf_keys_nodup or the remaining suffix;
4. retain exact map/list correspondence in the forest/index object;
5. pass the same exact forest/index object forward.

Do not:

- call build_forest_blocks again;
- rediscover expressions from ci_visit;
- build the work map independently in every consumer;
- project a raw map and recover its proof later;
- use map equality alone while allowing foreign pairing;
- silently overwrite a duplicate key;
- keep a list-search fallback.

The map may be a derived identity index. It does not become a peer source AST or peer semantic authority.

===============================================================================
7. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems over production definitions.

7.1 Index construction

Prove:

- exact map domain iff ewf_items membership by work key;
- every ewf_items member has exactly one index entry;
- every index entry is exactly one ewf_items member;
- duplicate work keys are impossible;
- index construction adds each key once;
- index construction uses the already-built ewf_items and no second source traversal.

7.2 Total member query

Prove:

- query at a retained member key returns that exact member;
- query result has exact NodeRef, ExprRef, occurrence, role, and source expression;
- no foreign key has a member;
- no wrong-kind occurrence has a member;
- no equal-key fresh ExprWork value can be substituted.

7.3 Conversion work

Prove:

- build_conversion_work obtains cw_operand_work through the exact work index;
- cw_operand_work's ExprRef is the carried conversion operand ref;
- cw_operand_work's source expression is x;
- build_conversion_step carries that same member into the exact processed suffix;
- the outcome trace consumes that same SuffixMember.

7.4 Object flow

Prove or make definitional:

- one index object is built;
- the exact forest/index is consumed by every conversion work construction;
- no consumer rebuilds the map;
- facts, diagnostics, trace, and sealing remain indexed by the same forest/outcome objects.

7.5 Existing accepted evidence

Reprove and keep:

- StepCause_ok_conv_inv exact source ts/x;
- retained_convsuccess_closure exact source step;
- nested_success_bundle exact source step;
- all four valid conversions;
- failure diagnostic identity;
- final-to-tail closure;
- trace uniqueness;
- exact fact/type-name sealing;
- alias/render/generated-byte results.

===============================================================================
8. REQUIRED DIRECT FIXTURES
===============================================================================

Add a direct work-index fixture over the deep nested program.

It must prove for every conversion:

- the conversion's carried operand ExprRef key queries the exact work index;
- the returned WorkMember is the exact operand member;
- the member lies in the processed suffix;
- the final ConversionStep uses that member;
- the final operand outcome and current outcome remain the accepted values.

Add an identity-distinction fixture with two syntactically equal expression values at distinct occurrences:

- both have distinct NodeKeys;
- both have distinct index entries;
- querying each key returns its own retained WorkMember;
- no value-equality or source-expression equality can conflate them.

Keep:

- exact deep valid success evidence;
- exact deep failure + stored diagnostic;
- outer child-failure closure;
- wrong-kind/foreign absence;
- exact work count;
- two-uint8 retained-fact fixture;
- alias matrix.

===============================================================================
9. REQUIRED COLLECTION AUDIT
===============================================================================

Rewrite the living collection audit again, this time including the lookup role which the previous rewrite missed.

Required rows:

1. ExprWorkForest ordered views:
   - ewf_blocks / ewf_items;
   - list;
   - order role only;
   - no keyed lookup through the list.

2. Exact work-member index:
   - NodeKey -> ExprWork/WorkMember representation;
   - NodeKeyMapBase / FMapAVL;
   - exact domain and map/list relation;
   - one retained index built once.

3. OutcomeAccumulator / ForestOutcomeTable:
   - unchanged standard map outcome authority.

4. OutcomeTrace:
   - unchanged causal proof structure.

5. Fact and type-name tables:
   - unchanged separate standard maps.

6. List.find inventory:
   - no List.find in GoCompile's production work path;
   - explicitly classify GoNames.classify over the fixed closed sixteen-name descriptor enumeration, or replace it;
   - do not claim zero List.find sites when one remains.

7. NoDup inventory:
   - ewf_keys_nodup is a retained fact about the ordered enumeration and index construction;
   - it is not the backing store or lookup mechanism;
   - no list + NoDup identity table remains.

Run a full current symbol-and-role audit.

===============================================================================
10. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete:

- forest_member_at;
- its List.find code;
- comments calling list search the exact member recovery mechanism;
- any fallback keyed scan of ewf_items;
- collection-audit claims that hide that scan;
- stale repair-12 current-state wording.

Run tracked-tree searches for:

- forest_member_at;
- List.find in GoCompile.v;
- nodekey_eqb scans over ewf_items;
- existsb/find scans over ewf_items;
- "none used as identity/membership storage" without an exact site inventory;
- list + ewf_keys_nodup described as the member lookup authority;
- repeated work-index construction;
- old family-specific conversion constructors;
- raw OutcomeCause / build_outcome_accumulator / FinalMemberCause;
- duplicate type-name spelling/resolver tables;
- C5 uintptr/rune implementation;
- stale repair-12 range 48c0b31..af7d5d3;
- stale "repair-12 freeze will be candidate head";
- stale "no scope change in repair 11".

Historical wording inside this repair-13 directive is allowed.

===============================================================================
11. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or scope decisions.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- every scope-ledger entry PROPOSED unless Rob explicitly accepts it.

Do not begin DecimalFloat decision work.

===============================================================================
12. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list.

Each TODO must contain:

- exact object produced;
- exact prior object consumed;
- semantic role: order or identity;
- standard backing;
- exact map/list relation;
- observable production completion condition;
- load-bearing theorem;
- old list-key path deleted;
- direct fixture;
- gate entry;
- residue search;
- status.

Minimum TODOs:

T1 — define the exact standard work-member index
T2 — build it once from ewf_items with no silent overwrite
T3 — total map-backed WorkMember query
T4 — build_conversion_work consumes the exact index query
T5 — build_conversion_step retains the exact indexed operand in the suffix
T6 — outcome trace unchanged and consumes the same member
T7 — exact domain / uniqueness / no-foreign proofs
T8 — deep nested and equal-expression-distinct-key fixtures
T9 — preserve repair-12 exact source-step evidence
T10 — rewrite collection audit including List.find and NoDup site inventories
T11 — current status/range/residue closeout
T12 — full verification/freeze/push

A TODO is not complete because List.find returns the mathematically correct member.

The standard collection law governs representation and lookup architecture, not only extensional result equality.

===============================================================================
13. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously.

Use this loop:

1. design the smallest exact standard work index;
2. build it once from the retained ordered items;
3. replace forest_member_at;
4. thread the exact query through ConversionWork and ConversionStep;
5. reprove the trace and accepted evidence;
6. add direct index fixtures;
7. rewrite the collection audit;
8. remove list-key residue;
9. fix current status/ranges;
10. run narrow proof checks;
11. run full verification;
12. inspect the exact freeze;
13. repeat until clean.

Do not stop for design approval, proof volume, or a large diff.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct repair attempts. Report the exact file,
definition/theorem or command, the smallest failing case, and why neither this directive nor the binding contract
decides it.

If the dependent work value cannot be represented in a standard map without violating the causal/object-identity
rules, that is an ARCHITECTURAL CONFLICT and must be reported. A desire to keep List.find is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 13 COMPLETE

or

FIDO C4 REPAIR 13 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
14. FINAL VERIFICATION
===============================================================================

Run from a clean supported environment:

make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check

Run the staged pre-commit check on the complete candidate.

Report:

- exact readable gate count and result;
- whole-theory audit and self-tests A-E;
- full pinned-Go alias matrix;
- exact generated go.mod and recursive .go byte identity;
- exact ExprWorkForest/index object shape;
- exact standard map backing;
- exact map/list correspondence theorems;
- exact total member query;
- exact production call path;
- confirmation of one work discovery and one index build;
- confirmation of zero GoCompile List.find work lookup;
- GoNames.classify disposition;
- deep nested index fixture;
- equal-expression/distinct-key fixture;
- preserved success/failure/diagnostic evidence;
- standard-collection audit conclusion;
- full old-constructor/no-C5 search;
- duplicate resolver/spelling search;
- stale status/range search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - af7d5d3..final.

Green commands do not replace inspection of the actual lookup path and collection roles.

===============================================================================
15. FINAL FREEZE AND PUSH
===============================================================================

After implementation, proofs, fixtures, audit, residue, and verification pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 exact standard work-member index repair 13 candidate complete;
   - original C4 baseline: 8c9212a;
   - all thirteen blocked candidates, ending at af7d5d3;
   - 37c9597 remains a superseded documentation-only acceptance closeout, not a candidate;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-12 range: 37c9597..af7d5d3;
   - repair-13 range: af7d5d3..this freeze commit;
   - human C4 Implementation Review pending;
   - exact standard work-member index retained;
   - no production List.find key lookup;
   - repair-12 exact source-step identity preserved;
   - collection audit current and role-checked;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until C4 acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-standard-work-member-index-repair-13
   result: thirteenth BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary impl(...) commits during implementation.

4. Make exactly one final freeze commit after all work passes:

   review(final): C4 — freeze exact standard work-index candidate

5. Run every final check on that exact commit.

6. If anything fails or the list-key lookup survives, repair it and create a new final freeze commit. Only the latest
   passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-13 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - index design and standard backing;
   - exact map/list relation;
   - deleted forest_member_at path;
   - exact production call path;
   - direct fixtures;
   - preserved repair-12 evidence;
   - collection audit;
   - gate count;
   - full verification;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.
