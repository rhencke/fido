(** ============================================================================
    GoSem.v — the AST's BEHAVIORAL semantics as a BRIDGE into cmd.v (charter Phase 5; ARCHITECTURE.md §GoSem).
    GoSem forks NO second universe: [denote_program : Program -> option (Cmd unit)] TRANSLATES a GoAst program
    into cmd.v's proven command tree, reusing cmd.v's [run_cmd] interpreter + [cbind], the GoSafe gate
    ([expr_stmt_ok] / [svalue]), and the model's own value ctors ([anyt] / [intwrap]) — single-authority, faithful
    (a denoted [println] produces EXACTLY the [w_log] the model's [println] does).

    SLICE 1 (partial, to grow):
    - DENOTES a SUBSET of supported statements: [println]/[print] -> [COut] (the model's [w_log]); [panic] ->
      [CPan]; [return]/[panic] TERMINATE (their unreachable successors need only be SUPPORTED, not denotable);
      [_ = e] -> [CRet] when [e] is a constant.  Print/panic args fold via [eval_value] (constants only — the
      folds exercised are listed in the [eval_value_good] table below; runtime / out-of-range / [GsDefer]'s CDfr
      etc. are NOT yet denoted).
    - FAITHFUL-OR-ABSENT: a supported program gets its RIGHT behavior or (not yet) NONE ([denote_program = None]) —
      NEVER a wrong one.  [None] means "not modeled yet", NOT "invalid".
    - [gosem_sound]: denotation ⊆ [SupportedProgram] (structural — [denote] consults the gate; a partial
      [eval_value] narrows only COMPLETENESS, never soundness).  NOT [supported ⇒ denotes] (the roadmap
      converse), and does NOT define [BehaviorSafe].
    - Public TRUST SURFACE (zero-axiom, [Print Assumptions]-gated): [gosem_trust_surface] +
      [gosem_string_authority_surface].  No axioms.
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.

(** Box an integer-constant VALUE [z] of int type [t] as the MODEL's runtime [GoAny] — or [None].  FAILS CLOSED
    at the BOUNDARY: it first checks [int_const_repr z t] (is [z] representable in [t]?), so an out-of-range [z]
    yields [None] HERE, not a silently [*wrap]-mangled value — exactness does NOT rely on a caller having gated
    (rule 4: evidence at the builder).  When in range the [*wrap] constructor is IDENTITY, so it builds EXACTLY
    the model's value (e.g. [int64(3)] -> [anyt TI64 (i64wrap 3)] = [MkI64 3], what the model's [println]
    carries).  [GTUint] is boxed via [mk_uint] below (the model's proof-carrying [uint_lit]); floats go through
    [box_float] below. *)

(** Box a [GTUint] (Go platform [uint]) CONSTANT [z].  The model's [GoUint] carries an [in_u64] PROOF, so
    [mk_uint] discharges it self-soundly via a dependent match on [in_u64 z] — NOT caller-gated ([None] if
    [z] ∉ [[0,2^64)]).  [box_int]'s [int_const_repr] guard already restricts [z] to [GTUint]'s conservative
    [[0,2^32-1]] ⊂ [[0,2^64)], where [uint_lit z] is the model's EXACT uint value [z] (the [GoU64] shape). *)
Definition mk_uint (z : Z) : option GoAny :=
  (match in_u64 z as b return (in_u64 z = b -> option GoAny) with
   | true  => fun pf => Some (anyt TUint (uint_lit z pf))
   | false => fun _  => None
   end) eq_refl.

Definition box_int (t : GoTy) (z : Z) : option GoAny :=
  if int_const_repr z t then
    match t with
    | GTInt   => Some (anyt TInt64 (intwrap z))   (* Go [int]  -> [GoInt] *)
    | GTInt64 => Some (anyt TI64  (i64wrap z))     (* Go [int64]-> [GoI64] (Z-carried) *)
    | GTU8    => Some (anyt TU8   (u8wrap  z))
    | GTI8    => Some (anyt TI8   (i8wrap  z))
    | GTU16   => Some (anyt TU16  (u16wrap z))
    | GTI16   => Some (anyt TI16  (i16wrap z))
    | GTU32   => Some (anyt TU32  (u32wrap z))
    | GTI32   => Some (anyt TI32  (i32wrap z))
    | GTU64   => Some (anyt TU64  (u64wrap z))
    | GTUint  => mk_uint z   (* Go platform [uint] -> [GoUint], via the model's proof-carrying [uint_lit] *)
    | _       => None        (* non-integer [t] *)
    end
  else None.

(** Box a float-CONSTANT VALUE — an integer [z] that an EXACT float of type [t] ([GTFloat64]/[GTFloat32]) came
    from — as the MODEL's runtime [GoAny], or [None].  FAILS CLOSED at the boundary with the SAME guard [ptype]
    used to FORM [PtFloatConst] ([int_in_float_exact_interval]: is [z] in the CONTIGUOUS exactly-representable
    interval [[-2^53,2^53]] / [[-2^24,2^24]]?), so an out-of-interval [z] yields [None] HERE — no rounded-lie
    value.  In range the boxed value is the UNIQUE canonical binary64/binary32 form of [z] ([renorm 53 1024] /
    [f32_lit] over the model's [sf_of_Z]), EXACTLY the float the model carries (inside the interval EVERY
    integer is exact, so there is no rounding).  Float CONSTANT arithmetic / fractional literals never reach
    here — [PtFloatConst] carries an integer [z], and [ptype] does not fold them (over-rejected). *)
Definition box_float (t : GoTy) (z : Z) : option GoAny :=
  if int_in_float_exact_interval t z then
    match t with
    | GTFloat64 => Some (anyt TFloat64 (renorm 53 1024 (sf_of_Z z)))   (* canonical binary64 of [z] *)
    | GTFloat32 => Some (anyt TFloat32 (f32_lit (sf_of_Z z)))           (* [f32_lit] rounds-in to canonical binary32 (exact here) *)
    | _         => None
    end
  else None.

(** The COMPARISON [BinOp]s fold a constant integer pair to a [bool] ([>]/[>=] reuse [<]/[<=] with swapped
    operands).  Arithmetic / [BLAnd] / [BLOr] are NOT comparisons -> [None] HERE; the logical [&&]/[||] are
    handled separately by [eval_bool] (which recurses on their bool operands). *)
Definition cmp_op (op : BinOp) : option (Z -> Z -> bool) :=
  match op with
  | BEq => Some Z.eqb
  | BNe => Some (fun x y => negb (Z.eqb x y))
  | BLt => Some Z.ltb
  | BLe => Some Z.leb
  | BGt => Some (fun x y => Z.ltb y x)
  | BGe => Some (fun x y => Z.leb y x)
  | _   => None
  end.

(** The constant VALUE of a numeric operand (an integer constant, or an exact-integer FLOAT constant — both
    carry the true value as [Z], so [Z]-comparison IS the Go comparison), via [ptype]; [None] for a RUNTIME or
    non-numeric operand (so a comparison with a [len(..)] operand is honestly absent, not folded wrong). *)
Definition const_z (e : GExpr) : option Z :=
  match ptype e with
  | Some (PtIntConst z) | Some (PtTIntConst _ z) | Some (PtFloatConst _ z) => Some z
  | _ => None
  end.

(** The constant string VALUE of a supported [PtStr] expr — THE SINGLE string-value authority (both
    [eval_value]'s [PtStr] arm AND [eval_bool]'s string comparisons consult it).  Folds a LITERAL [EStr s], the
    CONCATENATION [a + b] (Go [+] on strings = byte [String.append], exact), and the CONVERSION [string(a)]
    (mirroring [conv_to_scalar]'s [GTString] cases: an identity string source, or an ASCII rune [z ∈ [0,127]]
    whose UTF-8 IS the single byte [z]).  SEALED under [ptype = PtStr] (never folds ill-typed [`"a" + 1`]).
    ABSENT ([None], honestly): a multi-byte rune [string(200)] and any runtime string. *)
Fixpoint eval_str (e : GExpr) : option string :=
  match ptype e with
  | Some PtStr =>   (* SEAL: fold ONLY what [ptype] validated as a string *)
      match e with
      | EStr s        => Some s
      | EBn BAdd a b  => match eval_str a, eval_str b with
                         | Some sa, Some sb => Some (String.append sa sb)
                         | _, _ => None
                         end
      | ECall (EId i) (a :: nil) =>   (* the string conversion [string(a)] — MIRRORS [conv_to_scalar]'s [GTString] cases *)
          if String.eqb (proj1_sig i) "string"
          then match ptype a with
               | Some PtStr => eval_str a   (* string SOURCE: the identity conversion [string("a"+"b")] = its bytes *)
               | Some (PtIntConst z) | Some (PtTIntConst _ z) =>
                   (* rune conversion.  FAITHFUL-OR-ABSENT: fold ONLY code points [0,127], whose UTF-8 encoding IS
                      the single byte [z] ([string(65)] = ["A"]) — trivially exact.  A rune >127 (multi-byte UTF-8)
                      or an out-of-range/negative rune (Go yields [U+FFFD]) is NOT folded — absent, never wrong. *)
                   if andb (Z.leb 0 z) (Z.leb z 127)
                   then Some (String (Ascii.ascii_of_nat (Z.to_nat z)) EmptyString)
                   else None
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

(** The 6 COMPARISON ops on STRING constants — DELEGATED to the MODEL's string order, named by their FULLY
    QUALIFIED paths ([Fido.builtins.str_eqb] / [str_neqb] / [str_ltb] / [str_gtb] / [str_geb], the byte-wise
    unsigned Go order, plugin-lowered to the native Go operators).  The qualified names make the live path
    SHADOW-IMMUNE: a local/nested [str_ltb] in GoSem cannot reroute it (the [str_cmp_*_model] pins below prove
    each branch IS the qualified model constant).  GoSem forks NO string order; [<=] is DERIVED from the model's
    [>=] ([s <= t] iff [t >= s]).  Non-comparison ops -> [None]. *)
Definition str_cmp_op (op : BinOp) : option (GoString -> GoString -> bool) :=
  match op with
  | BEq => Some Fido.builtins.str_eqb
  | BNe => Some Fido.builtins.str_neqb
  | BLt => Some Fido.builtins.str_ltb
  | BLe => Some (fun s t => Fido.builtins.str_geb t s)   (* [s <= t]  iff  [t >= s] — derived from the model order, not re-implemented *)
  | BGt => Some Fido.builtins.str_gtb
  | BGe => Some Fido.builtins.str_geb
  | _   => None
  end.

(** Fold a CONSTANT bool to its [bool], else [None] (bool VALUE lives here: [ptype] keeps [PtBool] value-less).
    SELF-SEALED: every entry (top + each recursive call) first demands [ptype e = Some PtBool], so a
    [ptype]-rejected compare (e.g. mixed-width [int64(1)==int32(1)]) returns [None], not a fabricated value — the
    precondition is enforced here, not assumed of the caller.  Reuses [ptype]'s numeric operand values
    ([const_z]) / string constants ([eval_str], the single string-value authority), recursing over the 6 numeric
    or string-constant COMPARISONs, the LOGICAL [&&]/[||]/[!], and the identity [bool(x)].  A runtime-operand or
    multi-byte-rune leaf is honestly absent ([None]). *)
Fixpoint eval_bool (e : GExpr) : option bool :=
  match ptype e with
  | Some PtBool =>   (* SEAL: fold ONLY what [ptype] validated as a bool *)
      match e with
      | EUn UNot a    => match eval_bool a with Some x => Some (negb x) | None => None end
      | EBn BLAnd a b => match eval_bool a, eval_bool b with Some x, Some y => Some (andb x y) | _, _ => None end
      | EBn BLOr  a b => match eval_bool a, eval_bool b with Some x, Some y => Some (orb  x y) | _, _ => None end
      | EBn op a b =>
          match cmp_op op, const_z a, const_z b with
          | Some cmp, Some x, Some y => Some (cmp x y)                      (* numeric comparison *)
          | _, _, _ =>
              match str_cmp_op op, eval_str a, eval_str b with
              | Some scmp, Some s, Some t => Some (scmp s t)               (* string-CONSTANT comparison (any [eval_str]-folded operand, via [str_cmp_op]) *)
              | _, _, _ =>
                  match op, eval_bool a, eval_bool b with                 (* else [==]/[!=] of two bool sub-bools *)
                  | BEq, Some x, Some y => Some (Bool.eqb x y)
                  | BNe, Some x, Some y => Some (negb (Bool.eqb x y))
                  | _, _, _ => None
                  end
              end
          end
      | ECall (EId f) (a :: nil) =>                                        (* identity bool CONVERSION [bool(x)] *)
          if String.eqb (proj1_sig f) "bool" then eval_bool a else None
      | _ => None
      end
  | _ => None
  end.

(** Evaluate a value expr to the model's [GoAny], else [None].  FAITHFUL via [ptype] (the SINGLE folding
    authority): [ptype] folds a numeric constant to its VALUE+TYPE, and [box_int] / [box_float] attach the model
    value, FAILING CLOSED on an out-of-range/interval [z] (self-sound, not caller-gated).  Coverage exercised —
    the [eval_value_good] table (gated by [eval_value_good_ok]) folds: integer constants (conversions / in-range
    [uint] via [mk_uint] / arithmetic / complement, EXCLUDING platform-[uint] complement), exact-integer FLOAT
    constants, string constants ([eval_str]), and constant bools ([eval_bool]).  ABSENT ([None], honestly): runtime operands
    ([len(..)]/[int(x)]), out-of-range or COMPLEMENTED [uint], fractional/multi-byte-rune — never wrong. *)
Definition eval_value (e : GExpr) : option GoAny :=
  match ptype e with
  | Some (PtIntConst z)     => box_int GTInt z                                                 (* untyped const -> default [int], range-checked *)
  | Some (PtTIntConst t z)  => box_int t z                                                     (* typed int const (conversion / typed arith) *)
  | Some (PtFloatConst t z) => box_float t z                                                   (* typed float const (exact int-valued: [float64(3)], [-float32(5)]) *)
  | Some PtStr              => match eval_str e with Some s => Some (anyt TString s) | None => None end  (* a string CONSTANT: literal / concatenation / string-or-rune conversion ([PtStr] carries no value; [eval_str] folds it) *)
  | Some PtBool             => match eval_bool e with Some b => Some (anyt TBool b) | None => None end   (* a CONSTANT bool: comparison / logical fold *)
  | _                       => None
  end.

Fixpoint eval_args (args : list GExpr) : option (list GoAny) :=
  match args with
  | [] => Some []
  | a :: rest =>
      match eval_value a, eval_args rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** Translate ONE statement to its command PAIRED WITH a TERMINATES flag (successors unreachable), or [None] if
    unmodeled.  The flag makes [denote_stmt] the SINGLE control-flow authority ([denote_body] never re-decides);
    it is ESSENTIAL, not derivable (a [return] and a blank-assign both give [CRet tt] but differ
    stop/fall-through).  The EFFECT arm fires ONLY when [expr_stmt_ok] holds — this makes [denote] ⊆ the gate
    ([gosem_sound]), however partial [eval_value] is.  [println]/[print] -> fall-through [COut]; [panic] ->
    terminating [CPan]; [return] -> terminating [CRet]; a blank-assign of a constant -> fall-through [CRet]. *)
Definition denote_stmt (s : GoStmt) : option (Cmd unit * bool) :=
  match s with
  | GsReturn        => Some (CRet tt, true)    (* TERMINATES the body *)
  | GsBlankAssign e =>
      (* [_ = e] discards [e]'s VALUE but NOT its runtime EFFECTS.  Denote it ONLY when slice-1 [eval_value]
         handles [e] (a scalar LITERAL — no effect, CANNOT panic), giving the faithful fall-through [CRet tt].
         A RUNTIME [e] (e.g. [1 / len([]int{})], which Go PANICS on) is left UN-denoted ([None]) until the
         evaluator models effects — GoSem must NEVER give it the WRONG (silent) behavior.  [svalue e] is still
         required so [denote] ⊆ the gate ([stmt_ok]'s blank arm IS [svalue]). *)
      if svalue e then match eval_value e with Some _ => Some (CRet tt, false) | None => None end else None
  | GsReturnVal _   => None                                        (* a value return is invalid in void [main] *)
  | GsExprStmt e =>
      if expr_stmt_ok e then
        match e with
        | ECall (EId f) args =>
            let fn := proj1_sig f in
            if String.eqb fn "panic"
            then match args with
                 | a :: nil => match eval_value a with Some v => Some (CPan v, true) | None => None end  (* TERMINATES *)
                 | _ => None
                 end
            else match eval_args args with                        (* println / print: fall through *)
                 | Some vs => Some (COut (String.eqb fn "println") vs (CRet tt), false)
                 | None => None
                 end
        | _ => None
        end
      else None
  | GsDefer _ => None
      (* [defer <call>] is SUPPORTED + emittable but NOT YET denoted (faithful-or-ABSENT): its [cmd.v] [CDfr]
         denotation needs [run_cmd] fuel > 1, whereas slice 1's execution story is fuel-1 (denotes [no_defer]
         only).  Denoting defers needs that foundation generalized to sufficient-fuel; until then it is absent. *)
  end.

Fixpoint denote_body (b : list GoStmt) : option (Cmd unit) :=
  match b with
  | [] => Some (CRet tt)
  | s :: rest =>
      match denote_stmt s with
      | None => None
      | Some (c, term) =>
          if term then
            (* [s] TERMINATES (return / panic, per [denote_stmt]'s flag): emit its command [c] (which stops —
               [CRet]/[CPan]); the REST is UNREACHABLE, so its DENOTABILITY is irrelevant — require only that it
               be SUPPORTED ([forallb stmt_ok rest], the gate).  Keeps [denote_body] ⊆ the gate while NOT making
               a terminator depend on a successor slice 1 cannot yet evaluate. *)
            (if forallb stmt_ok rest then Some c else None)
          else
            match denote_body rest with
            | Some k => Some (cbind c (fun _ => k))
            | None => None
            end
      end
  end.

Definition denote_program (p : Program) : option (Cmd unit) :=
  if String.eqb (proj1_sig (prog_pkg p)) "main"
  then denote_body (prog_body p)
  else None.

(** ---- GATE CONNECTION (the slice-1 earns-its-weight theorem): denotation ⊆ supportedness ----
    GoSem gives a behavior ONLY to a program GoSafe accepts.  Because each [denote_stmt] arm that returns
    [Some] is itself gated ([GsReturn] is always [stmt_ok]; [GsBlankAssign] on [svalue]; [GsExprStmt] under
    [expr_stmt_ok]), this is structural. *)
Lemma denote_stmt_sound : forall s, denote_stmt s <> None -> stmt_ok s = true.
Proof.
  intros s H. destruct s as [e| |e0|e|e]; simpl in *.
  - destruct (expr_stmt_ok e); [reflexivity | congruence].   (* GsExprStmt: gated on [expr_stmt_ok] *)
  - reflexivity.                                             (* GsReturn *)
  - congruence.                                              (* GsReturnVal: None *)
  - destruct (svalue e); [reflexivity | congruence].         (* GsBlankAssign: gated on [svalue] = stmt_ok *)
  - congruence.                                              (* GsDefer: [denote_stmt] = None, so [H] is absurd *)
Qed.

Lemma denote_body_sound : forall b, denote_body b <> None -> forallb stmt_ok b = true.
Proof.
  induction b as [|s rest IH]; simpl; intro H.
  - reflexivity.
  - destruct (denote_stmt s) as [[c term]|] eqn:Es; [|congruence].   (* denote_stmt s = None => denote_body = None *)
    apply andb_true_intro; split.
    + apply denote_stmt_sound. congruence.             (* stmt_ok s, uniform via [Es] *)
    + destruct term.                                   (* the [denote_stmt] flag: terminator gates rest on supportedness; else on denotability *)
      * destruct (forallb stmt_ok rest) eqn:Ef; [reflexivity | congruence].
      * destruct (denote_body rest) eqn:Er; [|congruence]. apply IH. congruence.
Qed.

Theorem gosem_sound : forall p, denote_program p <> None -> supported_program p = true.
Proof.
  intros p H. unfold denote_program in H. unfold supported_program.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:Epkg; simpl in *.
  - apply denote_body_sound. exact H.
  - congruence.
Qed.

(** ---- DENOTABILITY IS DECIDABLE, characterized STRUCTURALLY (the converse-direction companion of
    [gosem_sound] / [denote_body_sound]).  [denotable_body] is a pure [bool] decision procedure mirroring
    [denote_body]'s discipline: a body denotes iff its head statement denotes ([denote_stmt s <> None]) AND —
    at a TERMINATOR — the unreachable rest is merely SUPPORTED ([forallb stmt_ok rest]), else the rest is
    itself denotable.  [denote_body_dec] proves the two AGREE: denotability decomposes statement-by-statement,
    with NO body-level failure mode of its own beyond [denote_stmt]'s.  This is the SCAFFOLD toward the eventual
    "supported ⟺ denotes".  The [denotable_*] ⊊ [supported_*] gap has TWO independent sources: (a) unmodeled
    VALUE forms (runtime [len]/[int(x)], fractional floats) that [eval_value] does not yet fold; (b) [GsDefer]
    — supported + emittable but undenoted until [run_cmd] fuel > 1.  [eval_value] growth closes only (a), and
    only on the DEFER-FREE fragment; full "supported ⟺ denotes" ALSO needs defer denotation.  TODAY [denotable_*]
    pins the EXACT denotable fragment as a decidable predicate.  (It is a CHARACTERIZATION/decidability result,
    NOT yet [supported_program ⟹ denotes] — [eval_value] is partial AND defer is unmodeled.) *)
Fixpoint denotable_body (b : list GoStmt) : bool :=
  match b with
  | [] => true
  | s :: rest =>
      match denote_stmt s with
      | None            => false
      | Some (_, true)  => forallb stmt_ok rest      (* terminator: the UNREACHABLE rest need only be SUPPORTED *)
      | Some (_, false) => denotable_body rest        (* continuer: the rest must itself be DENOTABLE *)
      end
  end.

Theorem denote_body_dec : forall b, denote_body b <> None <-> denotable_body b = true.
Proof.
  induction b as [|s rest IH]; simpl.
  - split; intro H; congruence.                                       (* [] : Some (CRet tt) <> None and true = true *)
  - destruct (denote_stmt s) as [[c term]|] eqn:Es.
    + destruct term.
      * destruct (forallb stmt_ok rest); split; intro H; congruence.   (* terminator: gates rest on supportedness *)
      * destruct (denote_body rest) eqn:Er; split; intro H.            (* continuer: gates rest on denotability (IH + Er) *)
        -- apply (proj1 IH); congruence.
        -- congruence.
        -- congruence.
        -- apply (proj2 IH) in H; congruence.
    + split; intro H; congruence.                                     (* denote_stmt s = None => both reject *)
Qed.

Definition denotable_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main" && denotable_body (prog_body p).

Theorem denote_program_dec : forall p, denote_program p <> None <-> denotable_program p = true.
Proof.
  intro p. unfold denote_program, denotable_program.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main"); simpl.
  - apply denote_body_dec.
  - split; intro H; [congruence | discriminate].
Qed.

(** ---- COMPLETENESS FRAGMENT — the [supported ⟹ denotes] direction for the PRINT/PRINTLN-of-DENOTABLE-ARGS
    fragment (AUTHORITY: [out_main_denotes] below; [print] as well as [println]).  NOT the whole supported output
    class — a print/println of a RUNTIME arg is supported but not [denotable_arg], so it does NOT denote
    ([out_boundary_runtime_undenoted]).  A print/println ARG denotes iff it EVALUATES and is PRINTABLE:
    [denotable_arg].  A `main` body of denotable-arg output statements + [return] ALWAYS denotes for the args
    [eval_value] folds: string CONSTANTS (literals, concatenations, identity string conversions, ASCII rune
    conversions [string(65)]) plus the folded integer / exact-float / bool CONSTANTS — NOT every supported string
    (a MULTI-BYTE rune conversion like `string(200)` is supported at classifier+gate but eval-partial, so NOT
    [denotable_arg]; the FULL supported-but-absent boundary is pinned by [runeconv_multibyte_boundary]).
    ([gosem_strlit_*] demos string literals; [println_main_denotes_mixed] a mixed string-literal+int-const
    program.)  [denotable_arg] is EXACTLY the per-arg denotation condition, so this is the converse OUTRIGHT on
    that fragment.  [denotable_supported] pins denotable ⊆ supported; the inclusion is STRICT (a runtime
    blank-assign is supported but not denotable) — the gap covering BOTH eval-partial forms (eval-growth closes
    these) AND [GsDefer] (supported + emittable, undenoted until [run_cmd] fuel > 1, which eval-growth never touches). *)
Definition denotable_arg (e : GExpr) : bool :=
  match eval_value e with Some _ => printable_arg_ok e | None => false end.

Lemma denotable_arg_eval : forall e, denotable_arg e = true -> eval_value e <> None.
Proof. intros e H Hn. unfold denotable_arg in H. rewrite Hn in H. discriminate. Qed.

Lemma denotable_arg_printable : forall e, denotable_arg e = true -> printable_arg_ok e = true.
Proof. intros e H. unfold denotable_arg in H. destruct (eval_value e); [exact H | discriminate]. Qed.

(** String CONCATENATION and CONVERSIONS DENOTE (the [eval_value] folds are in [eval_value_good]; these pin the
    stronger [denotable_arg] — evaluable AND printable): [`"a" + "b"`], the ASCII rune [`string(65)`], the
    identity [`string("a"+"b")`]. *)
Example denotable_arg_str_concat : denotable_arg (EBn BAdd (EStr "a") (EStr "b")) = true.
Proof. vm_compute. reflexivity. Qed.
Example denotable_arg_runeconv_ascii :
  denotable_arg (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = true.
Proof. vm_compute. reflexivity. Qed.

(** BOUNDARY PIN (keeps the converse EXACT — pins the FULL state, not just non-denotability): a MULTI-BYTE rune
    [`string(200)`] (UTF-8 = 2 bytes — [eval_str] folds only [0,127]) is SUPPORTED at the classifier AND the gate
    ([ptype] = [PtStr], [printable_arg_ok], so [println(string(200))] is a [supported_program]) yet ABSENT
    ([eval_value] = [None], so the program does NOT denote).  Pinning support+absence TOGETHER stops the boundary
    from silently sliding to "rejected" (if [ptype] dropped it) or "wrong" (if [eval] folded it).  Until
    multi-byte rune encoding is modelled, these stay OUTSIDE the denoted fragment, faithfully absent. *)
Definition runeconv_mb : GExpr := ECall (EId (mkIdent "string" eq_refl)) [EInt 200].
Definition runeconv_mb_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb]); GsReturn].
Example runeconv_multibyte_boundary :
  ptype runeconv_mb = Some PtStr                  (* SUPPORTED at the classifier (a valid [PtStr]) *)
  /\ printable_arg_ok runeconv_mb = true          (* ... and printable *)
  /\ supported_program runeconv_mb_prog = true    (* ... so [println(string(200))] IS a supported program *)
  /\ eval_value runeconv_mb = None                (* yet ABSENT: the multi-byte rune is not folded *)
  /\ denote_program runeconv_mb_prog = None.      (* ... so the SUPPORTED program does NOT denote (faithful-or-absent) *)
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma eval_args_denotable : forall args, forallb denotable_arg args = true -> eval_args args <> None.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [discriminate|].
  apply andb_true_iff in H as [Ha Hrest]. specialize (IH Hrest).
  pose proof (denotable_arg_eval a Ha) as Hva.
  destruct (eval_value a); [|exfalso; apply Hva; reflexivity].
  destruct (eval_args rest); [discriminate | exfalso; apply IH; reflexivity].
Qed.

Lemma forallb_denotable_printable : forall args,
  forallb denotable_arg args = true -> forallb printable_arg_ok args = true.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [reflexivity|].
  apply andb_true_iff in H as [Ha Hrest]. rewrite (denotable_arg_printable a Ha), (IH Hrest). reflexivity.
Qed.

(** THE CONVERSE AUTHORITY — [supported ⟹ denotes] on the PRINT/PRINTLN-of-DENOTABLE-ARGS fragment.  A
    print/println arg denotes iff it EVALUATES + is PRINTABLE ([denotable_arg]).  [out_call pr]: [println]
    (pr=true) / [print] (pr=false) — the gate admits both ([stmt_call_ok]), and [print] denotes identically with
    the [COut] flag FALSE.  ⚠ This is a FRAGMENT, NOT the whole supported output class — a print/println of a
    RUNTIME arg ([println(len([]int{1}))]) is SUPPORTED but NOT [denotable_arg], so it does NOT denote (pinned
    by [out_boundary_runtime_undenoted]); widening [eval_value] widens this fragment.  [println_main_denotes]
    below is the all-[println] COROLLARY. *)
Definition out_call (pr : bool) (args : list GExpr) : GExpr :=
  if pr then ECall (EId (mkIdent "println" eq_refl)) args
        else ECall (EId (mkIdent "print" eq_refl)) args.
Fixpoint out_main_body (stmts : list (bool * list GExpr)) : list GoStmt :=
  match stmts with
  | [] => [GsReturn]
  | (pr, args) :: rest => GsExprStmt (out_call pr args) :: out_main_body rest
  end.
Lemma expr_stmt_ok_out_denotable : forall f args,
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb denotable_arg args = true ->
  expr_stmt_ok (ECall (EId f) args) = true.
Proof.
  intros f args Hf Hargs. cbn [expr_stmt_ok stmt_call_ok].
  destruct Hf as [Hf|Hf]; rewrite Hf; cbn; rewrite (forallb_denotable_printable args Hargs); reflexivity.
Qed.
(** A print/println of denotable args denotes — as a CONTINUER ([Some (_, false)]): the shape [denotable_body]
    consumes when it is followed by more statements. *)
Lemma denote_out_denotable : forall f args,
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb denotable_arg args = true ->
  exists c, denote_stmt (GsExprStmt (ECall (EId f) args)) = Some (c, false).
Proof.
  intros f args Hf Hargs. cbn [denote_stmt].
  rewrite (expr_stmt_ok_out_denotable f args Hf Hargs).
  destruct Hf as [Hf|Hf]; rewrite Hf; cbn;
    (destruct (eval_args args) as [vs|] eqn:Ea;
      [ eexists; reflexivity | exfalso; exact (eval_args_denotable args Hargs Ea) ]).
Qed.
Lemma denote_out_call_denotable : forall pr args,
  forallb denotable_arg args = true ->
  exists c, denote_stmt (GsExprStmt (out_call pr args)) = Some (c, false).
Proof.
  intros pr args Hargs. destruct pr; cbn [out_call].
  - exact (denote_out_denotable (mkIdent "println" eq_refl) args (or_introl eq_refl) Hargs).
  - exact (denote_out_denotable (mkIdent "print" eq_refl) args (or_intror eq_refl) Hargs).
Qed.
Lemma out_main_denotable : forall stmts,
  forallb (fun s => forallb denotable_arg (snd s)) stmts = true -> denotable_body (out_main_body stmts) = true.
Proof.
  induction stmts as [|[pr args] rest IH]; intro H.
  - reflexivity.
  - cbn in H. apply andb_true_iff in H as [Hargs Hrest]. cbn [out_main_body].
    destruct (denote_out_call_denotable pr args Hargs) as [c Hc].
    cbn [denotable_body]. rewrite Hc. exact (IH Hrest).
Qed.
Theorem out_main_denotes : forall stmts,
  forallb (fun s => forallb denotable_arg (snd s)) stmts = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) (out_main_body stmts)) <> None.
Proof.
  intros stmts H. apply (proj2 (denote_program_dec _)).
  cbn [denotable_program prog_pkg prog_body proj1_sig]. exact (out_main_denotable stmts H).
Qed.

Corollary denotable_supported : forall p, denotable_program p = true -> supported_program p = true.
Proof. intros p H. apply gosem_sound, (proj2 (denote_program_dec p)), H. Qed.

(** Grounding: a multi-statement `func main(){ println("a"); println("b"); return }` is denotable. *)
Definition gosem_strlit_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "a"]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "b"]); GsReturn].
Example gosem_strlit_denotable : denotable_program gosem_strlit_prog = true.   Proof. reflexivity. Qed.

(** [println_main_denotes] — the all-[println] COROLLARY of [out_main_denotes]: a `main` body of N
    [println(args)] (every arg [denotable_arg]) + [return] denotes.  [println_main_body] is [out_main_body] with
    every flag [true] ([println_main_body_out]); kept for the [gosem_strlit] / `_runs` demos. *)
Fixpoint println_main_body (arglists : list (list GExpr)) : list GoStmt :=
  match arglists with
  | [] => [GsReturn]
  | args :: rest => GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) args) :: println_main_body rest
  end.
Lemma println_main_body_out : forall arglists,
  println_main_body arglists = out_main_body (map (fun a => (true, a)) arglists).
Proof.
  induction arglists as [|args rest IH]; [reflexivity|].
  cbn [println_main_body out_main_body map out_call]. rewrite IH. reflexivity.
Qed.
Lemma denotable_arglists_out : forall arglists,
  forallb (forallb denotable_arg) arglists = true ->
  forallb (fun s => forallb denotable_arg (snd s)) (map (fun a => (true, a)) arglists) = true.
Proof.
  induction arglists as [|args rest IH]; [reflexivity|].
  cbn; intro H; apply andb_true_iff in H as [Ha Hr]; rewrite Ha; cbn; exact (IH Hr).
Qed.
Theorem println_main_denotes : forall arglists,
  forallb (forallb denotable_arg) arglists = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) (println_main_body arglists)) <> None.
Proof.
  intros arglists H. rewrite (println_main_body_out arglists).
  exact (out_main_denotes _ (denotable_arglists_out arglists H)).
Qed.

(** Coverage (the all-[println] corollary): MIXED evaluable args — `println("a"); println(int64(3)); return`
    denotes (a string literal AND an integer-constant conversion), not just strings. *)
Example println_main_denotes_mixed :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    (println_main_body [[EStr "a"]; [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]]])) <> None.
Proof. apply println_main_denotes. reflexivity. Qed.

(** Coverage: a MIXED print+println body denotes — [println("a"); print(int64(3)); return]. *)
Example out_main_denotes_mixed :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    (out_main_body [(true, [EStr "a"]); (false, [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]])])) <> None.
Proof. apply out_main_denotes. reflexivity. Qed.
(** BOUNDARY — the fragment is NOT the whole supported output class: [println(len([]int{1}))] is SUPPORTED
    (valid Go) yet its arg is a RUNTIME [len] (NOT [denotable_arg]), so the program does NOT denote. *)
Definition out_runtime_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                       [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]); GsReturn].
Example out_boundary_runtime_undenoted :
  supported_program out_runtime_prog = true
  /\ denotable_arg (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) = false
  /\ denote_program out_runtime_prog = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ---- GENERAL statement-compositional CONVERSE: a body whose EVERY statement INDIVIDUALLY denotes is a
    denotable body, so its `main` DENOTES.  This GENERALIZES [out_main_denotes] (the pure output-call fragment)
    to ALL denoting statement forms interleaved — [return] / [panic] terminators, blank constant-assignment,
    and print·println — INCLUDING a terminator followed by (supported) DEAD code, which [out_main_body] cannot
    even express.  It is SUFFICIENT, not necessary: a terminator's UNREACHABLE rest need only be SUPPORTED
    ([denotable_body]'s terminator arm gates on [forallb stmt_ok rest]), so a denotable body may carry a
    non-denotable-but-supported dead tail.  Rests on [denote_stmt_sound] (via [stmt_denotable ⟹ stmt_ok]).
    STILL CONDITIONAL on [stmt_denotable], NOT full [supported_program] — which also admits [GsDefer] (undenoted
    until [run_cmd] fuel > 1) and runtime args slice 1 cannot evaluate (the boundary above).  [eval_value] growth
    closes ONLY the runtime-arg gap and ONLY on the defer-free fragment; full [stmt_denotable = stmt_ok] ALSO
    needs defer denotation. *)
Definition stmt_denotable (s : GoStmt) : bool :=
  match denote_stmt s with Some _ => true | None => false end.

Lemma stmt_denotable_ok : forall s, stmt_denotable s = true -> stmt_ok s = true.
Proof.
  intros s H. unfold stmt_denotable in H.
  destruct (denote_stmt s) eqn:Es; [|discriminate H].
  apply denote_stmt_sound. rewrite Es. discriminate.
Qed.

Lemma forallb_stmt_denotable_ok : forall b,
  forallb stmt_denotable b = true -> forallb stmt_ok b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|]. cbn [forallb]. intro H.
  apply andb_true_iff in H as [Hs Hr]. rewrite (stmt_denotable_ok s Hs). exact (IH Hr).
Qed.

Lemma denotable_body_of_stmts : forall b,
  forallb stmt_denotable b = true -> denotable_body b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|]. cbn [forallb denotable_body]. intro H.
  apply andb_true_iff in H as [Hs Hrest]. unfold stmt_denotable in Hs.
  destruct (denote_stmt s) as [[c term]|] eqn:Es; [|discriminate Hs].
  destruct term.
  - exact (forallb_stmt_denotable_ok rest Hrest).   (* terminator: unreachable rest need only be SUPPORTED *)
  - exact (IH Hrest).                                (* continuer: rest must itself be DENOTABLE *)
Qed.

Theorem denotable_stmts_main_denotes : forall b,
  forallb stmt_denotable b = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) b) <> None.
Proof.
  intros b H. apply (proj2 (denote_program_dec _)).
  cbn [denotable_program prog_pkg prog_body proj1_sig]. exact (denotable_body_of_stmts b H).
Qed.

(** Coverage — a MIXED body [out_main_denotes] CANNOT express: [println("a"); _ = int64(3); panic("boom");
    println("dead")] interleaves a continuer output call, a blank constant-assignment, a [panic] TERMINATOR,
    and a SUPPORTED dead tail — and DENOTES by APPLYING the general converse (not a black-box compute). *)
Example denotable_stmts_mixed_denotes :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "a"]);
     GsBlankAssign (ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]);
     GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "dead"])]) <> None.
Proof. apply denotable_stmts_main_denotes. reflexivity. Qed.

(** TIGHTNESS — WHERE the general converse's "sufficient, not necessary" comes from.  [stmt_terminates] just
    READS [denote_stmt]'s terminator flag (NOT a second authority).  On a TERMINATOR-FREE body the compositional
    converse is EXACT (an iff): the body denotes iff EVERY statement individually denotes.  The ONLY slack is the
    terminator escape — a terminator's UNREACHABLE rest need only be SUPPORTED, so a denotable body may carry an
    undenotable-but-supported DEAD tail (pinned by [denotable_body_escapes_stmt_denotable] below). *)
Definition stmt_terminates (s : GoStmt) : bool :=
  match denote_stmt s with Some (_, true) => true | _ => false end.

Lemma denotable_body_terminator_free_necessary : forall b,
  forallb (fun s => negb (stmt_terminates s)) b = true ->
  denotable_body b = true -> forallb stmt_denotable b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|].
  cbn [forallb denotable_body]. intros Htf Hden.
  apply andb_true_iff in Htf as [Hs Hrest]. apply negb_true_iff in Hs. unfold stmt_terminates in Hs.
  destruct (denote_stmt s) as [[c term]|] eqn:Es.
  - destruct term; [discriminate Hs|].                       (* terminator excluded by [terminator_free] *)
    apply andb_true_intro. split; [unfold stmt_denotable; rewrite Es; reflexivity | exact (IH Hrest Hden)].
  - discriminate Hden.                                       (* [denote_stmt s = None] => [denotable_body] false *)
Qed.

Corollary denotable_body_terminator_free_iff : forall b,
  forallb (fun s => negb (stmt_terminates s)) b = true ->
  (denotable_body b = true <-> forallb stmt_denotable b = true).
Proof.
  intros b Htf. split;
    [exact (denotable_body_terminator_free_necessary b Htf) | exact (denotable_body_of_stmts b)].
Qed.

(** The escape is REAL (the converse is genuinely sufficient-not-necessary): [return; defer println("x")] is a
    DENOTABLE body ([return] terminates; the [defer] is a SUPPORTED dead tail) whose [defer] does NOT denote, so
    [denotable_body = true] while [forallb stmt_denotable = false].  This body HAS a terminator — exactly why the
    iff above does not apply to it. *)
Example denotable_body_escapes_stmt_denotable :
  denotable_body [GsReturn; GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "x"])] = true
  /\ forallb stmt_denotable [GsReturn; GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "x"])] = false.
Proof. split; reflexivity. Qed.

(** ---- EXECUTABLE TOTALITY: every GoSem denotation RUNS to an Outcome — it never gets STUCK under [run_cmd],
    even with MINIMAL fuel 1.  Slice-1 denotations are [COut]/[CRet]/[CPan] chains with NO [CDfr] (defer is not
    modelled yet), so [cmd.v]'s [go] accumulates an EMPTY deferred list and [run_defers] returns immediately.
    [denote_program_runs] proves the DENOTATION->EXECUTION link: [denote_program p = Some c -> run_cmd 1 c w <>
    None] — a DENOTED program ([Cmd]) RUNS to an [Outcome].  (It assumes the program DENOTES; it does NOT prove
    supported ⟹ denotes in GENERAL — that converse is partial, see [denote_program_dec] / [out_main_denotes]
    (the authority; its all-[println] corollary is [println_main_denotes]).
    Composed with [denote_program_dec], a DENOTABLE program denotes-and-runs.)  GoSem's executable semantics is TOTAL on
    what it denotes.  ([no_defer] — the straight-line predicate this rests on — now lives in cmd.v, shared with
    the cmd_unified.v bridge.) *)
Lemma cbind_no_defer : forall (c : Cmd unit) (k : unit -> Cmd unit),
  no_defer c = true -> (forall u, no_defer (k u) = true) -> no_defer (cbind c k) = true.
Proof.
  intro c; induction c as [a|b xs c' IHc'|v|d c' IHc'] using Cmd_rect';
    intros k Hc Hk; cbn [cbind no_defer] in *.
  - apply Hk.
  - apply IHc'; [exact Hc | exact Hk].
  - reflexivity.
  - discriminate Hc.
Qed.

Lemma denote_stmt_no_defer : forall s c b, denote_stmt s = Some (c, b) -> no_defer c = true.
Proof.
  intros s c b H. destruct s as [e| |ev|be|de]; cbn [denote_stmt] in H.
  - destruct (expr_stmt_ok e); [|discriminate H].
    destruct e as [ | | | | | | | fe fargs | | | | | | ]; try discriminate H.
    destruct fe as [ fi | | | | | | | | | | | | | ]; try discriminate H.
    destruct (String.eqb (proj1_sig fi) "panic").
    + destruct fargs as [|a [|? ?]]; try discriminate H.
      destruct (eval_value a); [|discriminate H]. inversion H; subst; reflexivity.
    + destruct (eval_args fargs); [|discriminate H]. inversion H; subst; reflexivity.
  - inversion H; subst; reflexivity.
  - discriminate H.
  - destruct (svalue be); [|discriminate H]. destruct (eval_value be); [|discriminate H].
    inversion H; subst; reflexivity.
  - discriminate H.   (* GsDefer: [denote_stmt] = None *)
Qed.

Lemma denote_body_no_defer : forall b c, denote_body b = Some c -> no_defer c = true.
Proof.
  induction b as [|s rest IH]; cbn [denote_body]; intros c H.
  - inversion H; subst; reflexivity.
  - destruct (denote_stmt s) as [[cs term]|] eqn:Es; [|discriminate H]. destruct term.
    + destruct (forallb stmt_ok rest); [|discriminate H]. inversion H; subst.
      exact (denote_stmt_no_defer s c true Es).
    + destruct (denote_body rest) as [k|] eqn:Er; [|discriminate H]. inversion H; subst.
      apply cbind_no_defer; [exact (denote_stmt_no_defer s cs false Es) | intro u; exact (IH k eq_refl)].
Qed.

Lemma no_defer_go_nil : forall (c : Cmd unit) w, no_defer c = true -> snd (go c w) = nil.
Proof.
  intro c; induction c as [a|b xs c' IHc'|v|d c' IHc'] using Cmd_rect';
    intros w Hc; cbn [go no_defer] in *.
  - reflexivity.
  - apply IHc'; exact Hc.
  - reflexivity.
  - discriminate Hc.
Qed.

Lemma no_defer_run : forall (c : Cmd unit) w, no_defer c = true -> run_cmd 1 c w <> None.
Proof.
  intros c w Hc. unfold run_cmd.
  pose proof (no_defer_go_nil c w Hc) as Hnil.
  destruct (go c w) as [oc ds]. cbn [snd] in Hnil. subst ds.
  cbn [run_defers]. destruct (oc_unit oc); discriminate.
Qed.

Theorem denote_program_runs : forall p c w, denote_program p = Some c -> run_cmd 1 c w <> None.
Proof.
  intros p c w H. apply (no_defer_run c w). unfold denote_program in H.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main"); [|discriminate H].
  exact (denote_body_no_defer (prog_body p) c H).
Qed.

(** Capstone: a DENOTED print/println-of-denotable-args program not only DENOTES but RUNS to an Outcome —
    composing [out_main_denotes] with [denote_program_runs].  [println_main_runs] is the all-[println] corollary. *)
Theorem out_main_runs : forall stmts w,
  forallb (fun s => forallb denotable_arg (snd s)) stmts = true ->
  match denote_program (mkProgram (mkIdent "main" eq_refl) (out_main_body stmts)) with
  | Some c => run_cmd 1 c w <> None
  | None => False
  end.
Proof.
  intros stmts w H.
  destruct (denote_program (mkProgram (mkIdent "main" eq_refl) (out_main_body stmts))) as [c|] eqn:Hd.
  - exact (denote_program_runs _ c w Hd).
  - exact (out_main_denotes stmts H Hd).
Qed.
Theorem println_main_runs : forall arglists w,
  forallb (forallb denotable_arg) arglists = true ->
  match denote_program (mkProgram (mkIdent "main" eq_refl) (println_main_body arglists)) with
  | Some c => run_cmd 1 c w <> None
  | None => False
  end.
Proof.
  intros arglists w H. rewrite (println_main_body_out arglists).
  exact (out_main_runs _ w (denotable_arglists_out arglists H)).
Qed.

(** ---- A load-bearing end-to-end witness with REAL OBSERVABLE OUTPUT: a supported
    `func main(){ println("hi"); return }` denotes to a [Cmd unit] and RUNS through cmd.v's authoritative
    [run_cmd] to a World whose output trace records the `println` — FAITHFULLY, the very [w_log true ["hi"]]
    the model's own [println] produces. *)
Definition gosem_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]); GsReturn].
Example gosem_demo_denotes : denote_program gosem_demo_prog
                           = Some (COut true (anyt TString "hi" :: nil) (CRet tt)).
Proof. vm_compute. reflexivity. Qed.
Example gosem_demo_runs : forall w,
  match denote_program gosem_demo_prog with
  | Some c => run_cmd 5 c w
  | None => None
  end = Some (ORet tt (w_log true (anyt TString "hi" :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

(** REGRESSION (P0, Codex 2026-06-30): [return] STOPS the body — a NON-tail return's successors do NOT run.
    `func main(){ return; println("after") }` is SUPPORTED (Go compiles it), yet prints NOTHING; GoSem denotes
    it to a no-output [CRet], NOT to running the [println].  [run_cmd] leaves the world UNCHANGED. *)
Definition gosem_return_stops_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsReturn; GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "after"])].
Example gosem_return_stops_no_output : forall w,
  match denote_program gosem_return_stops_prog with
  | Some c => run_cmd 5 c w
  | None => None
  end = Some (ORet tt w).   (* w UNCHANGED — no [w_log]; the [println] after [return] never runs *)
Proof. intro w. vm_compute. reflexivity. Qed.

(** UNIVERSAL TERMINATOR PROPERTY (consolidates the old undenotable-successor witnesses, Codex 2026-06-30):
    a TERMINATOR ([return] / a denoted [panic]) must NOT depend on its UNREACHABLE successors DENOTING — only on
    their SUPPORTEDNESS.  Stated for ALL [s]/[c]/[rest]: whenever [denote_stmt] marks [s] terminating
    ([Some (c, true)]), [denote_body] emits [c] and gates the rest ONLY on [forallb stmt_ok rest], NEVER on
    [denote_body rest].  A UNIVERSAL lemma (over ALL [rest]), NOT a fixture keyed to one specific
    supported-but-undenotable successor — so it never erodes.  Such successors PERSIST, not vanish: [GsDefer]
    is supported + emittable yet undenoted (until [run_cmd] fuel > 1), and a runtime-arg statement is supported
    yet eval-partial; the lemma holds for EVERY [rest] regardless of how [eval_value] grows. *)
Lemma denote_body_terminator_ignores_succ : forall s c rest,
  denote_stmt s = Some (c, true) ->
  denote_body (s :: rest) = (if forallb stmt_ok rest then Some c else None).
Proof. intros s c rest H. cbn [denote_body]. rewrite H. reflexivity. Qed.

(** The two terminators the lemma covers (so it is not vacuous): bare [return] -> [CRet tt], and a denoted
    [panic("x")] -> [CPan (anyt TString "x")], each with the [true] terminates-flag. *)
Example denote_stmt_return_terminates : denote_stmt GsReturn = Some (CRet tt, true).
Proof. reflexivity. Qed.
Example denote_stmt_panic_terminates :
  denote_stmt (GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"]))
  = Some (CPan (anyt TString "x"), true).
Proof. vm_compute. reflexivity. Qed.

(** A denoted [panic] TERMINATES end-to-end: `func main(){ panic("x") }` denotes to a [CPan] and [run_cmd]
    PANICS with [anyt TString "x"]. *)
Definition gosem_panic_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"])].
Example gosem_panic_demo_runs : forall w,
  match denote_program gosem_panic_demo_prog with Some c => run_cmd 5 c w | None => None end
  = Some (OPanic (anyt TString "x") w).
Proof. intro w. vm_compute. reflexivity. Qed.

(** REGRESSION (P0, Codex 2026-06-30): a RUNTIME blank-assign Go PANICS on — `_ = 1 / len([]int{})`
    ([len] of an empty slice = 0, a runtime divide-by-zero) — is SUPPORTED ([GoTypes] admits runtime division;
    the div-by-zero is GoSem's concern), but slice-1 [eval_value] does NOT model it, so GoSem leaves it
    UN-denoted ([denote_program = None]) rather than giving it the WRONG (silent, no-panic) behavior.  Once the
    evaluator models runtime panics this becomes a [CPan]; until then it is honestly absent, not wrong. *)
Definition gosem_runtime_blank_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EBn BDiv (EInt 1)
                              (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []]))].
Example gosem_runtime_blank_undenoted : denote_program gosem_runtime_blank_prog = None.
Proof. reflexivity. Qed.

(** BOUNDARY — a [defer <call>] statement is SUPPORTED (emittable) but NOT YET denoted (faithful-or-ABSENT): its
    [cmd.v] denotation is a [CDfr], which needs [run_cmd] fuel > 1, and GoSem's execution/safety story is fuel-1
    (slice 1 denotes [no_defer] only).  So `func main(){ defer println("bye"); return }` is supported yet does
    NOT denote — the RIGHT behavior is (not yet) NONE, never a WRONG one. *)
Definition gosem_defer_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "bye"]); GsReturn].
Example gosem_defer_undenoted : denote_program gosem_defer_prog = None.
Proof. reflexivity. Qed.
Example gosem_defer_not_denotable : denotable_program gosem_defer_prog = false.  (* the decidable predicate agrees *)
Proof. reflexivity. Qed.

(** ---- [eval_value] FOLD TABLE (grouped regression) ---- each LISTED row's constant [eval_value] denotes to
    the paired value, pinned as one [(expr, value)] list.  A BREADTH sample, NOT a completeness claim: some
    printable supported constants are honestly ABSENT (e.g. the multi-byte rune [string(200)], pinned separately
    by [runeconv_multibyte_boundary]).  The listed rows exercise integer conversions/arith/complement (boxing
    the model's EXACT value per signedness/width; [^int64(5)] = [-6]), exact-integer FLOAT constants (the UNIQUE
    canonical binary64/32), constant BOOLs (the 6 numeric or STRING-constant comparisons — order via the model's
    [str_*] — combined by [==]/[!=]/[&&]/[||]/[!] + the identity [bool(x)]), and string CONSTANTs (literal /
    concat / ASCII-rune / identity string conv: ["a"+"b"] = ["ab"] byte append, [string(65)] = ["A"] ([0,127]
    arm), high-byte "\200">"\100" pins UNSIGNED order).  The [box_*]/[ptype] FAIL-CLOSED pins (out-of-range
    boxing / ill-typed compare / uint underflow) are separate below — those lock the GATE boundary, not a fold. *)
Definition eval_value_good : list (GExpr * GoAny) :=
  [ (ECall (EId (mkIdent "int64" eq_refl)) [EInt 3], anyt TI64 (i64wrap 3))
  ; (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 5], anyt TU8 (u8wrap 5))
  ; (ECall (EId (mkIdent "int8" eq_refl)) [EInt 127], anyt TI8 (i8wrap 127))
  ; (EBn BAdd (EInt 1) (EInt 2), anyt TInt64 (intwrap 3))
  ; (EUn UXor (ECall (EId (mkIdent "int64" eq_refl)) [EInt 5]), anyt TI64 (i64wrap (-6)))   (* ^int64(5) = bitwise NOT = -6 *)
  ; (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3], anyt TUint (uint_lit 3 eq_refl))
  ; (EBn BAdd (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "uint" eq_refl)) [EInt 4]), anyt TUint (uint_lit 7 eq_refl))
  ; (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3], anyt TFloat64 (renorm 53 1024 (sf_of_Z 3)))
  ; (ECall (EId (mkIdent "float32" eq_refl)) [EInt 5], anyt TFloat32 (f32_lit (sf_of_Z 5)))
  ; (ECall (EId (mkIdent "len" eq_refl)) [EStr "abc"], anyt TInt64 (intwrap 3))
  ; (EBn BAdd (EStr "a") (EStr "b"), anyt TString "ab")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EInt 65], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EStr "A"], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")], anyt TString "ab")
  ; (EBn BEq (EInt 1) (EInt 1), anyt TBool true)
  ; (EBn BLt (EInt 3) (EInt 5), anyt TBool true)
  ; (EBn BEq (EInt 1) (EInt 2), anyt TBool false)
  ; (EBn BEq (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]), anyt TBool true)
  ; (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)), anyt TBool true)
  ; (EBn BLOr (EBn BEq (EInt 1) (EInt 2)) (EBn BLt (EInt 3) (EInt 5)), anyt TBool true)
  ; (EUn UNot (EBn BEq (EInt 1) (EInt 2)), anyt TBool true)
  ; (EBn BEq (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)), anyt TBool true)
  ; (EUn UNot (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 3))), anyt TBool true)
  ; (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)], anyt TBool true)
  ; (EBn BEq (EStr "a") (EStr "a"), anyt TBool true)
  ; (EBn BNe (EStr "a") (EStr "b"), anyt TBool true)
  ; (EBn BLt (EStr "a") (EStr "b"), anyt TBool true)
  ; (EBn BLt (EStr "b") (EStr "a"), anyt TBool false)
  ; (EBn BLe (EStr "a") (EStr "a"), anyt TBool true)
  ; (EBn BGt (EStr "b") (EStr "a"), anyt TBool true)
  ; (EBn BLt (EStr "a") (EStr "ab"), anyt TBool true)
  ; (EBn BGe (EStr "b") (EStr "a"), anyt TBool true)
  ; (EBn BGe (EStr "a") (EStr "b"), anyt TBool false)
  ; (EBn BGt (EStr (String (Ascii.ascii_of_nat 200) EmptyString)) (EStr (String (Ascii.ascii_of_nat 100) EmptyString)), anyt TBool true)
  ; (EBn BEq (EBn BAdd (EStr "a") (EStr "b")) (EStr "ab"), anyt TBool true)
  ; (EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) (EStr "A"), anyt TBool true)
  ; (EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")]) (EStr "ab"), anyt TBool true)
  ].
Example eval_value_good_ok :
  map (fun p => eval_value (fst p)) eval_value_good = map (fun p => Some (snd p)) eval_value_good.
Proof. vm_compute. reflexivity. Qed.

(** BREADTH run-witness: every row of the fold table also RUNS end-to-end — [println(e); return] denotes and
    EXECUTES through cmd.v's authoritative [run_cmd] to the world logging the EXACT model value [v] the fold
    produced ([w_log true [v]]).  MANIFEST-GATED (in [gosem_trust_surface]).  NOTE this theorem is quantified
    OVER the table, so it does NOT by itself pin WHICH behaviors are present (a shrunk table still proves it);
    the required behavior CATEGORIES are pinned STANDALONE, table-independently, by [gosem_category_coverage]
    below. *)
Definition println_prog (e : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [e]); GsReturn].
Example eval_value_good_runs : forall w,
  map (fun p => match denote_program (println_prog (fst p)) with
                | Some c => run_cmd 5 c w | None => None end) eval_value_good
  = map (fun p => Some (ORet tt (w_log true (snd p :: nil) w))) eval_value_good.
Proof. intro w. vm_compute. reflexivity. Qed.

(** REQUIRED-CATEGORY COVERAGE as a TYPED obligation.  [runs_to e v] = [println(e); return] denotes and runs
    through cmd.v's [run_cmd] to the world logging [v].  The RECORD TYPE [GoSemRequiredCategoryCoverage] fixes,
    in its FIELD TYPES, the EXACT five behavior categories the model must exhibit end-to-end (int CONVERSION,
    exact FLOAT, numeric-compare BOOL, string CONCAT, string-compare-of-concat BOOL).  [gosem_category_coverage]
    inhabits that type, so it can be built ONLY by discharging ALL five with the stated programs+values: a
    category cannot be dropped without editing this typed STATEMENT (the record), never silently by convention.
    Table-INDEPENDENT (no reference to [eval_value_good]).  (String-literal println / return / panic behaviors
    are pinned separately by [gosem_demo_runs] / [gosem_return_stops_no_output] / [gosem_panic_demo_runs].) *)
Definition runs_to (e : GExpr) (v : GoAny) : Prop :=
  forall w, match denote_program (println_prog e) with
            | Some c => run_cmd 5 c w | None => None end = Some (ORet tt (w_log true (v :: nil) w)).
Record GoSemRequiredCategoryCoverage : Prop := {
  rc_conv      : runs_to (ECall (EId (mkIdent "int64"   eq_refl)) [EInt 3]) (anyt TI64 (i64wrap 3));
  rc_float     : runs_to (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (anyt TFloat64 (renorm 53 1024 (sf_of_Z 3)));
  rc_bool      : runs_to (EBn BEq (EInt 1) (EInt 1)) (anyt TBool true);
  rc_concat    : runs_to (EBn BAdd (EStr "a") (EStr "b")) (anyt TString "ab");
  rc_concatcmp : runs_to (EBn BEq (EBn BAdd (EStr "a") (EStr "b")) (EStr "ab")) (anyt TBool true);
}.
Definition gosem_category_coverage : GoSemRequiredCategoryCoverage.
Proof. constructor; intro w; vm_compute; reflexivity. Qed.
Check gosem_category_coverage : GoSemRequiredCategoryCoverage.   (* the typed obligation, made explicit *)

(** FAIL-CLOSED pins (LOAD-BEARING, lock the GATE boundary — NOT folds): out-of-range boxing is [None]
    ([mk_uint]/[box_*] never carry a [*wrap]-mangled value); a mixed-WIDTH ill-typed compare [int64(1)==int32(1)]
    has [ptype = None] so [eval_bool]/[eval_value] fail closed (no fabricated [true]); the uint underflow
    [uint(3)-uint(5)] has [ptype = None] ⇒ [printable_arg_ok = false] ⇒ never emitted (the ROOT rejection, not
    the eval backstop).  A supported [ptype = Some PtBool] pins the two string/bool categories are ADMITTED. *)
Definition mixed_width_cmp : GExpr :=
  EBn BEq (ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "int32" eq_refl)) [EInt 1]).
Definition uint_underflow_e := EBn BSub (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "uint" eq_refl)) [EInt 5]).
Example eval_value_failclosed :
  box_float GTFloat64 9007199254740993 = None
  /\ box_int GTU8 300 = None
  /\ ptype mixed_width_cmp = None /\ eval_bool mixed_width_cmp = None /\ eval_value mixed_width_cmp = None
  /\ ptype uint_underflow_e = None /\ printable_arg_ok uint_underflow_e = false
  /\ ptype (EBn BEq (EStr "a") (EStr "a")) = Some PtBool
  /\ ptype (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)]) = Some PtBool.
Proof. repeat split; vm_compute; reflexivity. Qed.
(** faithful-or-absent: every supported-but-unfoldable form evaluates to [None], never a wrong value — a bool
    with a runtime [len] operand (even under [&&]), a MULTI-BYTE rune string operand ([string(200)], UTF-8 > 1
    byte — ASCII-rune/string-source/concat operands DO fold), an untyped const past the
    default-[int] range, an out-of-range [uint] conversion, the uint underflow (backstop behind the gate), and
    a runtime slice [len]. *)
Definition eval_absent : list GExpr :=
  [ EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)
  ; EBn BLAnd (EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)) (EBn BEq (EInt 2) (EInt 2))
  ; EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 200]) (EStr "A")   (* MULTI-BYTE rune -> string absent (only [0,127] fold) *)
  ; EInt 2147483648
  ; ECall (EId (mkIdent "uint" eq_refl)) [EInt 4294967296]
  ; uint_underflow_e
  ; ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]] ].
Example eval_absent_none : forallb (fun e => match eval_value e with None => true | Some _ => false end) eval_absent = true.
Proof. vm_compute. reflexivity. Qed.

(** DENOTABILITY-DECISION witnesses: [denotable_program] (the decidable predicate of [denote_program_dec])
    agrees with whether the program denotes — TRUE for the denoting demos (`println("hi")`, the `return`-stops
    program), FALSE for the supported-but-undenoted runtime blank-assign `_ = 1/len([]int{})` and the
    supported-but-undenoted defer program (`gosem_defer_not_denotable`, above). *)
Example denotable_demo          : denotable_program gosem_demo_prog = true.            Proof. reflexivity. Qed.
Example denotable_return_stops  : denotable_program gosem_return_stops_prog = true.    Proof. reflexivity. Qed.
Example denotable_runtime_blank : denotable_program gosem_runtime_blank_prog = false.  Proof. reflexivity. Qed.

(** All five demo programs above are SUPPORTED (each is emittable Go); grouped so the gate is pinned once. *)
Example demo_progs_supported :
  forallb supported_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_panic_demo_prog;
     gosem_runtime_blank_prog; gosem_defer_prog] = true.
Proof. reflexivity. Qed.

(** GOSEM TRUST SURFACE — the EXPLICIT, bounded set of public GoSem results certified zero-axiom.  Bundling the
    proof terms into ONE constant makes a SINGLE [Print Assumptions] cover their whole transitive cones; the
    Docker manifest gate captures the report and FAILS on any axiom (rule 3, manifest empty).  This is a seal
    for exactly this surface, NOT a module-wide claim — a theorem not bundled here is not claimed zero-axiom;
    to certify one, ADD it to the tuple. *)
Definition gosem_trust_surface :=
  (gosem_sound, denote_program_dec, denotable_supported, out_main_denotes, println_main_denotes,
   denotable_stmts_main_denotes, denotable_body_terminator_free_iff,
   denote_program_runs, out_main_runs, println_main_runs,
   gosem_demo_runs, gosem_return_stops_no_output, gosem_panic_demo_runs,
   eval_value_good_ok, eval_value_good_runs, eval_value_failclosed, eval_absent_none,
   gosem_category_coverage).
Print Assumptions gosem_trust_surface.

(** ---- STRING-AUTHORITY PINS (gated): each of [str_cmp_op]'s six branches IS, by reflexivity, the FULLY
    QUALIFIED model constant [Fido.builtins.str_*] — so a fork that reroutes a branch breaks a pin and FAILS the
    build ([<=] = the model's [str_geb] with operands swapped).  Bundled into [gosem_string_authority_surface]
    so its [Print Assumptions] certifies the whole cone zero-axiom (the honest place for the "authority
    guarantee" claim); a fork that DIDN'T reroute a live branch would be dead code. *)
Example str_cmp_eq_model : str_cmp_op BEq = Some Fido.builtins.str_eqb.                     Proof. reflexivity. Qed.
Example str_cmp_ne_model : str_cmp_op BNe = Some Fido.builtins.str_neqb.                    Proof. reflexivity. Qed.
Example str_cmp_lt_model : str_cmp_op BLt = Some Fido.builtins.str_ltb.                     Proof. reflexivity. Qed.
Example str_cmp_le_model : str_cmp_op BLe = Some (fun s t => Fido.builtins.str_geb t s).    Proof. reflexivity. Qed.
Example str_cmp_gt_model : str_cmp_op BGt = Some Fido.builtins.str_gtb.                     Proof. reflexivity. Qed.
Example str_cmp_ge_model : str_cmp_op BGe = Some Fido.builtins.str_geb.                     Proof. reflexivity. Qed.
Definition gosem_string_authority_surface :=
  (str_cmp_eq_model, str_cmp_ne_model, str_cmp_lt_model, str_cmp_le_model, str_cmp_gt_model, str_cmp_ge_model).
Print Assumptions gosem_string_authority_surface.
