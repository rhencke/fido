(** ============================================================================
    GoAST — the ONE raw program representation.  The permanent root pairs an intrinsic module spec with a
    verified finite map of raw file ASTs (the map MAY be empty):

      GoProgram := { prog_module : ModuleSpec ; prog_files : fmap FilePath GoFileAST }

    [ModuleSpec] describes the GENERATED Go module itself — its import-path prefix ([ModulePath]) and its
    module-declared language version ([GoVersion]) — NOT ambient execution details (no GOOS/GOARCH/ABI/
    scheduler/point-release/architecture matrix; those stay operationally pinned, off the theorems).  It
    is NOT a TargetConfig.

    A [GoFileAST] is RAW top-level declarations only — nothing compiled.  It does NOT carry a package
    clause, a package identity, an entry-point flag, imports, symbols, or types: those are COMPILATION /
    TYPING RESULTS — package grouping and entry status by GoCompile, types by GoTypes (the one type
    authority) — derived over the whole path-indexed program.  There is no raw GoPackage tree and no typed
    AST: raw literals stay UNTYPED syntax.

    The one raw declaration today is [DMain body]: syntactically a `func main() { body }` declaration
    (zero parameters, no results) whose body is the existing [SPrintln] statements.  Whether that
    declaration is the UNIQUE entry point of its package is decided by GoCompile — MULTIPLE [DMain] in a
    file are representable precisely so GoCompile can reject a duplicate `main` exactly as Go would.  A
    file with NO declarations is representable (a valid file in a package whose `main` is elsewhere), and
    the EMPTY file map is representable (a valid module with a `go.mod` and no packages).

    No identifiers, calls, parameters, results, imports, arbitrary expressions/statements, user types,
    concurrency, or package clauses.  Anything else is UNREPRESENTABLE.
    ============================================================================ *)
From Stdlib Require Import NArith List String.
From Fido Require Import FilePath FMap ModulePath GoVersion Ints Floats Complexes.
Import ListNotations.

(** A raw expression is UNTYPED syntax: a boolean literal, an integer literal as an unsigned magnitude
    ([EInt]) optionally negated ([ENeg]), a STRING literal whose argument is the EXACT SEMANTIC BYTE
    SEQUENCE ([EString], a Rocq [string] = a list of [ascii] bytes — NOT source spelling, NOT an
    already-escaped literal, NOT Unicode scalars/code points), or an EXPLICIT integer conversion
    ([EIntConvert it e], the source spelling `<keyword it>(e)`, e.g. `int8(42)` / `uint64(...)` /
    `uint8(int(300))`), a FLOATING literal carrying an INTRINSIC finite-decimal semantic value ([EFloat d],
    a bounded canonical [DecimalFloat] — NOT source spelling / underscores / hex / capitalization / a rounded
    value), or an EXPLICIT float conversion ([EFloatConvert ft e], the source spelling `float32(e)` /
    `float64(e)`).  [EIntConvert]'s target is the INTRINSIC [IntegerType] and [EFloatConvert]'s the intrinsic
    [FloatType] — never a raw type-name string.  A COMPLEX literal ([EComplex dc], carrying two
    [DecimalFloat] components — its canonical spelling is Go's predeclared `complex(re, im)` form, NOT
    imaginary-literal syntax and NOT a general call), or an EXPLICIT complex conversion ([EComplexConvert ct
    e], the source spelling `complex64(e)` / `complex128(e)`).  [EComplexConvert]'s target is the intrinsic
    [ComplexType].  Nesting is representable syntax that may be compiler-invalid
    (`uint8(int(300))`, `int8(int16(128))`, `int(3.5)`, `float32(true)`, `int(complex(3.5, 0.0))`) — such a
    program is REJECTED by GoTypes/GoCompile, not unrepresentable.  No type is attached here — the exact
    untyped-constant meaning (a bare float denotes its EXACT rational value; a conversion rounds ONCE at the
    destination format) and the context-directed typing/representability of these literals are the concern of
    [GoTypes]; the canonical source spelling is a separate proved encoding in [GoRender].  [EInt]/[ENeg]
    remain exact untyped integer-literal syntax.  No arithmetic, comparison, bitwise, shift, division,
    general named conversion, imaginary-literal syntax, `real`/`imag`, NaN/Inf constructors, parenthesis
    node, variables, calls, or string operations are representable. *)
Inductive GoExpr : Type :=
| EBool           : bool -> GoExpr
| EInt            : N -> GoExpr
| ENeg            : N -> GoExpr
| EString         : string -> GoExpr
| EIntConvert     : IntegerType -> GoExpr -> GoExpr
| EFloat          : DecimalFloat -> GoExpr
| EFloatConvert   : FloatType -> GoExpr -> GoExpr
| EComplex        : DecimalComplex -> GoExpr
| EComplexConvert : ComplexType -> GoExpr -> GoExpr.

Inductive GoStmt : Type :=
| SPrintln : list GoExpr -> GoStmt.

(** A raw top-level declaration.  Today: a `func main()` declaration with a statement body. *)
Inductive GoDecl : Type :=
| DMain : list GoStmt -> GoDecl.

(** The raw AST of one source file: its top-level declarations, in order. *)
Definition GoFileAST := list GoDecl.

(** ---- the module spec: intrinsic facts about the GENERATED module (not environment config) ---- *)

Record ModuleSpec : Type := mkModuleSpec {
  module_path       : ModulePath;
  module_go_version : GoVersion
}.

(** ---- the program: a module spec + a (possibly empty) path-indexed map of raw file ASTs ---- *)

Record GoProgram : Type := mkProgram {
  prog_module : ModuleSpec;
  prog_files  : fmap FilePath GoFileAST
}.

Definition prog_entries (p : GoProgram) : list (FilePath * GoFileAST) := fm_list (prog_files p).
Definition prog_keys (p : GoProgram) : list FilePath := fm_keys (prog_files p).
Definition prog_find (path : FilePath) (p : GoProgram) : option GoFileAST :=
  fm_find fp_eqb path (prog_files p).

(** ---- builders (keys unique, intrinsic; the file map MAY be empty) ---- *)

(** A single-file program under a module spec. *)
Definition singleton_program (ms : ModuleSpec) (path : FilePath) (f : GoFileAST) : GoProgram :=
  mkProgram ms (fm_singleton path f).

(** A module-only program: a valid [ModuleSpec] with NO source files. *)
Definition empty_program (ms : ModuleSpec) : GoProgram :=
  mkProgram ms fm_empty.

(** From a module spec + a list of (path, file): [None] ONLY on duplicate paths; the EMPTY list yields a
    valid module-only program (key-uniqueness is intrinsic). *)
Definition build_program (ms : ModuleSpec) (l : list (FilePath * GoFileAST)) : option GoProgram :=
  match fm_of_list fp_eqb fp_eqb_eq l with
  | None => None
  | Some m => Some (mkProgram ms m)
  end.
