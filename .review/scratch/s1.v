(* Proposed C6 public surface, in dependency order.  Scratch: untracked, not a build input. *)

From Stdlib Require Import List String Ascii ZArith NArith Sorted.
Import ListNotations.

(* ── (a) existing repository public names, faithfully stubbed ──────────────── *)
Parameter SyntaxProgram SyntaxFile ModuleSpec FilePathT : Type.
Parameter PackageRef : SyntaxProgram -> Type.
Parameter package_ref_key : forall {p}, PackageRef p -> string.
Parameter Identifier : Type.
Parameter spelling : Identifier -> string.
(* Integer.Kind, Float.Kind and Complex.Kind are closed today; stub them faithfully. *)
Inductive IntegerKind : Type :=
| IKInt | IKInt8 | IKInt16 | IKInt32 | IKInt64
| IKUint | IKUint8 | IKUint16 | IKUint32 | IKUint64.
Inductive FloatKind : Type := FKF32 | FKF64.
Inductive ComplexKind : Type := CKC64 | CKC128.
Parameter IntegerRepresentable : IntegerKind -> Z -> Prop.
Parameter FloatTypedConstant : FloatKind -> Type.
Parameter ComplexTypedConstant : ComplexKind -> Type.
Parameter Decimal : Type.
Parameter coefficient : Decimal -> Z.
Parameter IndexKey : Type.
Parameter Input : SyntaxProgram -> Type.
Parameter Core : SyntaxProgram -> Type.
Parameter core_input : forall {p}, Core p -> Input p.
Parameter Elaboration : SyntaxProgram -> Type.
Parameter elaboration_core : forall {p}, Elaboration p -> Core p.
Parameter elaborate : forall p, Elaboration p.
Parameter Admissible : SyntaxProgram -> Prop.

(* ── Names ─────────────────────────────────────────────────────────────────── *)
Inductive PredeclaredName : Type :=
| PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
| PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16 | PUint32
| PUint64 | PUintptr | PTrue | PFalse | PIota | PNil | PAppend | PCap | PClear | PClose | PComplex
| PCopy | PDelete | PImag | PLen | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal
| PRecover.

Definition predeclared_spelling (n : PredeclaredName) : string :=
  match n with
  | PAny => "any" | PBool => "bool" | PByte => "byte" | PComparable => "comparable"
  | PComplex64 => "complex64" | PComplex128 => "complex128" | PError => "error"
  | PFloat32 => "float32" | PFloat64 => "float64" | PInt => "int" | PInt8 => "int8"
  | PInt16 => "int16" | PInt32 => "int32" | PInt64 => "int64" | PRune => "rune"
  | PString => "string" | PUint => "uint" | PUint8 => "uint8" | PUint16 => "uint16"
  | PUint32 => "uint32" | PUint64 => "uint64" | PUintptr => "uintptr" | PTrue => "true"
  | PFalse => "false" | PIota => "iota" | PNil => "nil" | PAppend => "append" | PCap => "cap"
  | PClear => "clear" | PClose => "close" | PComplex => "complex" | PCopy => "copy"
  | PDelete => "delete" | PImag => "imag" | PLen => "len" | PMake => "make" | PMax => "max"
  | PMin => "min" | PNew => "new" | PPanic => "panic" | PPrint => "print" | PPrintln => "println"
  | PReal => "real" | PRecover => "recover"
  end.

Definition all_predeclared : list PredeclaredName :=
  [PAny; PBool; PByte; PComparable; PComplex64; PComplex128; PError; PFloat32; PFloat64;
   PInt; PInt8; PInt16; PInt32; PInt64; PRune; PString; PUint; PUint8; PUint16; PUint32;
   PUint64; PUintptr; PTrue; PFalse; PIota; PNil; PAppend; PCap; PClear; PClose; PComplex;
   PCopy; PDelete; PImag; PLen; PMake; PMax; PMin; PNew; PPanic; PPrint; PPrintln; PReal;
   PRecover].

Parameter classify_spelling : string -> option PredeclaredName.
Parameter predeclared_eqb : PredeclaredName -> PredeclaredName -> bool.

(* An ordinary identifier excludes blank and nothing else.  Every predeclared spelling is a legal source
   name and may be shadowed; its meaning comes only from binding. *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank : spelling ordinary_identifier <> "_"%string
}.

(* Collections owns NonEmpty; Float owns NonNegativeDecimal. *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Definition ne_to_list {A} (ne : NonEmpty A) : list A := ne_first A ne :: ne_rest A ne.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal; nnd_nonneg : (0 <= coefficient nnd_decimal)%Z
}.

(* ── Syntax ────────────────────────────────────────────────────────────────── *)
Inductive BindingName : Type := Named (n : OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

(* Magnitudes only: a negative source value is exactly one `Unary UnaryMinus` over a nonnegative literal. *)
Inductive Literal : Type :=
| IntegerLiteral (n : N)
| FloatLiteral (d : NonNegativeDecimal)
| StringLiteral (s : string).

Inductive TypeExpr : Type := NamedType (n : OrdinaryIdentifier).

Inductive Expr : Type :=
| Name (n : OrdinaryIdentifier)
| LiteralExpr (l : Literal)
| Unary (op : UnaryOp) (e : Expr)
| Application (head : Expr) (args : list Expr).

Inductive ConstInitializer : Type :=
| ExplicitConstInit (ty : option TypeExpr) (values : NonEmpty Expr)
| InheritedConstInit.

Record ConstSpec : Type := MakeConstSpec {
  const_names : NonEmpty BindingName; const_init : ConstInitializer
}.

Inductive VarInitializer : Type :=
| VarTypeOnly (ty : TypeExpr)
| VarValues (ty : option TypeExpr) (values : NonEmpty Expr).

Record VarSpec : Type := MakeVarSpec {
  var_names : NonEmpty BindingName; var_init : VarInitializer
}.

(* Both alias and definition admit blank; a blank type spec creates no object and no type identity. *)
Inductive TypeSpec : Type :=
| AliasSpec (name : BindingName) (target : TypeExpr)
| DefSpec (name : BindingName) (target : TypeExpr).

(* Pinned Go accepts `const ()`, `var ()` and `type ()`, so a spec group is a list.  Name lists and explicit
   initializer expression lists stay nonempty. *)
Inductive Declaration : Type :=
| ConstDecl (specs : list ConstSpec)
| VarDecl (specs : list VarSpec)
| TypeDecl (specs : list TypeSpec).

Inductive Stmt : Type :=
| ExprStmt (e : Expr)
| DeclarationStmt (d : Declaration)
| ShortVarDecl (names : NonEmpty BindingName) (values : NonEmpty Expr).

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration (d : Declaration)
| Main (body : Block).

Parameter program_files : SyntaxProgram -> list (FilePathT * SyntaxFile).
Parameter program_module : SyntaxProgram -> ModuleSpec.
(* Rendering cannot be pinned against an opaque file: these mirror the repository accessors. *)
Parameter file_decls : SyntaxFile -> list TopLevelDecl.
Parameter path_string : FilePathT -> string.
Parameter module_path : ModuleSpec -> string.
Parameter module_go_version : ModuleSpec -> string.
