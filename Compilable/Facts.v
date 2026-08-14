(* Facts — resolution meanings, site roles, the resolver at a use, and the println default-overflow fact. *)
From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Names Integer Float Complex FilePath Syntax Index Compilable.TypeResolution Compilable.Bindings.
Import ListNotations.

(* The semantic type a predeclared type-name denotes, or None when the name is not one of the sixteen types. *)
Definition predeclared_type_of_name (n : Names.PredeclaredName) : option Compilable.TypeResolution.SemanticType :=
  match n with
  | Names.PInt    => Some (Compilable.TypeResolution.IntegerType Integer.Int)    | Names.PInt8  => Some (Compilable.TypeResolution.IntegerType Integer.Int8)
  | Names.PInt16  => Some (Compilable.TypeResolution.IntegerType Integer.Int16)  | Names.PInt32 => Some (Compilable.TypeResolution.IntegerType Integer.Int32)
  | Names.PInt64  => Some (Compilable.TypeResolution.IntegerType Integer.Int64)
  | Names.PUint   => Some (Compilable.TypeResolution.IntegerType Integer.Uint)   | Names.PUint8  => Some (Compilable.TypeResolution.IntegerType Integer.Uint8)
  | Names.PUint16 => Some (Compilable.TypeResolution.IntegerType Integer.Uint16) | Names.PUint32 => Some (Compilable.TypeResolution.IntegerType Integer.Uint32)
  | Names.PUint64 => Some (Compilable.TypeResolution.IntegerType Integer.Uint64)
  | Names.PFloat32 => Some (Compilable.TypeResolution.FloatType Float.F32) | Names.PFloat64 => Some (Compilable.TypeResolution.FloatType Float.F64)
  | Names.PComplex64 => Some (Compilable.TypeResolution.ComplexType Complex.C64) | Names.PComplex128 => Some (Compilable.TypeResolution.ComplexType Complex.C128)
  | Names.PByte => Some (Compilable.TypeResolution.IntegerType Integer.Uint8) | Names.PRune => Some (Compilable.TypeResolution.IntegerType Integer.Int32)
  | _ => None
  end.

(* The binding result of resolving a name: a meaning, unresolved, unmodelled, or a known-invalid identity. *)
Inductive Resolution : Type :=
| ResMeaning    : Compilable.TypeResolution.NameMeaning -> Resolution
| ResUnresolved : Resolution
| ResUnmodelled : Resolution
| ResInvalid    : Resolution.

(* The local typing spec needs a meaning or nothing; the compiler-owned failure kind stays behind. *)
Definition resolution_meaning (r : Resolution) : option Compilable.TypeResolution.NameMeaning :=
  match r with ResMeaning m => Some m | _ => None end.

Definition predeclared_meaning (n : Names.PredeclaredName) : Resolution :=
  match predeclared_type_of_name n with
  | Some t => ResMeaning (Compilable.TypeResolution.NMConversionType t)
  | None =>
      match n with
      | Names.PTrue    => ResMeaning (Compilable.TypeResolution.NMValueConstant (Compilable.TypeResolution.BoolConstant true))
      | Names.PFalse   => ResMeaning (Compilable.TypeResolution.NMValueConstant (Compilable.TypeResolution.BoolConstant false))
      | Names.PComplex => ResMeaning Compilable.TypeResolution.NMComplexBuiltin
      | Names.PPrintln => ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin
      | Names.PIota    => ResInvalid
      | Names.PNil     => ResInvalid
      | _ => ResUnmodelled
      end
  end.

Definition object_meaning {p} {idx : Index.ProgramIndex p} (o : Compilable.Bindings.ObjectRef idx) : Resolution :=
  match o with
  | Compilable.Bindings.PredeclaredObject n => predeclared_meaning n
  | Compilable.Bindings.SourceObject _      => ResUnmodelled   (* type/value/callable meaning is a later root *)
  end.

Definition is_value_role (r : Index.Role) : bool :=
  match r with Index.ApplicationHead => false | _ => true end.
Definition is_stmt_expr_role (r : Index.Role) : bool :=
  match r with Index.ExprStatementExpr => true | _ => false end.

Section WithProgram.
Variable p : Syntax.Program.

(* the resolver at a use, over the retained index and the once-gathered establishers *)
Definition resolver_at (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (use_path : FilePath.T) (use_id : positive) (n : Names.OrdinaryIdentifier) : Resolution :=
  match Compilable.Bindings.resolve p idx es use_path use_id (Names.ordinary_spelling n) with
  | Some o => object_meaning o
  | None   => ResUnresolved
  end.

(* The local typing spec's view of the resolver: a meaning where one exists, None for unresolved/unmodelled. *)
Definition nm_at (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (use_path : FilePath.T) (use_id : positive) : Names.OrdinaryIdentifier -> option Compilable.TypeResolution.NameMeaning :=
  fun n => resolution_meaning (resolver_at idx es use_path use_id n).

(* a println argument whose default type cannot hold it — the head resolves at the arg's id (same statement) *)
Definition arg_default_overflow (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (f : Syntax.File) (id : positive) (c : Index.CFile f)
  : option Compilable.TypeResolution.Constant :=
  match Index.cfile_role c with
  | Index.ApplicationArgument _ =>
      match Index.cfile_parentview c with
      | Some (Index.VExpr (Syntax.Application (Syntax.Name h) _)) =>
                  match resolver_at idx es path id h with
                  | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin =>
                      match Index.cfile_view_expr c with
                      | Some e =>
                          match Compilable.TypeResolution.constant_info (nm_at idx es path id) e with
                          | Some ci =>
                              match Compilable.TypeResolution.resolve_constant_info ci with
                              | None    => Some (Compilable.TypeResolution.constant_info_exact ci)
                              | Some _  => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
      | _ => None
      end
  | _ => None
  end.

End WithProgram.
