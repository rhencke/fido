(* Facts — name-resolution meanings and site roles the phase consumes: predeclared/object meaning and role tests. *)
From Fido Require Import Names Integer Float Complex Index Compilable.TypeResolution Compilable.Bindings.

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

(* The compiler owns the binding result of resolving a name: a semantic meaning, or unresolved/unmodelled. *)
Inductive Resolution : Type :=
| ResMeaning    : Compilable.TypeResolution.NameMeaning -> Resolution
| ResUnresolved : Resolution
| ResUnmodelled : Resolution.

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
