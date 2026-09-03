-- Port of Index/Model.v (lean/README.md).
import Fido.Names
import Fido.Syntax

/-! divergences:
  * `Record`s are `structure`s and data `Inductive`s keep their constructors, with `genInjectivity` /
    `genSizeOfSpec` off and every constructor and projection `export`ed (Syntax.lean), so `VName n`,
    `c_view c`, `mkCell …` read as in the `.v`.
  * `nth_error l n` is `l[n]?` (core's `GetElem?` on lists); `False_rect A (Nat.nlt_0_r n H)` is
    `absurd H (Nat.not_lt_zero n)`, `proj2 (Nat.succ_lt_mono …)` is `Nat.lt_of_succ_lt_succ`, and
    `Peano_dec.le_unique` is definitional proof irrelevance (`lt_unique` is `rfl`).  `S pos` is `pos + 1`.
  * `k <? nn` / `k =? nn` are `decide (k < nn)` / `decide (k = nn)` (Names.lean), `andb` is `&&`, and Rocq's
    `if` on a `bool` is `bif` (Syntax.lean).
  * Catch-all `_` match arms are enumerated (Integer.lean): the thirteen `false` alternatives of
    `requires_first_edge` (eleven views, `VStmt` split by shape), the nine `RPlain` views of `layout_role`,
    the `_ + 1` ordinal of the `VTypeSpec` arms of `layout_role` and `layout_kind`, the four `None` views of
    `layout_count`, and the thirty-nine `False` pairs of `spec_view_of_flavor`.
  * Axiom closure (the audit's finding; no statement changes): `nth_lt_nth_error` carries `propext`, and it
    alone — its statement mentions `l[n]?`, and core's `List.get?Internal` (what the `GetElem?` instance on
    lists unfolds to in v4.33; `List.get?` no longer exists) is itself `propext`-dependent through its own
    `| _, _ => none` wildcard arm, the Integer.lean finding inside core.  The proof is the `.v`'s induction and
    adds nothing (`Nat.not_lt_zero`, `Nat.lt_of_succ_lt_succ` and `rfl` are axiom-free).  Every other
    constant here is axiom-free; nothing reaches `Classical.choice`.
-/

namespace Fido.Index.Model

inductive SpecFlavor : Type
  | ConstSpecF | VarSpecF | TypeSpecF

export SpecFlavor (ConstSpecF VarSpecF TypeSpecF)

/-! shallow local shapes: the immediate constructor and its scalar payload only; substructure is child cells -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive ConstShape : Type
  | CSExplicit (has_type : Bool) (n_names n_values : Nat)
  | CSInherited (n_names : Nat)

export ConstShape (CSExplicit CSInherited)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive VarShape : Type
  | VSTypeOnly (n_names : Nat)
  | VSValues (has_type : Bool) (n_names n_values : Nat)

export VarShape (VSTypeOnly VSValues)

inductive TypeSpecShape : Type
  | TSAlias | TSDef

export TypeSpecShape (TSAlias TSDef)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive StmtShape : Type
  | SSExpr | SSDecl
  | SSShort (n_names n_values : Nat)

export StmtShape (SSExpr SSDecl SSShort)

inductive TopShape : Type
  | TSTopDecl | TSMain

export TopShape (TSTopDecl TSMain)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- the occurrence view: one shallow local cell — the head constructor and only immediate scalars, no
    descendants -/
inductive NodeView : Type
  | VName        : Names.OrdinaryIdentifier → NodeView
  | VLiteral     : Syntax.Literal           → NodeView
  | VUnary       : Syntax.UnaryOp           → NodeView
  | VApplication : NodeView
  | VTypeExpr    : Syntax.TypeExpr          → NodeView
  | VBindingName : Syntax.BindingName       → NodeView
  | VConstSpec   : ConstShape               → NodeView
  | VVarSpec     : VarShape                 → NodeView
  | VTypeSpec    : TypeSpecShape            → NodeView
  | VDecl        : SpecFlavor               → NodeView
  | VStmt        : StmtShape                → NodeView
  | VBlock       : NodeView
  | VTop         : TopShape                 → NodeView
  | VFile        : NodeView

export NodeView (VName VLiteral VUnary VApplication VTypeExpr VBindingName VConstSpec VVarSpec VTypeSpec
  VDecl VStmt VBlock VTop VFile)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive Kind : Type
  | ExprKind | TypeExprKind | BindingNameKind
  | SpecKind : SpecFlavor → Kind
  | DeclKind | StmtKind | BlockKind | TopKind | FileKind

export Kind (ExprKind TypeExprKind BindingNameKind SpecKind DeclKind StmtKind BlockKind TopKind FileKind)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive Role : Type
  | RPlain | RApplicationHead
  | RApplicationArg : Nat → Role
  | RUnaryOperand
  | RSpecName : SpecFlavor → Role
  | RShortLhs | RExprStatementExpr | RTypeUse

export Role (RPlain RApplicationHead RApplicationArg RUnaryOperand RSpecName RShortLhs RExprStatementExpr
  RTypeUse)

/-- the kind each view is classified as; node_kind derives this, so kind is never stored -/
def kind_of_view (v : NodeView) : Kind :=
  match v with
  | VName _ | VLiteral _ | VUnary _ | VApplication => ExprKind
  | VTypeExpr _ => TypeExprKind | VBindingName _ => BindingNameKind
  | VConstSpec _ => SpecKind ConstSpecF | VVarSpec _ => SpecKind VarSpecF | VTypeSpec _ => SpecKind TypeSpecF
  | VDecl _ => DeclKind | VStmt _ => StmtKind | VBlock => BlockKind | VTop _ => TopKind | VFile => FileKind

/-- generic total positional list access; the in-range proof makes it a projection, never a fallback -/
def nth_lt {A : Type} : (l : List A) → ∀ n, n < l.length → A
  | [], n, H => absurd H (Nat.not_lt_zero n)
  | x :: _, 0, _ => x
  | _ :: xs, k + 1, H => nth_lt xs k (Nat.lt_of_succ_lt_succ H)

theorem lt_unique (n m : Nat) (p q : n < m) : p = q := rfl

theorem nth_lt_nth_error {A : Type} (l : List A) : ∀ n H, l[n]? = some (nth_lt l n H) := by
  induction l with
  | nil => intro n H; exact absurd H (Nat.not_lt_zero n)
  | cons x xs IH =>
    intro n H
    cases n with
    | zero => rfl
    | succ k => exact IH k (Nat.lt_of_succ_lt_succ H)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- one shallow cell: view, role, parent position, subtree extent, ordered direct-child positions, own parent
    slot -/
structure Cell : Type where
  mkCell ::
  c_view     : NodeView
  c_role     : Role
  c_parent   : Option Nat
  c_extent   : Nat
  c_children : List Nat
  c_slot     : Nat

export Cell (mkCell c_view c_role c_parent c_extent c_children c_slot)

/-- set only the parent-slot tag, leaving every structural field of the cell untouched -/
def set_slot (k : Nat) (c : Cell) : Cell :=
  mkCell (c_view c) (c_role c) (c_parent c) (c_extent c) (c_children c) k

theorem set_slot_view : ∀ k c, c_view (set_slot k c) = c_view c := fun _ _ => rfl
theorem set_slot_role : ∀ k c, c_role (set_slot k c) = c_role c := fun _ _ => rfl
theorem set_slot_parent : ∀ k c, c_parent (set_slot k c) = c_parent c := fun _ _ => rfl
theorem set_slot_extent : ∀ k c, c_extent (set_slot k c) = c_extent c := fun _ _ => rfl
theorem set_slot_children : ∀ k c, c_children (set_slot k c) = c_children c := fun _ _ => rfl
theorem set_slot_slot : ∀ k c, c_slot (set_slot k c) = k := fun _ _ => rfl

/-- which views carry a required first-child edge, and the shape of that edge — shared vocabulary of the
    build -/
def requires_first_edge (v : NodeView) : Bool :=
  match v with
  | VApplication | VUnary _ | VStmt SSExpr => true
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ | VConstSpec _ | VVarSpec _ | VTypeSpec _ | VDecl _
  | VStmt SSDecl | VStmt (SSShort _ _) | VBlock | VTop _ | VFile => false
def first_child_wf (children : List Nat) (pos bnd : Nat) : Prop :=
  match children with | hp :: _ => hp = pos + 1 ∧ hp < bnd | [] => False

/-- the exact role each child ordinal carries, a total formula over the parent's shallow view alone -/
def layout_role (v : NodeView) (k : Nat) : Role :=
  match v with
  | VApplication => match k with | 0 => RApplicationHead | i + 1 => RApplicationArg i
  | VUnary _ => RUnaryOperand
  | VStmt SSExpr => RExprStatementExpr
  | VStmt (SSShort nn _) => bif decide (k < nn) then RShortLhs else RPlain
  | VConstSpec (CSExplicit ht nn _) =>
      bif decide (k < nn) then RSpecName ConstSpecF else bif ht && decide (k = nn) then RTypeUse else RPlain
  | VConstSpec (CSInherited _) => RSpecName ConstSpecF
  | VVarSpec (VSTypeOnly nn) => bif decide (k < nn) then RSpecName VarSpecF else RTypeUse
  | VVarSpec (VSValues ht nn _) =>
      bif decide (k < nn) then RSpecName VarSpecF else bif ht && decide (k = nn) then RTypeUse else RPlain
  | VTypeSpec _ => match k with | 0 => RSpecName TypeSpecF | _ + 1 => RTypeUse
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ | VStmt SSDecl | VDecl _ | VBlock | VTop _ | VFile =>
      RPlain
/-- the exact child count a shape fixes; views whose counts live below the shallow scalars stay
    unconstrained -/
def layout_count (v : NodeView) : Option Nat :=
  match v with
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ => some 0
  | VUnary _ => some 1
  | VStmt SSExpr | VStmt SSDecl => some 1
  | VStmt (SSShort nn nv) => some (nn + nv)
  | VTop _ => some 1
  | VConstSpec (CSExplicit ht nn nv) => some (nn + (bif ht then 1 else 0) + nv)
  | VConstSpec (CSInherited nn) => some nn
  | VVarSpec (VSTypeOnly nn) => some (nn + 1)
  | VVarSpec (VSValues ht nn nv) => some (nn + (bif ht then 1 else 0) + nv)
  | VTypeSpec _ => some 2
  | VApplication | VDecl _ | VBlock | VFile => none
/-- the kind of the child at ordinal k, a total formula over the parent view alone — the view-level layout -/
def layout_kind (v : NodeView) (k : Nat) : Kind :=
  match v with
  | VApplication => ExprKind
  | VUnary _ => ExprKind
  | VStmt SSExpr => ExprKind
  | VStmt SSDecl => DeclKind
  | VStmt (SSShort nn _) => bif decide (k < nn) then BindingNameKind else ExprKind
  | VConstSpec (CSExplicit ht nn _) =>
      bif decide (k < nn) then BindingNameKind else bif ht && decide (k = nn) then TypeExprKind else ExprKind
  | VConstSpec (CSInherited _) => BindingNameKind
  | VVarSpec (VSTypeOnly nn) => bif decide (k < nn) then BindingNameKind else TypeExprKind
  | VVarSpec (VSValues ht nn _) =>
      bif decide (k < nn) then BindingNameKind else bif ht && decide (k = nn) then TypeExprKind else ExprKind
  | VTypeSpec _ => match k with | 0 => BindingNameKind | _ + 1 => TypeExprKind
  | VDecl fl => SpecKind fl
  | VBlock => StmtKind
  | VTop TSTopDecl => DeclKind
  | VTop TSMain => BlockKind
  | VFile => TopKind
  | VName _ | VLiteral _ | VTypeExpr _ | VBindingName _ => FileKind

/-- each spec flavor's exact child view class: a declaration's children are exactly its flavor's specs -/
def spec_view_of_flavor (fl : SpecFlavor) (v : NodeView) : Prop :=
  match fl, v with
  | ConstSpecF, VConstSpec _ => True
  | VarSpecF, VVarSpec _ => True
  | TypeSpecF, VTypeSpec _ => True
  | ConstSpecF, VName _ | ConstSpecF, VLiteral _ | ConstSpecF, VUnary _ | ConstSpecF, VApplication
  | ConstSpecF, VTypeExpr _ | ConstSpecF, VBindingName _ | ConstSpecF, VVarSpec _ | ConstSpecF, VTypeSpec _
  | ConstSpecF, VDecl _ | ConstSpecF, VStmt _ | ConstSpecF, VBlock | ConstSpecF, VTop _ | ConstSpecF, VFile
  | VarSpecF, VName _ | VarSpecF, VLiteral _ | VarSpecF, VUnary _ | VarSpecF, VApplication
  | VarSpecF, VTypeExpr _ | VarSpecF, VBindingName _ | VarSpecF, VConstSpec _ | VarSpecF, VTypeSpec _
  | VarSpecF, VDecl _ | VarSpecF, VStmt _ | VarSpecF, VBlock | VarSpecF, VTop _ | VarSpecF, VFile
  | TypeSpecF, VName _ | TypeSpecF, VLiteral _ | TypeSpecF, VUnary _ | TypeSpecF, VApplication
  | TypeSpecF, VTypeExpr _ | TypeSpecF, VBindingName _ | TypeSpecF, VConstSpec _ | TypeSpecF, VVarSpec _
  | TypeSpecF, VDecl _ | TypeSpecF, VStmt _ | TypeSpecF, VBlock | TypeSpecF, VTop _ | TypeSpecF, VFile => False

end Fido.Index.Model
