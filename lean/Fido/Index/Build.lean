-- Port of Index/Build.v (lean/README.md).
import Fido.Collections
import Fido.Syntax
import Fido.Index.Model

/-! divergences:
  * `number_expr`'s argument loop is an INLINED `let fix do_args …` in the `.v` (there only so Rocq's guard
    checker accepts each argument); Lean's structural recursion has no inline fixpoint over a nested inductive,
    so `number_expr` and a named companion `number_args (b i bi : Nat) (es : List Expr)` are one `mutual`
    structural definition over the nested `Expr` / `List Expr` (the Render.lean `render_expr` / `render_args`
    pattern).  `number_args b` is `do_args` with the application position `b` — the parent every argument cell
    records, captured by the inline fix — made an explicit first argument; it returns the same
    `(cells, next, roots)` triple, so `number_expr`'s `Application` equation is EXACTLY the `.v`'s with
    `do_args` replaced by `number_args b`.  Index/BuildLaws.v's proofs destructure the inline fix
    (`destruct ((fix do_args …) 0 b1 args)`); the next port reasons about `number_args` instead.
  * Rocq's `let '(x, y) := e in …` is `match e with | (x, y) => …`; a Rocq triple `A * B * C` is the
    left-nested `(A * B) * C`, its Lean rendering `A × B × C` the right-nested `A × (B × C)` — the value
    `(cells, next, roots)` is written identically in both, and BuildLaws' `fst (fst t)` / `snd (fst t)` /
    `snd t` become `t.1` / `t.2.1` / `t.2.2`.
  * `NodeMap` keys are `Nat` (Collections.lean: `positive` is `Nat`), so `Pos.of_succ_nat n` is `n + 1` in
    `posmap_of`, `slotmap` and `slot_at` — the map is keyed by successor position exactly as in the `.v`.
    `S b` is `b + 1`; `fold_right` / `combine` / `seq 0 n` / `flat_map` / `map` are `List.foldr` / `List.zip` /
    `List.range n` / `List.flatMap` / `List.map`; `fst kv` / `snd kv` are `kv.1` / `kv.2`.
  * `Record FileInfo` is a `structure` with `genInjectivity` / `genSizeOfSpec` off and its constructor and
    projections `export`ed (Syntax.lean), so `mkFileInfo`, `fi_cells`, `fi_count` read as in the `.v`.
  * Rocq's `match ot with Some _ => true | None => false end` is the same two-arm match on `Option`; every
    match here is already total and arm-enumerated (no catch-all `_` arm exists in the `.v`).
  * Axiom closure (the audit's finding; no statement changes): the whole numbering — `number_list` through
    `number_file`, the six shapes, `expr_view`, `number_args` and `child_slots` — is axiom-free (the mutual
    structural recursion over the nested `Expr` compiles to `Expr.rec` / `brecOn` and adds nothing).
    `posmap_of`, `slotmap`, `slot_at`, `assign_slots`, `build_fileinfo`, `raw_index` and `FileInfo` (its
    `fi_cells` field is a `NodeMap.t`, so its generated `rec` / `casesOn` / `noConfusion` too) reach
    `Classical.choice`, `propext` and `Quot.sound` through the `NodeMap` / `FileMap` operations alone — the
    Collections.lean core finding; no proof here adds one (the module has no lemmas).
-/

namespace Fido.Index.Build
open Fido.Index.Model

/-- number a list of items left to right, threading the next free position and collecting each item's root -/
def number_list {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) (b : Nat) (xs : List A)
    : List (Nat × Cell) × Nat × List Nat :=
  match xs with
  | [] => ([], b, [])
  | x :: rest =>
      match f b x with
      | (xc, b') =>
        match number_list f b' rest with
        | (rc, b'', roots) => (xc ++ rc, b'', b :: roots)

def number_leaf (v : NodeView) (par : Option Nat) (role : Role) (b : Nat) : List (Nat × Cell) × Nat :=
  ([(b, mkCell v role par b [] 0)], b + 1)

/-! the shallow shape of each composite occurrence: its head constructor and immediate scalar flags only -/

def constspec_shape (cs : Syntax.ConstSpec) : ConstShape :=
  match Syntax.const_init cs with
  | Syntax.ExplicitConstInit ot vals =>
      CSExplicit (match ot with | some _ => true | none => false)
                 (List.length (Collections.ne_to_list (Syntax.const_names cs)))
                 (List.length (Collections.ne_to_list vals))
  | Syntax.InheritedConstInit => CSInherited (List.length (Collections.ne_to_list (Syntax.const_names cs)))
def varspec_shape (vs : Syntax.VarSpec) : VarShape :=
  match Syntax.var_init vs with
  | Syntax.VarTypeOnly _ => VSTypeOnly (List.length (Collections.ne_to_list (Syntax.var_names vs)))
  | Syntax.VarValues ot vals => VSValues (match ot with | some _ => true | none => false)
                                         (List.length (Collections.ne_to_list (Syntax.var_names vs)))
                                         (List.length (Collections.ne_to_list vals))
def typespec_shape (ts : Syntax.TypeSpec) : TypeSpecShape :=
  match ts with | Syntax.AliasSpec _ _ => TSAlias | Syntax.DefSpec _ _ => TSDef
def decl_flavor (d : Syntax.Declaration) : SpecFlavor :=
  match d with | Syntax.ConstDecl _ => ConstSpecF | Syntax.VarDecl _ => VarSpecF | Syntax.TypeDecl _ => TypeSpecF
def stmt_shape (s : Syntax.Stmt) : StmtShape :=
  match s with
  | Syntax.ExprStmt _ => SSExpr | Syntax.DeclarationStmt _ => SSDecl
  | Syntax.ShortVarDecl names vals => SSShort (List.length (Collections.ne_to_list names))
                                              (List.length (Collections.ne_to_list vals))
def top_shape (td : Syntax.TopLevelDecl) : TopShape :=
  match td with | Syntax.TopDeclaration _ => TSTopDecl | Syntax.Main _ => TSMain

mutual
/-- an expression subtree; the arg list is the named companion `number_args` (the `.v`'s inline `do_args`) -/
def number_expr (par : Option Nat) (role : Role) (b : Nat) (e : Syntax.Expr) : List (Nat × Cell) × Nat :=
  match e with
  | Syntax.Name n => number_leaf (VName n) par role b
  | Syntax.LiteralExpr lit => number_leaf (VLiteral lit) par role b
  | Syntax.Unary op e' =>
      match number_expr (some b) RUnaryOperand (b + 1) e' with
      | (kc, nxt) => ((b, mkCell (VUnary op) role par (nxt - 1) [b + 1] 0) :: kc, nxt)
  | Syntax.Application head args =>
      match number_expr (some b) RApplicationHead (b + 1) head with
      | (hc, b1) =>
        match number_args b 0 b1 args with
        | (ac, bfin, aroots) =>
          ((b, mkCell VApplication role par (bfin - 1) ((b + 1) :: aroots) 0) :: (hc ++ ac), bfin)
/-- the `.v`'s `do_args`, with the application position `b` (each argument's parent) explicit -/
def number_args (b : Nat) (i : Nat) (bi : Nat) (es : List Syntax.Expr) : List (Nat × Cell) × Nat × List Nat :=
  match es with
  | [] => ([], bi, [])
  | a :: rest =>
      match number_expr (some b) (RApplicationArg i) bi a with
      | (ac, bi') =>
        match number_args b (i + 1) bi' rest with
        | (rc, bf, roots) => (ac ++ rc, bf, bi :: roots)
end

/-- the shallow view each expression head presents as its own root cell -/
def expr_view (e : Syntax.Expr) : NodeView :=
  match e with
  | Syntax.Name n => VName n
  | Syntax.LiteralExpr l => VLiteral l
  | Syntax.Unary op _ => VUnary op
  | Syntax.Application _ _ => VApplication

def number_typeexpr (par : Option Nat) (role : Role) (b : Nat) (t : Syntax.TypeExpr) : List (Nat × Cell) × Nat :=
  number_leaf (VTypeExpr t) par role b
def number_bindingname (par : Option Nat) (role : Role) (b : Nat) (bn : Syntax.BindingName) : List (Nat × Cell) × Nat :=
  number_leaf (VBindingName bn) par role b

def number_opttype (par : Option Nat) (b : Nat) (ot : Option Syntax.TypeExpr) : List (Nat × Cell) × Nat × List Nat :=
  match ot with
  | some t => match number_typeexpr par RTypeUse b t with | (c, b') => (c, b', [b])
  | none => ([], b, [])

def number_constspec (par : Option Nat) (role : Role) (b : Nat) (cs : Syntax.ConstSpec) : List (Nat × Cell) × Nat :=
  let self := b
  match number_list (number_bindingname (some self) (RSpecName ConstSpecF))
                    (self + 1) (Collections.ne_to_list (Syntax.const_names cs)) with
  | (nc, b1, nroots) =>
    match (match Syntax.const_init cs with
           | Syntax.ExplicitConstInit ot vals =>
               match number_opttype (some self) b1 ot with
               | (oc, b2, oroots) =>
                 match number_list (number_expr (some self) RPlain) b2 (Collections.ne_to_list vals) with
                 | (vc, b3, vroots) => (oc ++ vc, b3, oroots ++ vroots)
           | Syntax.InheritedConstInit => ([], b1, [])) with
    | (ic, bfin, iroots) =>
      ((self, mkCell (VConstSpec (constspec_shape cs)) role par (bfin - 1) (nroots ++ iroots) 0) :: (nc ++ ic), bfin)

def number_varspec (par : Option Nat) (role : Role) (b : Nat) (vs : Syntax.VarSpec) : List (Nat × Cell) × Nat :=
  let self := b
  match number_list (number_bindingname (some self) (RSpecName VarSpecF))
                    (self + 1) (Collections.ne_to_list (Syntax.var_names vs)) with
  | (nc, b1, nroots) =>
    match (match Syntax.var_init vs with
           | Syntax.VarTypeOnly t =>
               match number_typeexpr (some self) RTypeUse b1 t with | (c, b2) => (c, b2, [b1])
           | Syntax.VarValues ot vals =>
               match number_opttype (some self) b1 ot with
               | (oc, b2, oroots) =>
                 match number_list (number_expr (some self) RPlain) b2 (Collections.ne_to_list vals) with
                 | (vc, b3, vroots) => (oc ++ vc, b3, oroots ++ vroots)) with
    | (ic, bfin, iroots) =>
      ((self, mkCell (VVarSpec (varspec_shape vs)) role par (bfin - 1) (nroots ++ iroots) 0) :: (nc ++ ic), bfin)

def number_typespec (par : Option Nat) (role : Role) (b : Nat) (ts : Syntax.TypeSpec) : List (Nat × Cell) × Nat :=
  let self := b
  match (match ts with | Syntax.AliasSpec bn t | Syntax.DefSpec bn t => (bn, t)) with
  | (bn, t) =>
    match number_bindingname (some self) (RSpecName TypeSpecF) (self + 1) bn with
    | (bc, b1) =>
      match number_typeexpr (some self) RTypeUse b1 t with
      | (tc, bfin) =>
        ((self, mkCell (VTypeSpec (typespec_shape ts)) role par (bfin - 1) [self + 1, b1] 0) :: (bc ++ tc), bfin)

def number_decl (par : Option Nat) (role : Role) (b : Nat) (d : Syntax.Declaration) : List (Nat × Cell) × Nat :=
  let self := b
  match (match d with
         | Syntax.ConstDecl cs => number_list (number_constspec (some self) RPlain) (self + 1) cs
         | Syntax.VarDecl vs   => number_list (number_varspec (some self) RPlain) (self + 1) vs
         | Syntax.TypeDecl ts  => number_list (number_typespec (some self) RPlain) (self + 1) ts) with
  | (kc, bfin, roots) =>
    ((self, mkCell (VDecl (decl_flavor d)) role par (bfin - 1) roots 0) :: kc, bfin)

def number_stmt (par : Option Nat) (role : Role) (b : Nat) (s : Syntax.Stmt) : List (Nat × Cell) × Nat :=
  let self := b
  match (match s with
         | Syntax.ExprStmt e =>
             match number_expr (some self) RExprStatementExpr (self + 1) e with | (c, b') => (c, b', [self + 1])
         | Syntax.DeclarationStmt d =>
             match number_decl (some self) RPlain (self + 1) d with | (c, b') => (c, b', [self + 1])
         | Syntax.ShortVarDecl names vals =>
             match number_list (number_bindingname (some self) RShortLhs)
                               (self + 1) (Collections.ne_to_list names) with
             | (nc, b1, nroots) =>
               match number_list (number_expr (some self) RPlain) b1 (Collections.ne_to_list vals) with
               | (vc, b2, vroots) => (nc ++ vc, b2, nroots ++ vroots)) with
  | (kc, bfin, roots) =>
    ((self, mkCell (VStmt (stmt_shape s)) role par (bfin - 1) roots 0) :: kc, bfin)

def number_block (par : Option Nat) (role : Role) (b : Nat) (blk : Syntax.Block) : List (Nat × Cell) × Nat :=
  let self := b
  let stmts := match blk with | Syntax.MakeBlock stmts => stmts
  match number_list (number_stmt (some self) RPlain) (self + 1) stmts with
  | (kc, bfin, roots) =>
    ((self, mkCell VBlock role par (bfin - 1) roots 0) :: kc, bfin)

def number_toplevel (par : Option Nat) (role : Role) (b : Nat) (td : Syntax.TopLevelDecl) : List (Nat × Cell) × Nat :=
  let self := b
  match (match td with
         | Syntax.TopDeclaration d =>
             match number_decl (some self) RPlain (self + 1) d with | (c, b') => (c, b', [self + 1])
         | Syntax.Main blk =>
             match number_block (some self) RPlain (self + 1) blk with | (c, b') => (c, b', [self + 1])) with
  | (kc, bfin, roots) =>
    ((self, mkCell (VTop (top_shape td)) role par (bfin - 1) roots 0) :: kc, bfin)

/-- the file occurrence at position 0, its children the top-level declarations, in one preorder pass -/
def number_file (f : Syntax.File) : List (Nat × Cell) :=
  match number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with
  | (dc, bfin, droots) => (0, mkCell VFile RPlain none (bfin - 1) droots 0) :: dc
/-- one per-file finite structure: the position map keyed by occurrence position, and the occurrence count -/
def posmap_of (occs : List (Nat × Cell)) : Collections.NodeMap.t Cell :=
  List.foldr (fun kv m => Collections.NodeMap.add (kv.1 + 1) kv.2 m)
             (Collections.NodeMap.empty Cell) occs

/-- each parent contributes one pair per direct child: that child's position paired with its exact ordinal -/
def child_slots (occs : List (Nat × Cell)) : List (Nat × Nat) :=
  List.flatMap (fun kv => List.zip (c_children kv.2) (List.range (List.length (c_children kv.2)))) occs

/-- the finite child-position to ordinal map, keyed like the cell map, so a child slot is one O(1) lookup -/
def slotmap (occs : List (Nat × Cell)) : Collections.NodeMap.t Nat :=
  List.foldr (fun p m => Collections.NodeMap.add (p.1 + 1) p.2 m)
             (Collections.NodeMap.empty Nat) (child_slots occs)

/-- the exact ordinal a position occupies in its parent, zero only for the parentless file root -/
def slot_at (occs : List (Nat × Cell)) (pos : Nat) : Nat :=
  match Collections.NodeMap.find (pos + 1) (slotmap occs) with | some k => k | none => 0

/-- one linear decoration pass folded into construction: each cell gains its exact parent slot, nothing else
    moves -/
def assign_slots (occs : List (Nat × Cell)) : List (Nat × Cell) :=
  List.map (fun kv => (kv.1, set_slot (slot_at occs kv.1) kv.2)) occs

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure FileInfo : Type where
  mkFileInfo ::
  fi_cells : Collections.NodeMap.t Cell
  fi_count : Nat

export FileInfo (mkFileInfo fi_cells fi_count)

/-- one structural pass: `number_file` is evaluated once, decorated with parent slots, and reused for map and
    count -/
def build_fileinfo (f : Syntax.File) : FileInfo :=
  let occs := number_file f
  mkFileInfo (posmap_of (assign_slots occs)) (List.length occs)

def raw_index (p : Syntax.Program) : Collections.FileMap.t FileInfo :=
  Collections.FileMap.map build_fileinfo (Syntax.files p)

end Fido.Index.Build
