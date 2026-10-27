import QCryptLean.LOCC.MultipartiteSystem

/-!
# Branch-dependent output boundaries

This module records the finite public branching at the output of a LOCC program. Leaves carry
multipartite systems, while public nodes retain the announced value that selects the remaining
boundary.
-/

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A finite public tree of possible output multipartite systems.

The public constructor represents the measurement-history tree used for finite-round LOCC in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II: later local instruments may
depend on the already announced outcomes. This type records only that public control flow; quantum
actions are carried separately by `Program`. -/
inductive Boundary (P : Type) [Fintype P] [DecidableEq P] : Type 1
  /-- A completed branch with its final multipartite system. -/
  | leaf (system : MultipartiteSystem P) : Boundary P
  /-- A finite public announcement followed by an announcement-indexed boundary. -/
  | announce (Y : Type) [Fintype Y] [DecidableEq Y] (next : Y → Boundary P) : Boundary P

namespace Boundary

/-- The finite syntactic type of declared complete public exits from a boundary.

This includes every declared public label, whether or not a particular program can physically
reach that label. -/
def Exit (B : Boundary P) : Type :=
  match B with
  | @Boundary.leaf _ _ _ _ => Unit
  | @Boundary.announce _ _ _ Y _ _ next => Σ y : Y, (next y).Exit

/-- The final multipartite system selected by a complete public exit. -/
noncomputable def system (B : Boundary P) : B.Exit → MultipartiteSystem P :=
  -- Primitive recursion keeps dependent lookups from expanding course-of-values tables.
  Boundary.rec (motive := fun B => B.Exit → MultipartiteSystem P)
    (fun R _ => R) (fun _ _ _ _ systems e => systems e.1 e.2) B

/-- Every exit from a leaf selects the system carried by that leaf. -/
@[simp] theorem system_leaf (R : MultipartiteSystem P) (e : (leaf R).Exit) :
    (leaf R).system e = R := rfl

/-- An announced exit selects the system of its continuation exit. -/
@[simp] theorem system_announce {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P) (e : (announce Y next).Exit) :
    (announce Y next).system e = (next e.1).system e.2 := rfl

/-- The finite classical-quantum output space associated with a boundary.

An exit identifies a declared public branch, and its fibre is the joint quantum register at that
branch's final multipartite system. This is a syntactic output space and need not be the reachable
support of a particular program. -/
abbrev space (B : Boundary P) : Type := Σ e : B.Exit, (B.system e).total

/-- Complete exits form a finite type. -/
instance instFintypeExit (B : Boundary P) : Fintype B.Exit :=
  match B with
  | @Boundary.leaf _ _ _ _ => inferInstanceAs (Fintype Unit)
  | @Boundary.announce _ _ _ Y instY _ next =>
      letI := instY
      letI (y : Y) := instFintypeExit (next y)
      inferInstanceAs (Fintype (Σ y : Y, (next y).Exit))

/-- Complete exits have decidable equality. -/
instance instDecidableEqExit (B : Boundary P) : DecidableEq B.Exit :=
  match B with
  | @Boundary.leaf _ _ _ _ => inferInstanceAs (DecidableEq Unit)
  | @Boundary.announce _ _ _ Y _ decY next =>
      letI := decY
      letI (y : Y) := instDecidableEqExit (next y)
      inferInstanceAs (DecidableEq (Σ y : Y, (next y).Exit))

/-- A completed branch has exactly one complete public exit. -/
instance instUniqueLeafExit (R : MultipartiteSystem P) : Unique (Boundary.leaf R).Exit where
  default := ()
  uniq x := by
    cases x
    rfl

/-- A boundary with an exit and nonempty output fibres has a nonempty output space. -/
instance instNonemptySpace (B : Boundary P) [Nonempty B.Exit]
    [∀ e, Nonempty (B.system e).total] : Nonempty B.space :=
  (inferInstance : Nonempty B.Exit).elim fun e =>
    (inferInstance : Nonempty (B.system e).total).elim fun x => ⟨⟨e, x⟩⟩

/-- Replace every leaf of `B` by the boundary assigned to its complete exit. -/
def graft (B : Boundary P) (C : B.Exit → Boundary P) : Boundary P :=
  match B with
  | @Boundary.leaf _ _ _ _ => C ()
  | @Boundary.announce _ _ _ Y instY decY next =>
      @Boundary.announce P _ _ Y instY decY fun y =>
        (next y).graft fun e => C ⟨y, e⟩

/-- Complete exits of a graft are canonically a base exit together with an exit in its attached
boundary.

This is the dependent associativity equivalence for the public measurement-history tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
def graftExitEquiv (B : Boundary P) (C : B.Exit → Boundary P) :
    (B.graft C).Exit ≃ Σ e : B.Exit, (C e).Exit :=
  match B with
  | @Boundary.leaf _ _ _ _ =>
      { toFun := fun e => ⟨(), e⟩
        invFun := fun e => e.2
        left_inv := fun _ => rfl
        right_inv := fun e => by cases e with | mk e x => cases e; rfl }
  | @Boundary.announce _ _ _ Y _ _ next =>
      (Equiv.sigmaCongrRight fun y =>
          graftExitEquiv (next y) (fun e => C ⟨y, e⟩)).trans
        (Equiv.sigmaAssoc (fun y e => (C ⟨y, e⟩).Exit)).symm

/-- The exit equivalence for a graft preserves the final quantum-register multipartite system. -/
@[simp] theorem system_graftExitEquiv_symm (B : Boundary P) (C : B.Exit → Boundary P)
    (e : Σ b : B.Exit, (C b).Exit) :
    (B.graft C).system ((B.graftExitEquiv C).symm e) = (C e.1).system e.2 := by
  induction B with
  | leaf R =>
      rcases e with ⟨⟨⟩, e⟩
      rfl
  | @announce Y _ _ next ih =>
      rcases e with ⟨⟨y, b⟩, e⟩
      exact ih y (fun b => C ⟨y, b⟩) ⟨b, e⟩

/-- Forward form of `system_graftExitEquiv_symm`: decomposing a graft exit does not change its final
multipartite system. -/
theorem system_graftExitEquiv (B : Boundary P) (C : B.Exit → Boundary P)
    (e : (B.graft C).Exit) :
    (B.graft C).system e =
      (C ((B.graftExitEquiv C) e).1).system ((B.graftExitEquiv C e).2) := by
  simpa using system_graftExitEquiv_symm B C ((B.graftExitEquiv C) e)

end Boundary
end LOCC
