import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.MultipartiteSystem

/-! # Graft -/


open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Boundary

/-- The output space of a graft is canonically the dependent sum of the spaces attached to the
base boundary's complete exits.

The forward direction is from the native `Boundary.graft` coordinate space to
`Σ e : B.Exit, (C e).space`, preserving the terminal registers in each fibre. -/
def graftSpaceEquiv (B : Boundary P) (C : B.Exit → Boundary P) :
    (B.graft C).space ≃ Σ e : B.Exit, (C e).space :=
  match B with
  | @Boundary.leaf _ _ _ _ =>
      { toFun := fun x => ⟨(), x⟩
        invFun := fun x => x.2
        left_inv := fun _ => rfl
        right_inv := fun x => by
          rcases x with ⟨⟨⟩, x⟩
          rfl }
  | @Boundary.announce _ _ _ Y _ _ next =>
      (publicSpaceEquiv (fun y => (next y).graft fun e => C ⟨y, e⟩)).trans
        ((Equiv.sigmaCongrRight fun y =>
          graftSpaceEquiv (next y) fun e => C ⟨y, e⟩).trans
          (Equiv.sigmaAssoc fun y e => (C ⟨y, e⟩).space).symm)

/-- At a terminal boundary, the graft-space equivalence adds the unique base exit. -/
@[simp] theorem graftSpaceEquiv_leaf_apply (R : MultipartiteSystem P)
    (C : (Boundary.leaf R).Exit → Boundary P) (x : (C ()).space) :
    graftSpaceEquiv (.leaf R) C x = ⟨(), x⟩ :=
  rfl

/-- At an announced boundary, the graft-space equivalence exposes the outer public outcome and
then recursively exposes the continuation exit. -/
@[simp] theorem graftSpaceEquiv_announce_apply {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P) (C : (Boundary.announce Y next).Exit → Boundary P)
    (x : (Boundary.announce Y (fun y => (next y).graft fun e => C ⟨y, e⟩)).space) :
    graftSpaceEquiv (.announce Y next) C x =
      ⟨⟨x.1.1, ((next x.1.1).graftSpaceEquiv (fun e => C ⟨x.1.1, e⟩)
        ⟨x.1.2, x.2⟩).1⟩,
        ((next x.1.1).graftSpaceEquiv (fun e => C ⟨x.1.1, e⟩)
          ⟨x.1.2, x.2⟩).2⟩ :=
  rfl

/-- The graft-space equivalence exposes both the decomposed graft exit and the leaf payload
transported along the canonical equality of its selected multipartite systems. -/
@[simp] theorem graftSpaceEquiv_apply (B : Boundary P) (C : B.Exit → Boundary P)
    (x : (B.graft C).space) :
    graftSpaceEquiv B C x =
      ⟨(graftExitEquiv B C x.1).1,
        ⟨(graftExitEquiv B C x.1).2,
          Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
            (system_graftExitEquiv B C x.1)) x.2⟩⟩ := by
  induction B with
  | leaf R => rfl
  | @announce Y _ _ next ih =>
      rcases x with ⟨⟨y, e⟩, q⟩
      exact congrArg (fun z : Σ f : (next y).Exit, (C ⟨y, f⟩).space =>
        (⟨⟨y, z.1⟩, z.2⟩ : Σ f : (Boundary.announce Y next).Exit, (C f).space))
          (ih y (fun f => C ⟨y, f⟩) ⟨e, q⟩)

/-- The base public exit exposed by `graftSpaceEquiv` is exactly the base component exposed by
`graftExitEquiv`. Thus the forward reindex orientation agrees at the type and matrix layers. -/
theorem graftSpaceEquiv_fst (B : Boundary P) (C : B.Exit → Boundary P)
    (x : (B.graft C).space) :
    (graftSpaceEquiv B C x).1 = (graftExitEquiv B C x.1).1 := by
  induction B with
  | leaf R => rfl
  | @announce Y _ _ next ih =>
      rcases x with ⟨⟨y, e⟩, a⟩
      change
        (⟨y, (graftSpaceEquiv (next y) (fun e => C ⟨y, e⟩) ⟨e, a⟩).1⟩ :
          (Boundary.announce Y next).Exit) =
        (⟨y, (graftExitEquiv (next y) (fun e => C ⟨y, e⟩) e).1⟩ :
          (Boundary.announce Y next).Exit)
      exact congrArg (Sigma.mk y)
        (ih y (fun e => C ⟨y, e⟩) ⟨e, a⟩)

/-- When every continuation boundary has a unique public exit, two graft-space coordinates over
the same base exit select the same native graft exit. -/
theorem graftSpaceEquiv_symm_fst_eq_of_subsingleton (B : Boundary P)
    (C : B.Exit → Boundary P) [∀ e, Subsingleton (C e).Exit]
    (e : B.Exit) (a b : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, a⟩).1 =
      ((graftSpaceEquiv B C).symm ⟨e, b⟩).1 := by
  apply (graftExitEquiv B C).injective
  have hbase :
      (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1).1 =
        (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1).1 := by
    calc
      (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1).1 =
          (graftSpaceEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩)).1 :=
        (graftSpaceEquiv_fst B C _).symm
      _ = e := congrArg Sigma.fst ((graftSpaceEquiv B C).apply_symm_apply ⟨e, a⟩)
      _ = (graftSpaceEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩)).1 :=
        (congrArg Sigma.fst ((graftSpaceEquiv B C).apply_symm_apply ⟨e, b⟩)).symm
      _ = (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1).1 :=
        graftSpaceEquiv_fst B C _
  apply Sigma.ext hbase
  let u := graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1
  let v := graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1
  let htype : (C u.1).Exit = (C v.1).Exit := congrArg (fun f => (C f).Exit) hbase
  exact (cast_heq htype u.2).symm.trans
    (heq_of_eq (Subsingleton.elim (cast htype u.2) v.2))

/-- The complete exit of a point named in graft coordinates is the graft exit of its base exit and
continuation exit. -/
theorem graftSpaceEquiv_symm_fst (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (r : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, r⟩).1 = (graftExitEquiv B C).symm ⟨e, r.1⟩ := by
  induction B with
  | leaf S =>
      cases e
      rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact congrArg (Sigma.mk y) (ih y (fun f => C ⟨y, f⟩) e r)

/-- The payload of a point named in graft coordinates is the attached payload. -/
theorem graftSpaceEquiv_symm_snd_heq (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (r : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, r⟩).2 ≍ r.2 := by
  induction B with
  | leaf S =>
      cases e
      exact HEq.rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact ih y (fun f => C ⟨y, f⟩) e r

/-- The multipartite system transport attached to a decomposed graft exit. -/
abbrev graftSystemCast (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit) (f : (C e).Exit) :
    ((B.graft C).system ((graftExitEquiv B C).symm ⟨e, f⟩)).total ≃ ((C e).system f).total :=
  Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
    (system_graftExitEquiv_symm B C ⟨e,
    f⟩))

/-- Fully decomposed inverse of the graft-space equivalence. -/
theorem graftSpaceEquiv_symm_pair (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (f : (C e).Exit) (q : ((C e).system f).total) :
    (graftSpaceEquiv B C).symm ⟨e, ⟨f, q⟩⟩ =
      ⟨(graftExitEquiv B C).symm ⟨e, f⟩, (graftSystemCast B C e f).symm q⟩ := by
  refine Sigma.ext (graftSpaceEquiv_symm_fst B C e ⟨f, q⟩) ?_
  refine (graftSpaceEquiv_symm_snd_heq B C e ⟨f, q⟩).trans ?_
  exact (cast_heq _ q).symm

end Boundary
end LOCC
