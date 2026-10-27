import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.Quantum.Operators.Basic

/-! # Exit Weight -/


open scoped Matrix BigOperators ComplexOrder

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Reindexing a register along a bijection preserves the trace. -/
theorem trace_reindexOp {HH HH' : Type} [Fintype HH] [Fintype HH']
    (e : HH ≃ HH') (M : Op HH) : ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap M).trace =
       M.trace :=
  Fintype.sum_equiv e.symm _ _ fun _ => rfl

namespace Boundary

/-- **The diagonal mass of a set of complete public exits.**

For an operator `M` on the output space, `B.exitWeight E M` is the real part of the trace of the
blocks of `M` at the complete public exits satisfying `E`. For the output state of a run it is the
probability that the run ends at an exit in `E`. -/
noncomputable def exitWeight (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    (M : Op B.space) : ℝ :=
  ∑ q : B.space, if E q.1 then (M q q).re else 0

/-- The exit weight only depends on which exits satisfy the predicate. -/
theorem exitWeight_congr (B : Boundary P) {E E' : B.Exit → Prop} [DecidablePred E]
    [DecidablePred E'] (h : ∀ e, E e ↔ E' e) (M : Op B.space) :
    B.exitWeight E M = B.exitWeight E' M := by
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : E q.1
  · rw [ite_eq_left hq, ite_eq_left ((h q.1).mp hq)]
  · rw [ite_eq_right hq, ite_eq_right (fun h' => hq ((h q.1).mpr h'))]

/-- **Complementary exit sets partition the trace.** -/
theorem exitWeight_add_exitWeight_not (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    (M : Op B.space) :
    B.exitWeight E M + B.exitWeight (fun e => ¬ E e) M = (Matrix.trace M).re := by
  simp only [exitWeight, ← Finset.sum_add_distrib, Matrix.trace, Matrix.diag, Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : E q.1 <;> simp [hq]

/-- The exit weight of the set of all exits is the real part of the trace. -/
theorem exitWeight_true (B : Boundary P) (M : Op B.space) :
    B.exitWeight (fun _ => True) M = (Matrix.trace M).re := by
  simp [exitWeight, Matrix.trace, Complex.re_sum]

/-- The exit weight of the empty set of exits is zero. -/
theorem exitWeight_false (B : Boundary P) (M : Op B.space) :
    B.exitWeight (fun _ => False) M = 0 := by
  simp [exitWeight]

/-- A positive semidefinite output assigns nonnegative weight to every set of exits. -/
theorem exitWeight_nonneg (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ B.exitWeight E M := by
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · exact (Complex.nonneg_iff.mp hM.diag_nonneg).1
  · exact le_rfl

/-- **The exit weight of a diagonal pushforward.** If every diagonal entry of `M` collects the
weights `w i` of the indices `i` that `p` sends to it, then the weight of a set of exits collects
the real weights of the indices sent into it. -/
theorem exitWeight_eq_sum_of_diag {ι : Type} [Fintype ι] (B : Boundary P) (E : B.Exit → Prop)
    [DecidablePred E] (M : Op B.space) (p : ι → B.space) (w : ι → ℂ)
    (hM : ∀ q, M q q = ∑ i, if p i = q then w i else 0) :
    B.exitWeight E M = ∑ i, if E (p i).1 then (w i).re else 0 := by
  unfold exitWeight
  simp_rw [hM]
  calc
    _ = ∑ q : B.space, ∑ i, if p i = q then (if E q.1 then (w i).re else 0) else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : E q.1
      · rw [ite_eq_left hq, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      · rw [ite_eq_right hq]
        symm
        exact Finset.sum_eq_zero fun i _ => by split_ifs <;> rfl
    _ = ∑ i, ∑ q : B.space, if p i = q then (if E q.1 then (w i).re else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq]
      simp

/-- The weight of a set of exits is at most the real part of the trace of a positive semidefinite
output. -/
theorem exitWeight_le_trace (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    {M : Op B.space} (hM : M.PosSemidef) : B.exitWeight E M ≤ (Matrix.trace M).re := by
  rw [← B.exitWeight_add_exitWeight_not E M]
  exact le_add_of_nonneg_right (B.exitWeight_nonneg _ hM)

/-- A change of output coordinates preserves the mass of corresponding exit predicates. -/
theorem exitWeight_reindexOp {B C : Boundary P} (F : B.space ≃ C.space)
    (E : B.Exit → Prop) (D : C.Exit → Prop) [DecidablePred E] [DecidablePred D]
    (h : ∀ q : B.space, E q.1 ↔ D (F q).1) (rho : Op B.space) :
    C.exitWeight D ((Matrix.reindexLinearEquiv ℂ ℂ F F).toLinearMap rho) = B.exitWeight E rho := by
  classical
  rw [exitWeight, ← F.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  change (if D (F q).1 then (rho (F.symm (F q)) (F.symm (F q))).re else 0) = _
  rw [F.symm_apply_apply]
  exact if_congr (h q).symm rfl rfl

end Boundary

namespace Program

variable [SystemPresentation P] {End : MultipartiteSystem P → Type 1}

/-- **A program preserves the trace of every operator.** This is the completeness of the
flattened path instrument (`Program.kraus_complete`). -/
theorem trace_denote {R : MultipartiteSystem P} (p : Program R End) (ρ : Op R.total) :
    (p.denote ρ).trace = ρ.trace := by
  rw [← p.toInstrument_channel]
  exact Instrument.channel_trace_eq p.toInstrument ρ

/-- **A program maps positive semidefinite operators to positive semidefinite operators.** -/
theorem posSemidef_denote {R : MultipartiteSystem P} (p : Program R End) {ρ : Op
    R.total}
    (hρ : ρ.PosSemidef) : (p.denote ρ).PosSemidef := by
  rw [denote_eq_krausSum, LinearMap.sum_apply]
  exact Matrix.posSemidef_sum _ fun b _ => hρ.mul_mul_conjTranspose_same (p.kraus b)

/-- The weight of public branches is the sum of their continuation weights. -/
theorem exitWeight_announced_denote {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y] (a : AnnouncedAction R Y) (e : a.Outcome ≃ Y)
    (he : ∀ o, a.announce o = e o)
    (k : ∀ y, Program (SystemPresentation.update R a.actor (a.Output y)) End)
    (E : ∀ y, (k y).boundary.Exit → Prop) [∀ y, DecidablePred (E y)]
    (rho : Op R.total) :
    (a.then k).boundary.exitWeight (fun f => E f.1 f.2) ((a.then k).denote rho) =
      ∑ o, (k (a.announce o)).boundary.exitWeight (E (a.announce o))
        ((k (a.announce o)).denote (a.successorOperation o rho)) := by
  classical
  let B := fun y => (k y).boundary
  let F := (Boundary.publicSpaceEquiv B).symm
  rw [Boundary.exitWeight, ← F.sum_comp]
  rw [Fintype.sum_sigma]
  change (∑ y, ∑ q : (k y).boundary.space,
    if E y q.1 then ((a.then k).denote rho (F ⟨y, q⟩) (F ⟨y, q⟩)).re else 0) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro o _
  rw [← he o]
  apply Finset.sum_congr rfl
  intro q _
  rw [denote_then_publicSpaceEquiv_symm_apply a e he]
  rfl

end Program

end LOCC
