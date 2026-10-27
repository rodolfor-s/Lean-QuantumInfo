import QCryptLean.InfoTheory.SmoothMinEntropy.Bipartite
import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedOrder
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Bipartite Regularity -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B : Type*} [Fintype A] [Fintype B]

/-- The infimum of feasible domination scales is nonnegative, including the empty domain. -/
theorem dmaxScale_nonneg (ρ σ : Op A) : 0 ≤ dmaxScale ρ σ := by
  unfold dmaxScale
  by_cases h : (Set.ofPred (IsDmaxFeasible ρ σ)).Nonempty
  · exact le_csInf h (fun _ ht => ht.1)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty]

/-- Nonzero positive subnormalized states have positive real trace. -/
theorem subDensity_trace_re_pos (ρ : SubDensityOp A) (hρ : ρ.toOp ≠ 0) :
    0 < ρ.toOp.trace.re := by
  apply lt_of_le_of_ne ρ.trace_nonneg
  intro h
  apply hρ
  apply ρ.posSemidef.trace_eq_zero_iff.mp
  exact Complex.ext h.symm ρ.trace_im

variable [DecidableEq A]

/-- Tracing domination bounds its scale below, uniformly over subnormalized references. -/
theorem trace_div_card_le_dmaxScale [Nonempty A]
    (ρ : SubDensityOp (A × B)) (σ : SubDensityOp B)
    (hfeas : HasDmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp)) :
    ρ.trace / Fintype.card A ≤ dmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) := by
  have hc : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  apply le_csInf hfeas
  rintro t ⟨ht, hle⟩
  rw [div_le_iff₀ hc]
  have hp := (opLe_iff_posSemidef_sub ρ.isHermitian
    ((PosSemidef.one.kronecker σ.posSemidef).smul
      (Complex.nonneg_iff.mpr ⟨ht, rfl⟩)).isHermitian).mp hle
  have htr := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  have hr : (((t : ℂ) • ((1 : Op A) ⊗ₖ σ.toOp)) - ρ.toOp).trace.re =
      t * ((Fintype.card A : ℝ) * σ.trace) - ρ.trace := by
    simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_kronecker,
      SubDensityOp.trace, Complex.mul_re]
  rw [hr] at htr
  have hb := mul_le_mul_of_nonneg_left σ.trace_le_one (mul_nonneg ht hc.le)
  dsimp [SubDensityOp.trace] at *
  nlinarith

/-- The maximally mixed reference makes the guarded optimization domain nonempty. -/
theorem nonempty_bipartiteMinEntropySet [Nonempty B] (ρ : SubDensityOp (A × B)) :
    {h | ∃ σ : SubDensityOp B, HasDmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) ∧
      h = bipartiteMinEntropyReal ρ σ}.Nonempty := by
  classical
  let σ := (DensityOp.maxMixed (X := B)).toSubDensityOp
  refine ⟨_, σ, ⟨Fintype.card B * ρ.trace, mul_nonneg (Nat.cast_nonneg _) ρ.trace_nonneg, ?_⟩,
    rfl⟩
  have he : ((Fintype.card B * ρ.trace : ℝ) : ℂ) • ((1 : Op A) ⊗ₖ σ.toOp) =
      (ρ.trace : ℂ) • (1 : Op (A × B)) := by
    change _ • ((1 : Op A) ⊗ₖ (((Fintype.card B : ℝ)⁻¹ : ℂ) • (1 : Op B))) = _
    rw [Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [he]
  exact opLe_of_posSemidef_sub (Matrix.le_iff.mp ρ.posSemidef.le_re_trace_smul_one)

/-- A nonzero state has a positive scale against every feasible reference. -/
theorem dmaxScale_pos_of_ne_zero [Nonempty A]
    (ρ : SubDensityOp (A × B)) (hρ : ρ.toOp ≠ 0) (σ : SubDensityOp B)
    (hfeas : HasDmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp)) :
    0 < dmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) :=
  (div_pos (subDensity_trace_re_pos ρ hρ) (Nat.cast_pos.mpr Fintype.card_pos)).trans_le
    (trace_div_card_le_dmaxScale ρ σ hfeas)

/-- A positive trace lower bound uniformly bounds guarded optimized entropy above. -/
theorem bipartiteMinEntropyOptReal_le_of_trace_le [Nonempty A] [Nonempty B]
    (ρ : SubDensityOp (A × B)) {t : ℝ} (ht : 0 < t) (htr : t ≤ ρ.trace) :
    bipartiteMinEntropyOptReal ρ ≤ -Real.log (t / Fintype.card A) / Real.log 2 := by
  apply csSup_le (nonempty_bipartiteMinEntropySet ρ)
  rintro h ⟨σ, hfeas, rfl⟩
  have hc : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have hb := (div_le_div_of_nonneg_right htr hc.le).trans
    (trace_div_card_le_dmaxScale ρ σ hfeas)
  unfold bipartiteMinEntropyReal
  exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log (div_pos ht hc) hb))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The guarded fixed-state reference domain is bounded above, including at the zero state. -/
theorem bddAbove_bipartiteMinEntropySet [Nonempty A] (ρ : SubDensityOp (A × B)) :
    BddAbove {h | ∃ σ : SubDensityOp B, HasDmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) ∧
      h = bipartiteMinEntropyReal ρ σ} := by
  by_cases hρ : ρ.toOp = 0
  · refine ⟨0, ?_⟩
    rintro h ⟨σ, _, rfl⟩
    have hz : dmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) = 0 := by
      apply le_antisymm _ (dmaxScale_nonneg _ _)
      apply dmaxScale_le_of_isDmaxFeasible _ _
      refine ⟨le_rfl, ?_⟩
      rw [hρ, Complex.ofReal_zero, zero_smul]
      exact OpLe.refl _
    simp [bipartiteMinEntropyReal, hz]
  · refine ⟨-Real.log (ρ.trace / Fintype.card A) / Real.log 2, ?_⟩
    rintro h ⟨σ, hf, rfl⟩
    have hc : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
    exact div_le_div_of_nonneg_right
      (neg_le_neg (Real.log_le_log (div_pos (subDensity_trace_re_pos ρ hρ) hc)
        (trace_div_card_le_dmaxScale ρ σ hf))) (Real.log_pos (by norm_num)).le

omit [DecidableEq A] in
/-- A ball of radius below one around a normalized state excludes zero. -/
theorem ne_zero_of_purifiedDistance_of_normalized (ρ τ : SubDensityOp A)
    (hρ : ρ.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hd : purifiedDistance ρ τ ≤ ε) : τ.toOp ≠ 0 := by
  have ht := ρ.one_sub_sq_le_trace_of_purifiedDistance_le τ hρ hd
  intro hz
  simp only [SubDensityOp.trace, hz, Matrix.trace_zero, Complex.zero_re] at ht
  nlinarith

/-- A normalized center and radius below one bound the entire smoothing domain. -/
theorem smoothBipartiteMinSet_bddAbove_of_normalized [Nonempty A] [Nonempty B]
    (ρ : SubDensityOp (A × B)) (hρ : ρ.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    BddAbove (Set.ofPred (IsInSmoothBipartiteMinSet ε ρ)) := by
  refine ⟨-Real.log ((1 - ε ^ 2) / Fintype.card A) / Real.log 2, ?_⟩
  rintro h ⟨τ, hd, rfl⟩
  exact bipartiteMinEntropyOptReal_le_of_trace_le τ (by nlinarith)
    (ρ.one_sub_sq_le_trace_of_purifiedDistance_le τ hρ hd)

end InfoTheory.SmoothMinEntropy
