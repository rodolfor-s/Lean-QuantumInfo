import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.Direct
import QCryptLean.InfoTheory.QuantumLHL.CollisionAverage
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleRegularization
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Math.LinearAlgebra.Matrix.WeightedCollision
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Metrics.WeightedTraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Seed Collision -/


noncomputable section
namespace InfoTheory.QuantumLHL.SeedKey
open Matrix Quantum.Operators Quantum.Metrics
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder
variable {S C Z Q : Type*} [Fintype S] [Nonempty S] [Fintype C]
  [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype Q]

/-- The unscaled hash block after subtracting the uniform quantum marginal. -/
def centeredBlock (H : HashFamily S C Z) (ρ : CQState C Q) (s : S) (z : Z) : Op Q :=
  (∑ c, if H.hash s c = z then (ρ.stateMap c).toOp else 0) -
    (Fintype.card Z : ℂ)⁻¹ • ρ.quantumMarginal.toOp

omit [Fintype S] [Nonempty S] in
/-- A centered quantum hash block is Hermitian. -/
theorem centeredBlock_isHermitian (H : HashFamily S C Z) (ρ : CQState C Q) (s : S) (z : Z) :
    (centeredBlock H ρ s z).IsHermitian := by
  have he : (∑ c, if H.hash s c = z then (ρ.stateMap c).toOp else 0).PosSemidef :=
    posSemidef_sum _ fun c _ => by
      split_ifs
      · exact (ρ.stateMap c).posSemidef
      · exact Matrix.PosSemidef.zero
  exact he.isHermitian.sub ((ρ.quantumMarginal.posSemidef.smul (by positivity)).isHermitian)

/-- Hashing error equals half the average sum of centered block trace norms. -/
theorem traceDistanceGen_output_eq_half_average [DecidableEq S]
    (H : HashFamily S C Z) (ρ : CQState C Q) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp =
    (1 / 2) * ((Fintype.card S : ℝ)⁻¹ *
      ∑ sz : S × Z, traceNorm (centeredBlock H ρ sz.1 sz.2)) := by
  classical
  have ho : ((output H ρ).toJointDensity.toOp).trace = ρ.quantumMarginal.toOp.trace := by
    change (blockDiagonal (fun sz : S × Z => weightedOp H ρ sz.1 sz.2)).trace = _
    rw [trace_blockDiagonal]
    calc
      _ = (∑ sz : S × Z, weightedOp H ρ sz.1 sz.2).trace := (Matrix.trace_sum _ _).symm
      _ = _ := congrArg Matrix.trace (sum_weightedOp H ρ)
  have hu : ((uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp).trace =
      ρ.quantumMarginal.toOp.trace := by
    change (blockDiagonal (fun _ : S × Z =>
      (↑((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) • ρ.quantumMarginal.toOp)).trace = _
    simp only [trace_blockDiagonal, trace_smul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := S × Z))), one_mul]
  have hb (sz : S × Z) : weightedOp H ρ sz.1 sz.2 -
      (↑((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) • ρ.quantumMarginal.toOp =
      (↑((Fintype.card S : ℝ)⁻¹) : ℂ) • centeredBlock H ρ sz.1 sz.2 := by
    ext i j
    simp only [weightedOp, centeredBlock, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, Fintype.card_prod, Nat.cast_mul, one_div,
      Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_mul, _root_.mul_inv_rev]
    ring
  rw [traceDistanceGen, ho, hu, sub_self, Complex.zero_re, abs_zero, mul_zero, add_zero,
    traceDistance]
  change (1 / 2 : ℝ) * traceNorm
    (blockDiagonal (fun sz : S × Z => weightedOp H ρ sz.1 sz.2) -
      blockDiagonal (fun _ : S × Z => (↑((Fintype.card (S × Z) : ℝ)⁻¹) : ℂ) •
        ρ.quantumMarginal.toOp)) = _
  rw [← blockDiagonal_sub, traceNorm_blockDiagonal]
  simp only [Pi.sub_apply]
  simp_rw [hb, traceNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card S : ℝ)⁻¹ by positivity), Finset.mul_sum]

/-- A feasible positive definite reference gives the direct public-seed hashing bound. -/
private theorem traceDistanceGen_output_le_of_isFeasible_posDef [DecidableEq S]
    (H : HashFamily S C Z) (hH : H.IsTwoUniversal) (ρ : CQState C Q)
    (σ : SubDensityOp Q) (hσ : σ.toOp.PosDef) {t : ℝ} (ht : IsFeasible ρ σ t) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
    (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * t) := by
  classical
  let F := CFC.sqrt (CFC.sqrt σ.toOp⁻¹)
  let A (c : C) := F * (ρ.stateMap c).toOp * F
  let D (sz : S × Z) := centeredBlock H ρ sz.1 sz.2
  have hF : F.IsHermitian := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hA (c : C) : (A c).PosSemidef := by
    simpa only [hF.eq] using (ρ.stateMap c).posSemidef.conjTranspose_mul_mul_same F
  have hB (c : C) : (A c * A c).trace.re ≤ t * (ρ.stateMap c).trace := by
    apply PosSemidef.trace_inverse_fourth_sandwich_sq_le (ρ.stateMap c).posSemidef hσ
    apply Matrix.le_iff.mpr
    exact (opLe_iff_posSemidef_sub (ρ.stateMap c).posSemidef.isHermitian
      ((σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian)).mp (ht.2 c)
  have hAsum : (∑ c, (A c * A c).trace.re) ≤ t := by
    apply (Finset.sum_le_sum fun c _ => hB c).trans
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right ht.1 ρ.weight_le_one
  have hcenter := average_trace_centered_hash_sq_le H hH A hA
  have he (s : S) (z : Z) :
      (∑ c, if H.hash s c = z then A c else 0) -
        (Fintype.card Z : ℂ)⁻¹ • ∑ c, A c = F * D (s, z) * F := by
    simp only [D, centeredBlock, CQState.quantumMarginal, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Finset.sum_mul, A]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  simp_rw [he] at hcenter
  have hsq : (Fintype.card S : ℝ)⁻¹ * ∑ sz : S × Z, traceNorm (D sz) ^ 2 ≤ t := by
    calc
      _ ≤ (Fintype.card S : ℝ)⁻¹ * ∑ sz : S × Z,
          σ.toOp.trace.re * ((F * D sz * F) * (F * D sz * F)).trace.re := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro sz _
        exact Quantum.Metrics.traceNorm_sq_le_re_trace_mul_re_trace_sandwich_sq hσ
          (centeredBlock_isHermitian H ρ sz.1 sz.2)
      _ = σ.trace * ((Fintype.card S : ℝ)⁻¹ * ∑ s, ∑ z,
          ((F * D (s, z) * F) * (F * D (s, z) * F)).trace.re) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]
        change _ = σ.toOp.trace.re * _
        ring
      _ ≤ σ.trace * ∑ c, (A c * A c).trace.re :=
        mul_le_mul_of_nonneg_left hcenter σ.trace_nonneg
      _ ≤ σ.trace * t := mul_le_mul_of_nonneg_left hAsum σ.trace_nonneg
      _ ≤ t := mul_le_of_le_one_left ht.1 σ.trace_le_one
  have hcs :=
    InfoTheory.QuantumLHL.SeedKey.sq_seed_average_sum_le_card_output_mul_seed_average_sum_sq
    (fun sz : S × Z => traceNorm (D sz))
  simp only [one_div] at hcs
  have hn : (Fintype.card S : ℝ)⁻¹ * ∑ sz : S × Z, traceNorm (D sz) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * t) := by
    apply Real.le_sqrt_of_sq_le
    exact hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  rw [traceDistanceGen_output_eq_half_average]
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

/-- Every feasible reference, including a singular one, gives the direct hashing bound. -/
theorem traceDistanceGen_output_le_of_isFeasible [DecidableEq S] [Nonempty Q]
    (H : HashFamily S C Z) (hH : H.IsTwoUniversal) (ρ : CQState C Q)
    (σ : SubDensityOp Q) {t : ℝ} (ht : IsFeasible ρ σ t) :
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) ρ.quantumMarginal).toJointDensity.toOp ≤
    (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * t) := by
  let f : ℝ → ℝ := fun u => (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * u)
  have hf : Continuous f := continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))
  have hs : Filter.Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds t) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
  apply ge_of_tendsto' ((hf.tendsto t).comp hs)
  intro n
  obtain ⟨σ', hσ', ht'⟩ := ht.exists_posDef_of_lt
    (lt_add_of_pos_right t (show 0 < 1 / ((n : ℝ) + 1) by positivity))
  exact traceDistanceGen_output_le_of_isFeasible_posDef H hH ρ σ' hσ' ht'

end InfoTheory.QuantumLHL.SeedKey
