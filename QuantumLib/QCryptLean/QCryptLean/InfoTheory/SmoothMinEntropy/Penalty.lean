import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Kernel
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelMetric
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.RegisterExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.InfoTheory.SmoothMinEntropy.StateOrder
import QCryptLean.Math.LinearAlgebra.Matrix.TensorOrder
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Penalty -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {C D Q R : Type*} [Fintype C] [Fintype D] [Fintype Q] [Fintype R]

/-- Filtering fine outcomes before coarsening cannot decrease extended smooth entropy. -/
theorem smoothMinEntropy_coarsen_filterKeep_ge [DecidableEq D] [Nonempty D] [Nonempty Q]
    (ε : ℝ) (g : C → D) (keep : C → Bool) (ρ : CQState C Q) (σ : SubDensityOp Q) :
    smoothMinEntropy ε (ρ.coarsen g) σ ≤
      smoothMinEntropy ε ((ρ.filterKeep keep).coarsen g) σ := by
  apply smoothMinEntropy_mono_state
  intro d
  apply Matrix.le_iff.mpr
  change ((∑ c, if g c = d then (ρ.stateMap c).toOp else 0) -
    ∑ c, if g c = d then ((ρ.filterKeep keep).stateMap c).toOp else 0).PosSemidef
  rw [← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro c _
  by_cases hc : g c = d
  · cases hk : keep c <;> simp only [hc, ↓reduceIte, CQState.filterKeep, hk,
      Bool.false_eq_true, SubDensityOp.zero, sub_zero, sub_self]
    · exact (ρ.stateMap c).posSemidef
    · exact PosSemidef.zero
  · simpa only [hc, ↓reduceIte, sub_self] using (PosSemidef.zero : (0 : Op Q).PosSemidef)

variable [DecidableEq C] [Nonempty C] [Nonempty Q] [Nonempty R] [DecidableEq R]

omit [Nonempty C] [Nonempty Q] in
/-- The left announcement charge is exactly the positive part of `log₂ c`. -/
theorem smoothMinEntropy_le_tensorLeftKernel_add (ε : ℝ) (ρ : CQState C Q)
    (σ : SubDensityOp Q) (K : C → SubDensityOp R) {c : ℝ} (hc : 1 ≤ c)
    (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, OpLe (K x).toOp ((c : ℂ) • (DensityOp.maxMixed (X := R)).toOp)) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.tensorLeftKernel K)
        ((DensityOp.maxMixed (X := R)).toSubDensityOp.kronecker σ) +
      ENNReal.ofReal (Real.log c / Real.log 2) := by
  apply smoothMinEntropy_le_add_of_feasible_transport _ _ _ _ _ _ _
    (div_nonneg (Real.log_nonneg hc) (Real.log_pos one_lt_two).le)
  intro τ hd
  refine ⟨τ.tensorLeftKernel K, (ρ.purifiedDistance_tensorLeftKernel_le τ K hK).trans hd, ?_⟩
  intro t ht
  have hc0 := (zero_lt_one.trans_le hc).le
  have he : (2 : ℝ) ^ (Real.log c / Real.log 2) = c :=
    Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hc)
  rw [he]
  refine ⟨mul_nonneg hc0 ht.1, fun z => opLe_of_posSemidef_sub ?_⟩
  have hleft := (opLe_iff_posSemidef_sub (K z).isHermitian
    (DensityOp.maxMixed.posSemidef.smul (Complex.zero_le_real.mpr hc0)).isHermitian).mp (hdom z)
  have hright := (opLe_iff_posSemidef_sub (τ.stateMap z).isHermitian
    (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 z)
  have h := Matrix.le_iff.mp (Matrix.kronecker_mono (K z).posSemidef (τ.stateMap z).posSemidef
    (Matrix.le_iff.mpr hleft) (Matrix.le_iff.mpr hright))
  convert h using 1
  simp only [CQState.tensorLeftKernel, SubDensityOp.kronecker, DensityOp.toSubDensityOp,
    smul_kronecker, kronecker_smul, smul_smul, Complex.ofReal_mul, mul_comm (c : ℂ)]

omit [Nonempty C] in
/-- A correlated extension costs at most twice the logarithm of the reference cardinality. -/
theorem smoothMinEntropy_le_extension_add_of_partialTraceRight_eq
    (ρQR : CQState C (Q × R)) (ρ : CQState C Q) (σ : SubDensityOp Q)
    (hblocks : ∀ c, Matrix.partialTraceRight (ρQR.stateMap c).toOp = (ρ.stateMap c).toOp)
    (ε : ℝ) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε ρQR (σ.kronecker (DensityOp.maxMixed (X := R)).toSubDensityOp) +
        ENNReal.ofReal (2 * Real.log (Fintype.card R : ℝ) / Real.log 2) := by
  have he : ρQR.partialTraceRight = ρ := by
    ext c i j
    exact congrFun (congrFun (hblocks c) i) j
  simpa only [he, Real.logb, mul_div_assoc] using smoothMinEntropy_le_extension_add ρQR σ ε

omit [DecidableEq R] [Nonempty C] [Nonempty Q] [Nonempty R] in
/-- A decoupled subnormalized ancilla referenced to itself has no entropy charge,
including the zero ancilla. -/
theorem smoothMinEntropy_le_condTensor_decoupled_ancilla (ε : ℝ) (ρ : CQState C Q)
    (ρQR : CQState C (Q × R)) (σ : SubDensityOp Q) (τ : SubDensityOp R)
    (hproduct : ∀ c, (ρQR.stateMap c).toOp = ((ρ.stateMap c).kronecker τ).toOp) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε ρQR (σ.kronecker τ) := by
  have he : ρQR = ρ.tensorRightKernel (fun _ => τ) := by
    ext c i j
    exact congrFun (congrFun (hproduct c) i) j
  rw [he]
  have h := smoothMinEntropy_le_add_of_feasible_transport ρ σ
    (ρ.tensorRightKernel (fun _ => τ)) (σ.kronecker τ) ε ε 0 le_rfl ?_
  · simpa only [ENNReal.ofReal_zero, add_zero] using h
  intro υ hd
  refine ⟨υ.tensorRightKernel (fun _ => τ),
    (ρ.purifiedDistance_tensorRight_const_le υ τ).trans hd, ?_⟩
  intro t ht
  simp only [Real.rpow_zero, one_mul]
  refine ⟨ht.1, fun c => opLe_of_posSemidef_sub ?_⟩
  have hb := (opLe_iff_posSemidef_sub (υ.stateMap c).isHermitian
    (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c)
  convert hb.kronecker τ.posSemidef using 1
  ext i j
  simp only [CQState.tensorRightKernel_stateMap, SubDensityOp.kronecker,
    Matrix.sub_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul]
  ring

end InfoTheory.SmoothMinEntropy
