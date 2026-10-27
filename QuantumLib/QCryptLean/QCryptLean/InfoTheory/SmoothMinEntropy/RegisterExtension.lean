import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.InfoTheory.SmoothMinEntropy.CQExtensionFiber
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Reduction
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Correlated conditioning-register extensions with the exact dimension penalty

The reference is the original sub-density matrix tensored with the maximally
mixed added register. The operator order is local and no norm instance changes.
-/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker
variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R]
  [DecidableEq R] [Nonempty R]

/-- Adding a correlated register multiplies every feasible scale by its dimension squared. -/
theorem IsFeasible.extension {ρ : CQState C (Q × R)} {σ : SubDensityOp Q} {t : ℝ}
    (ht : IsFeasible ρ.partialTraceRight σ t) :
    IsFeasible ρ (σ.kronecker (DensityOp.maxMixed (X := R)).toSubDensityOp)
      ((Fintype.card R : ℝ) ^ 2 * t) := by
  refine ⟨mul_nonneg (sq_nonneg _) ht.1, fun c => ?_⟩
  have htσ : ((t : ℂ) • σ.toOp).PosSemidef :=
    σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)
  have hd := (opLe_iff_posSemidef_sub
    (ρ.partialTraceRight.stateMap c).isHermitian htσ.isHermitian).mp (ht.2 c)
  have h := (ρ.stateMap c).posSemidef.le_card_smul_partialTraceRight_kronecker_one
  have hm : (Fintype.card R : ℂ) •
      (Matrix.partialTraceRight (ρ.stateMap c).toOp ⊗ₖ (1 : Op R)) ≤
        (Fintype.card R : ℂ) • (((t : ℂ) • σ.toOp) ⊗ₖ (1 : Op R)) := by
    apply Matrix.le_iff.mpr
    have hh := (hd.kronecker (PosSemidef.one : (1 : Op R).PosSemidef)).smul
      (by positivity : (0 : ℂ) ≤ (Fintype.card R : ℂ))
    have he : (((t : ℂ) • σ.toOp) - (ρ.partialTraceRight.stateMap c).toOp) ⊗ₖ (1 : Op R) =
        (((t : ℂ) • σ.toOp) ⊗ₖ (1 : Op R)) -
          (Matrix.partialTraceRight (ρ.stateMap c).toOp ⊗ₖ (1 : Op R)) := by
      ext i j
      exact sub_mul _ _ _
    rwa [he, smul_sub] at hh
  apply opLe_of_posSemidef_sub
  apply Matrix.le_iff.mp
  convert h.trans hm using 1
  dsimp only [SubDensityOp.kronecker, DensityOp.toSubDensityOp, DensityOp.maxMixed]
  rw [kronecker_smul, smul_kronecker, smul_smul, smul_smul]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := R))]

/-- A correlated register costs at most twice its base-two log dimension at the same radius. -/
theorem smoothMinEntropy_le_extension_add [DecidableEq C] [Nonempty Q]
    (ρ : CQState C (Q × R)) (σ : SubDensityOp Q) (ε : ℝ) :
    smoothMinEntropy ε ρ.partialTraceRight σ ≤
      smoothMinEntropy ε ρ (σ.kronecker (DensityOp.maxMixed (X := R)).toSubDensityOp) +
        ENNReal.ofReal (2 * Real.logb 2 (Fintype.card R : ℝ)) := by
  have hc : 0 ≤ 2 * Real.logb 2 (Fintype.card R : ℝ) := mul_nonneg (by norm_num)
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos))
  apply smoothMinEntropy_le_add_of_feasible_transport _ _ _ _ _ _ _ hc
  intro τ hd
  obtain ⟨τ', hm, he⟩ := ρ.exists_extension_of_partialTraceRight_purifiedDistance_eq τ
  refine ⟨τ', he.trans_le hd, ?_⟩
  intro t ht
  have hf : IsFeasible τ'.partialTraceRight σ t := by rwa [hm]
  have hp : (2 : ℝ) ^ (2 * Real.logb 2 (Fintype.card R : ℝ)) = (Fintype.card R : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
        (by exact_mod_cast Fintype.card_pos), Real.rpow_two]
  rw [hp]
  exact hf.extension

end InfoTheory.SmoothMinEntropy
