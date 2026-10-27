import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.Petz
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.MaxEntangled

/-! # Petz Algebra -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]
variable {d r : ℕ}

/-- The Petz map on maximal entanglement retains only the input trace. -/
theorem petzTranspose_maxEntangledOp_apply [Nonempty X] (A : Op X) :
    petzTranspose (maxEntangledOp X) 1 A =
      (A.trace / (Fintype.card X : ℂ)) • maxEntangledOp X := by
  have hc : (((Real.sqrt (Fintype.card X))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card X))⁻¹ : ℝ) : ℂ) = (Fintype.card X : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card X))]
    simp
  change CFC.sqrt (maxEntangledOp X) *
    ((CFC.sqrt (1 : Op X)⁻¹ * A * CFC.sqrt (1 : Op X)⁻¹) ⊗ₖ 1) *
      CFC.sqrt (maxEntangledOp X) = _
  rw [inv_one, CFC.sqrt_one, Matrix.one_mul, Matrix.mul_one, sqrt_maxEntangledOp,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hc,
    maxEntangledOp_sandwich, smul_smul]
  congr 1
  ring

/-- Even this genuine Petz channel fails to realize arbitrary requested marginals. -/
theorem exists_partialTraceRight_petzTranspose_ne :
    ∃ A : Op Bool, A.PosSemidef ∧
      partialTraceRight (petzTranspose (maxEntangledOp Bool) 1 A) ≠ A := by
  refine ⟨diagonal (fun i : Bool => if i then 0 else 1), ?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    cases i <;> norm_num
  · intro h
    rw [petzTranspose_maxEntangledOp_apply, partialTraceRight_smul,
      partialTraceRight_maxEntangledOp] at h
    have he := congrFun (congrFun h true) true
    norm_num [trace_diagonal, Fintype.sum_bool] at he

/-- Marginal transport is not additive even on positive qubit inputs and a positive reference. -/
theorem exists_marginalTransport_add_ne :
    ∃ A B : Op Bool, A.PosSemidef ∧ B.PosSemidef ∧
      marginalTransport (maxEntangledOp Bool) 1 1 (A + B) ≠
        marginalTransport (maxEntangledOp Bool) 1 1 A +
          marginalTransport (maxEntangledOp Bool) 1 1 B := by
  let A : Bool → Op Bool := fun b => diagonal (fun i => if i = b then 1 else 0)
  have hpos (b : Bool) : (A b).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ if i = b then (1 : ℂ) else 0
    split <;> norm_num
  have hsqrt (b : Bool) : CFC.sqrt (A b) = A b := by
    apply CFC.sqrt_unique
    · rw [show A b = diagonal (fun i => if i = b then (1 : ℂ) else 0) from rfl,
        diagonal_mul_diagonal]
      congr 1
      funext i
      split <;> simp
    · exact (hpos b).nonneg
  have hab : A false + A true = 1 := by
    ext i j
    cases i <;> cases j <;> norm_num [A, diagonal_apply, Matrix.one_apply]
  refine ⟨A false, A true, hpos false, hpos true, ?_⟩
  intro h
  rw [hab] at h
  have he := congrFun (congrFun h (false, false)) (true, true)
  simp only [marginalTransport, inv_one, CFC.sqrt_one, hsqrt, mul_one, one_mul] at he
  norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, A,
    diagonal_apply, Matrix.one_apply, conjTranspose_apply, kroneckerMap_apply,
    maxEntangledOp_apply] at he

/-- Recovery of the reference follows by inverse-square-root normalization. -/
theorem petzTranspose_reference {ρ : Op (X × R)} (hρ : ρ.PosSemidef)
    {σ : Op X} (hσ : σ.PosDef) : petzTranspose ρ σ σ = ρ := by
  change CFC.sqrt ρ * ((CFC.sqrt σ⁻¹ * σ * CFC.sqrt σ⁻¹) ⊗ₖ 1) * CFC.sqrt ρ = ρ
  rw [hσ.sqrt_inv_mul_self_mul_sqrt_inv, one_kronecker_one, mul_one,
    CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- The Petz map is a channel when the reference has the supplied marginal. -/
theorem isChannel_petzTranspose {ρ : Op (X × R)} (hρ : ρ.PosSemidef)
    {σ : Op X} (hσ : σ.PosDef) (hm : partialTraceRight ρ = σ) :
    IsChannel (petzTranspose ρ σ) := by
  classical
  let T : R → Matrix (X × R) X ℂ := fun r p i => if p.2 = r then (1 : Op X) p.1 i else 0
  let S := CFC.sqrt ρ
  let V := CFC.sqrt σ⁻¹
  let K : R → Matrix (X × R) X ℂ := fun r => S * T r * V
  have hS : Sᴴ = S := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq
  have hV : Vᴴ = V := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ⁻¹)).isHermitian.eq
  have hT (B : Op X) : (∑ r, T r * B * (T r)ᴴ) = B ⊗ₖ (1 : Op R) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
    simp [T, Matrix.one_apply, kroneckerMap_apply, ite_mul, eq_comm, apply_ite]
    split_ifs <;> simp_all
  have he : petzTranspose ρ σ = krausMap K := by
    ext A p q
    have he' : (∑ r, K r * A * (K r)ᴴ) = S * ((V * A * V) ⊗ₖ 1) * S := by
      rw [← hT, Matrix.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      simp only [K, conjTranspose_mul, hS, hV, Matrix.mul_assoc]
    exact congrFun (congrFun he'.symm p) q
  rw [he]
  refine ⟨isCompletelyPositive_krausMap K, (isTracePreserving_krausMap_iff K).mpr ?_⟩
  have hm' : (∑ r, (T r)ᴴ * ρ * T r) = σ := by
    rw [← hm]
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
    simp [T, Matrix.one_apply, partialTraceRight_apply, ite_mul, apply_ite]
  have hk : (∑ r, (K r)ᴴ * K r) = (1 : Op X) := by
    calc
      (∑ r, (K r)ᴴ * K r) = V * (∑ r, (T r)ᴴ * ρ * T r) * V := by
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        simp only [K, conjTranspose_mul, hS, hV]
        calc
          _ = V * (T r)ᴴ * (S * S) * T r * V := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hm']
        exact hσ.sqrt_inv_mul_self_mul_sqrt_inv
  convert hk using 1
  ext i j
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

/-- Nonlinear marginal transport realizes every positive requested marginal
by the partial-trace sandwich identity. -/
theorem marginalTransport_partialTraceRight (ρ : Op (X × R))
    {σ : Op X} (hσ : σ.PosDef) (hm : partialTraceRight ρ = σ)
    (W : UnitaryOp X) {A : Op X} (hA : A.PosSemidef) :
    partialTraceRight (marginalTransport ρ σ W A) = A := by
  dsimp only [marginalTransport]
  rw [conjTranspose_kronecker, conjTranspose_one, partialTraceRight_kronecker_one_sandwich,
    hm, conjTranspose_mul, conjTranspose_mul]
  have hS := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ⁻¹)).isHermitian.eq
  have hA' := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  rw [hS, hA']
  calc
    _ = CFC.sqrt A * W.val * (CFC.sqrt σ⁻¹ * σ * CFC.sqrt σ⁻¹) * W.valᴴ * CFC.sqrt A := by
      simp only [Matrix.mul_assoc]
    _ = A := by
      rw [hσ.sqrt_inv_mul_self_mul_sqrt_inv, mul_one,
      Matrix.mul_assoc (CFC.sqrt A) W.val W.valᴴ,
      show W.val * W.valᴴ = 1 from W.property.2, mul_one,
      CFC.sqrt_mul_sqrt_self A hA.nonneg]

end Quantum.Channels
