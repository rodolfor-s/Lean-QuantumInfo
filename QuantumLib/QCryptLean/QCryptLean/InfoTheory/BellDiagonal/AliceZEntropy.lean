import QCryptLean.InfoTheory.BellDiagonal.AliceZ
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBitsBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Schmidt
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.StateOperations

/-! # Alice ZEntropy -/


noncomputable section

namespace InfoTheory.BellDiagonal

open Quantum.Operators InfoTheory.SmoothMinEntropy
  InfoTheory.VonNeumannEntropy Matrix
open scoped Kronecker

/-- Measuring Alice in a pure extension gives the entropy of Alice's dephased signal state.
The reference is a pair of qubit registers. Every block is specified before taking
its partial trace. -/
theorem aliceZ_measuredJoint_entropy_eq_dephase
    (σ : DensityOp (Fin 2 × Fin 2)) (ρ : CQState (Fin 2) (Fin 2 × Fin 2))
    (hρ : ∑ z, (ρ.stateMap z).trace = 1)
    (Ψ : DensityOp ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (hΨ : Ψ.IsPure)
    (hΨσ : partialTraceRight Ψ.toOp = σ.toOp)
    (horigin : ∀ z, (ρ.stateMap z).toOp = partialTraceLeft
      ((aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2))) * Ψ.toOp *
        (aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2))))) :
    vonNeumannEntropy (ρ.toJointDensityOp hρ) = vonNeumannEntropy (aliceZDephase σ) := by
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet Ψ hΨ
  have hp (p q) : Ψ.toOp p q = v.vec p * star (v.vec q) := by rw [← hv]; rfl
  let A : Matrix (Fin 2 × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    fun a p => if a.1 = p.2 then v.vec (a,p.1) else 0
  symm
  apply vonNeumannEntropy_eq_of_gram _ _ A
  · ext a b
    rw [aliceZDephase_apply, ← hΨσ]
    change (if a.1 = b.1 then ∑ e, Ψ.toOp (a,e) (b,e) else 0) =
      ∑ p, A a p * star (A b p)
    simp only [A, Fintype.sum_prod_type,
      apply_ite (Star.star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    by_cases hab : a.1 = b.1
    · simp [hab, hp]
    · simp [hab]
  · ext ⟨e,z⟩ ⟨f,w⟩
    change (if z = w then (ρ.stateMap z).toOp e f else 0) =
      ∑ a, star (A a (f,w)) * A a (e,z)
    rw [horigin]
    simp only [A,
      apply_ite (Star.star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    by_cases hzw : z = w
    · subst w
      simp only [↓reduceIte]
      change (∑ a, ((aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2))) * Ψ.toOp *
        (aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2)))) (a,e) (a,f)) = _
      apply Finset.sum_congr rfl
      intro a _
      rw [aliceZProj_kronecker_one_sandwich_apply]
      simp only [and_self, hp]
      split_ifs <;> ring
    · simp only [hzw, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : a.1 = w <;> by_cases hb : a.1 = z <;> simp_all


/-- The measured reference marginal has the entropy of the original signal state. -/
theorem aliceZ_quantumMarginal_entropy_eq_self
    (σ : DensityOp (Fin 2 × Fin 2)) (ρ : CQState (Fin 2) (Fin 2 × Fin 2))
    (hρ : ∑ z, (ρ.stateMap z).trace = 1)
    (Ψ : DensityOp ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (hΨ : Ψ.IsPure)
    (hΨσ : partialTraceRight Ψ.toOp = σ.toOp)
    (horigin : ∀ z, (ρ.stateMap z).toOp = partialTraceLeft
      ((aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2))) * Ψ.toOp *
        (aliceZProj z ⊗ₖ (1 : Op (Fin 2 × Fin 2))))) :
    vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ) = vonNeumannEntropy σ := by
  have hq : ρ.quantumMarginalDensityOp hρ = Ψ.partialTraceLeft := by
    apply DensityOp.ext
    ext e f
    change (∑ z, (ρ.stateMap z).toOp e f) = ∑ a, Ψ.toOp (a,e) (a,f)
    simp_rw [horigin, Matrix.partialTraceLeft, Matrix.of_apply,
      aliceZProj_kronecker_one_sandwich_apply, and_self]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  have hs : σ = Ψ.partialTraceRight := DensityOp.ext hΨσ.symm
  rw [hq, hs]
  exact (vonNeumannEntropy_partialTraceRight_eq_left Ψ hΨ).symm

end InfoTheory.BellDiagonal
