import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import QCryptLean.InfoTheory.BellDiagonal.AliceZ
import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.TraceFormula
import QCryptLean.Quantum.Operators.Basic

/-! # Alice dephasing and relative entropy -/

noncomputable section
namespace InfoTheory.BellDiagonal
open Quantum.Operators Matrix InfoTheory.RelativeEntropy
  InfoTheory.VonNeumannEntropy
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Alice's dephasing cannot shrink the support of a state. -/
lemma ker_aliceZDephase_sub (ρ : DensityOp (Fin 2 × Fin 2))
    (v : (Fin 2 × Fin 2) → ℂ) (hv : (aliceZDephase ρ).toOp *ᵥ v = 0) :
    ρ.toOp *ᵥ v = 0 := by
  let Z : Op (Fin 2 × Fin 2) := diagonal fun p => if p.1 = 0 then 1 else -1
  have he : (2 : ℂ) • (aliceZDephase ρ).toOp - ρ.toOp = Z * ρ.toOp * Zᴴ := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, aliceZDephase_apply,
      Z, diagonal_conjTranspose, diagonal_mul, mul_diagonal, Pi.star_apply]
    fin_cases a <;> fin_cases c <;> norm_num <;> ring
  have hn := (ρ.posSemidef.mul_mul_conjTranspose_same Z).dotProduct_mulVec_nonneg v
  rw [← he, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero,
    zero_sub, dotProduct_neg] at hn
  exact ρ.posSemidef.dotProduct_mulVec_zero_iff.mp
    (le_antisymm (neg_nonneg.mp hn) (ρ.posSemidef.dotProduct_mulVec_nonneg v))

/-- The relative entropy to Alice's dephasing equals the entropy produced by it. -/
lemma relativeEntropyReal_aliceZDephase (ρ : DensityOp (Fin 2 × Fin 2)) :
    relativeEntropyReal ρ (aliceZDephase ρ) =
      vonNeumannEntropy (aliceZDephase ρ) - vonNeumannEntropy ρ := by
  let S := (aliceZDephase ρ).toOp
  let L := CFC.log S
  have hc (z : Fin 2) : Commute S (aliceZProj z) := by
    change S * aliceZProj z = aliceZProj z * S
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [S, aliceZProj, mul_diagonal, diagonal_mul, aliceZDephase_apply]
    by_cases h : a = c
    · simp [h, mul_comm]
    · simp [h]
  have hl (z : Fin 2) : L * aliceZProj z = aliceZProj z * L :=
    ((hc z).cfc_real Real.log).eq
  have hP (z : Fin 2) : (aliceZProj z)ᴴ = aliceZProj z := by
    unfold aliceZProj
    rw [diagonal_conjTranspose]
    congr 1
    funext p
    by_cases h : p.1 = z <;> simp [h]
  have hid (z : Fin 2) : aliceZProj z * aliceZProj z = aliceZProj z := by
    unfold aliceZProj
    rw [diagonal_mul_diagonal]
    congr 1
    funext p
    by_cases h : p.1 = z <;> simp [h]
  have hs : ∑ z : Fin 2, aliceZProj z = 1 := by
    ext p q
    simp [aliceZProj, Matrix.sum_apply, diagonal_apply, one_apply]
  have ht : (S * L).trace = (ρ.toOp * L).trace := by
    change ((∑ z : Fin 2, aliceZProj z * ρ.toOp * (aliceZProj z)ᴴ) * L).trace = _
    simp only [hP, Matrix.sum_mul, Matrix.trace_sum]
    have he (z : Fin 2) : (aliceZProj z * ρ.toOp * aliceZProj z * L).trace =
        (ρ.toOp * (L * aliceZProj z)).trace := by
      rw [Matrix.mul_assoc (aliceZProj z), Matrix.mul_assoc (aliceZProj z), trace_mul_comm]
      congr 1
      calc
        _ = ρ.toOp * (aliceZProj z * L) * aliceZProj z := by simp [Matrix.mul_assoc]
        _ = ρ.toOp * (L * aliceZProj z) * aliceZProj z := by rw [← hl]
        _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc L, hid]
    simp_rw [he]
    rw [← trace_sum, ← Matrix.mul_sum, ← Matrix.mul_sum, hs, Matrix.mul_one]
  rw [relativeEntropyReal, vonNeumannEntropy_eq_neg_trace_mul_log (aliceZDephase ρ)]
  change -vonNeumannEntropy ρ - (ρ.toOp * L).trace.re =
    -(S * L).trace.re - vonNeumannEntropy ρ
  rw [ht]
  ring
end InfoTheory.BellDiagonal
