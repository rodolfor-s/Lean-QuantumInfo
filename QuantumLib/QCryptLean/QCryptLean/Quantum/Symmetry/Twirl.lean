import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Symmetry.Basic

/-!
# Uniform unitary twirls and permutation symmetrization

The channel is constructed natively from its finite Kraus family. Register,
unitary-label, and site types remain separate. Positivity is `Matrix.PosSemidef`;
no matrix norm or order instance is installed.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Channels

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Nonempty I]

/-- The Kraus family of a uniform finite unitary average. -/
def twirlKraus (U : I → UnitaryOp X) : I → Op X :=
  fun i => (Real.sqrt ((Fintype.card I : ℝ)⁻¹) : ℂ) • (U i).val

omit [Nonempty I] in
private theorem twirlWeight_sq :
    (Real.sqrt ((Fintype.card I : ℝ)⁻¹) : ℂ) *
      star (Real.sqrt ((Fintype.card I : ℝ)⁻¹) : ℂ) = (Fintype.card I : ℂ)⁻¹ := by
  rw [Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp

/-- Uniform unitary averaging is a complete Kraus operation. -/
def twirlRepresentation (U : I → UnitaryOp X) : KrausRepresentation X X I where
  operators := twirlKraus U
  completeness := by
    simp only [twirlKraus, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      twirlWeight_sq]
    change ∑ i, (Fintype.card I : ℂ)⁻¹ • (star (U i).val * (U i).val) = _
    have hunit : ∀ i, star (U i).val * (U i).val = (1 : Op X) :=
      fun i => Matrix.mem_unitaryGroup_iff'.mp (U i).property
    have hc : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [hunit, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
    ext i j
    simp [Matrix.one_apply]

/-- The linear channel that averages a finite family of unitary conjugations. -/
def twirl (U : I → UnitaryOp X) : Operation X X := (twirlRepresentation U).toOperation

/-- Uniform twirling has the expected normalized sum formula. -/
theorem twirl_apply (U : I → UnitaryOp X) (A : Op X) :
    twirl U A = (Fintype.card I : ℂ)⁻¹ • ∑ i, (U i).val * A * (U i).valᴴ := by
  change (∑ i, twirlKraus U i * A * (twirlKraus U i)ᴴ) = _
  simp only [twirlKraus, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Finset.smul_sum]
  congr 1
  simpa only [mul_comm] using (twirlWeight_sq (I := I))

/-- Every finite unitary twirl is a channel. -/
theorem isChannel_twirl (U : I → UnitaryOp X) : IsChannel (twirl U) :=
  (twirlRepresentation U).isChannel

omit [Fintype I] [Nonempty I] in
/-- The site-permutation matrix bundled in Mathlib's unitary group. -/
def permutationUnitary {k : ℕ} (σ : Equiv.Perm (Fin k)) : UnitaryOp (Fin k → X) :=
  ⟨permutationRepresentation σ, (Matrix.mem_unitaryGroup_iff').mpr
    (tensorPermutation_unitary σ).1⟩

omit [Fintype I] [Nonempty I] in
/-- The permutation-averaging channel on a tensor register. -/
def symmetrizeChannel (X : Type*) [Fintype X] [DecidableEq X] (k : ℕ) :
    Operation (Fin k → X) (Fin k → X) := twirl permutationUnitary

omit [Fintype I] [Nonempty I] in
/-- Symmetrization of a density state by the permutation channel. -/
def symmetrize {k : ℕ} (ρ : DensityOp (Fin k → X)) : DensityOp (Fin k → X) :=
  (isChannel_twirl permutationUnitary).applyDensity ρ

omit [Fintype I] [Nonempty I] in
/-- The state symmetrization is the average of the permutation conjugates. -/
theorem symmetrize_toOp {k : ℕ} (ρ : DensityOp (Fin k → X)) :
    (symmetrize ρ).toOp = (1 / (Nat.factorial k : ℂ)) •
      ∑ σ : Equiv.Perm (Fin k),
        permutationRepresentation σ * ρ.toOp * (permutationRepresentation σ)ᴴ := by
  change twirl permutationUnitary ρ.toOp = _
  rw [twirl_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, permutationUnitary, one_div]

omit [Fintype I] [Nonempty I] in
/-- Permutation averaging produces a permutation-invariant state. -/
theorem isPermutationInvariant_symmetrize {k : ℕ} (ρ : DensityOp (Fin k → X)) :
    IsPermutationInvariant (symmetrize ρ) := by
  intro σ
  simp only [symmetrize_toOp]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  apply congrArg ((1 / (Nat.factorial k : ℂ)) • ·)
  simp only [permutationRepresentation]
  simp_rw [← Matrix.mul_assoc, tensorPermutation_mul, Matrix.mul_assoc,
    ← conjTranspose_mul, tensorPermutation_mul, ← Matrix.mul_assoc]
  exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)

omit [Fintype I] [Nonempty I] in
/-- Averaging leaves an already invariant state unchanged. -/
theorem symmetrize_eq_self {k : ℕ} (ρ : DensityOp (Fin k → X))
    (hρ : IsPermutationInvariant ρ) : symmetrize ρ = ρ := by
  change ∀ σ, _ = ρ.toOp at hρ
  apply DensityOp.ext
  rw [symmetrize_toOp]
  simp only [hρ, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_smul]

end Quantum.Symmetry
