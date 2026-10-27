import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.Twirl

/-!
# Bell dephasing on function registers

The scalar character table and its orthogonality yield matrix identities on
Boolean-pair and Bell-label registers.
-/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators Quantum.Channels
open scoped ComplexOrder Kronecker
open private bellCharE bellCharOrtho
  from QCryptLean.Quantum.Symmetry.BellDeFinettiDomination

private theorem bellSinglePairRotation_mul_bilateralPauli (a : Fin 4) :
    bellSinglePairRotation * bilateralPauli a = diagonal (bellCharE a) *
      bellSinglePairRotation := by
  ext i ⟨b, c⟩
  fin_cases a <;> fin_cases i <;> cases b <;> cases c <;>
    norm_num [bellSinglePairRotation, bellLabelKet, bellKet, bilateralPauli, pauli,
      pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Fin.sum_univ_four, kroneckerMap_apply, diagonal_apply, bellCharE,
      Matrix.one_apply, Complex.star_def, mul_add, add_mul]

private theorem bellRotation_conj_twirlUnitary {k : ℕ} (g : Fin k → Fin 4) :
    bellRotation k * (bellTwirlUnitary g).val * (bellRotation k)ᴴ =
      diagonal (fun i => ∏ a, bellCharE (g a) (i a)) := by
  have hs (a : Fin 4) : bellSinglePairRotation * bilateralPauli a *
      bellSinglePairRotationᴴ = diagonal (bellCharE a) := by
    rw [bellSinglePairRotation_mul_bilateralPauli, Matrix.mul_assoc,
      bellSinglePairRotation_mul_conjTranspose, Matrix.mul_one]
  change piTensorProduct (fun _ : Fin k => bellSinglePairRotation) *
    piTensorProduct (fun i => bilateralPauli (g i)) *
      (piTensorProduct (fun _ : Fin k => bellSinglePairRotation))ᴴ = _
  rw [conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
  simp_rw [hs]
  exact piTensorProduct_diagonal _

private theorem bellWord_character_orthogonality {k : ℕ} (i j : Fin k → Fin 4) :
    ((4 : ℂ) ^ k)⁻¹ * ∑ g : Fin k → Fin 4,
      (∏ a, bellCharE (g a) (i a)) * star (∏ a, bellCharE (g a) (j a)) =
        if i = j then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun (a : Fin k) (g : Fin 4) =>
    bellCharE g (i a) * star (bellCharE g (j a)))]
  rw [show ((4 : ℂ) ^ k)⁻¹ = ∏ _ : Fin k, (4 : ℂ)⁻¹ by simp]
  rw [← Finset.prod_mul_distrib]
  simp_rw [bellCharOrtho]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, forall_const, ← funext_iff]

/-- Bell twirling removes exactly the off-diagonal entries in the product Bell basis. -/
theorem bellRotation_bellTwirl_eq_diagonal (k : ℕ) (A : Op (Fin k → Bool × Bool)) :
    bellRotation k * bellTwirl k A * (bellRotation k)ᴴ =
      diagonal (fun i => (bellRotation k * A * (bellRotation k)ᴴ) i i) := by
  let W := bellRotation k
  let M := W * A * Wᴴ
  let phase (g i : Fin k → Fin 4) := ∏ a, bellCharE (g a) (i a)
  have hexpand : W * bellTwirl k A * Wᴴ =
      ((4 : ℂ) ^ k)⁻¹ • ∑ g : Fin k → Fin 4,
        diagonal (phase g) * M * (diagonal (phase g))ᴴ := by
    rw [bellTwirl, twirl_apply]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    apply congrArg (fun N : Op (Fin k → Fin 4) => ((4 : ℂ) ^ k)⁻¹ • N)
    apply Finset.sum_congr rfl
    intro g _
    have hWW : Wᴴ * W = 1 := bellRotation_unitary k
    have hd : W * (bellTwirlUnitary g).val * Wᴴ = diagonal (phase g) :=
      bellRotation_conj_twirlUnitary g
    have hdh : W * (bellTwirlUnitary g).valᴴ * Wᴴ = (diagonal (phase g))ᴴ := by
      rw [← hd]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    calc
      _ = (W * (bellTwirlUnitary g).val * Wᴴ) * M *
          (W * (bellTwirlUnitary g).valᴴ * Wᴴ) := by
        dsimp only [M]
        symm
        calc
          _ = W * (bellTwirlUnitary g).val * (Wᴴ * W) * A * (Wᴴ * W) *
              (bellTwirlUnitary g).valᴴ * Wᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by simp only [hWW, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hd, hdh]
  change W * bellTwirl k A * Wᴴ = diagonal (fun i => M i i)
  rw [hexpand]
  ext i j
  have he (g : Fin k → Fin 4) :
      (diagonal (phase g) * M * (diagonal (phase g))ᴴ) i j =
        (phase g i * star (phase g j)) * M i j := by
    rw [diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Pi.star_apply]
    ring
  simp only [Matrix.smul_apply, Matrix.sum_apply, he, diagonal_apply, smul_eq_mul]
  rw [← Finset.sum_mul, ← mul_assoc]
  change (((4 : ℂ) ^ k)⁻¹ * ∑ g : Fin k → Fin 4, (∏ a, bellCharE (g a) (i a)) *
    star (∏ a, bellCharE (g a) (j a))) * M i j = _
  rw [bellWord_character_orthogonality]
  by_cases h : i = j <;> simp [h]

end Quantum.Symmetry
