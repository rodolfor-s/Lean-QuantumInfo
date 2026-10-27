import Batteries.Tactic.OpenPrivate
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.BellTwirlIdempotent
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Bell Basis -/


noncomputable section

namespace Quantum.Symmetry

open private bellPh_unit kleinAdd_klein
  from QCryptLean.Quantum.Symmetry.BellTwirlIdempotent

open Matrix Quantum.Operators

/-- The explicit Boolean qubit enumeration, with `false` before `true`. -/
def qubitEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

/-- Multiplying Pauli matrices produces the existing scalar Pauli cocycle. -/
private theorem pauli_mul_projective (a b : Fin 4) : pauli a * pauli b =
    Quantum.Symmetry.bellPauliCocycle a b • pauli (Quantum.Symmetry.kleinFourAdd a b) := by
  fin_cases a <;> fin_cases b <;> ext i j <;> cases i <;> cases j <;>
    norm_num [pauli, pauliX, pauliY, pauliZ,
      Quantum.Symmetry.kleinFourAdd, Quantum.Symmetry.bellPauliCocycle,
      Matrix.mul_apply, Fintype.sum_bool, diagonal_apply, Matrix.one_apply]

/-- Bell twirling is idempotent. -/
theorem bellTwirl_idempotent {k : ℕ} (A : Op (Fin k → Bool × Bool)) :
    bellTwirl k (bellTwirl k A) = bellTwirl k A := by
  classical
  let add := Quantum.Symmetry.kleinFourAdd
  let s := Quantum.Symmetry.bellSignCocycle
  have hp := pauli_mul_projective
  have hs (a b : Fin 4) : s a b * star (s a b) = 1 := bellPh_unit a b
  have ha (a b : Fin 4) : add a (add a b) = b := kleinAdd_klein a b
  have hb (a b : Fin 4) : bilateralPauli a * bilateralPauli b =
      s a b • bilateralPauli (add a b) := by
    rw [bilateralPauli, bilateralPauli, ← mul_kronecker_mul, hp, smul_kronecker,
      kronecker_smul, smul_smul]
    rfl
  let f (g h : Fin k → Fin 4) := fun i => add (g i) (h i)
  let z (g h : Fin k → Fin 4) : ℂ := ∏ i, s (g i) (h i)
  have hm (g h : Fin k → Fin 4) : (bellTwirlUnitary g).val * (bellTwirlUnitary h).val =
      z g h • (bellTwirlUnitary (f g h)).val := by
    change piTensorProduct _ * piTensorProduct _ = _
    rw [piTensorProduct_mul]
    simp only [hb]
    ext i j
    simp [bellTwirlUnitary, piTensorProduct_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.prod_mul_distrib, z, f]
  have hz (g h : Fin k → Fin 4) : z g h * star (z g h) = 1 := by
    simp only [z, star_prod, ← Finset.prod_mul_distrib, hs, Finset.prod_const_one]
  have hinv (g : Fin k → Fin 4) :
      (bellTwirlUnitary g).val * bellTwirl k A * (bellTwirlUnitary g).valᴴ = bellTwirl k A := by
    simp only [bellTwirl, twirl_apply, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul]
    apply congrArg ((Fintype.card (Fin k → Fin 4) : ℂ)⁻¹ • ·)
    have he (h : Fin k → Fin 4) :
        (bellTwirlUnitary g).val * ((bellTwirlUnitary h).val * A * (bellTwirlUnitary h).valᴴ) *
          (bellTwirlUnitary g).valᴴ =
        (bellTwirlUnitary (f g h)).val * A * (bellTwirlUnitary (f g h)).valᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hm, Matrix.mul_assoc,
        ← conjTranspose_mul, hm, conjTranspose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm (star (z g h)), hz, one_smul]
    simp_rw [he]
    exact Fintype.sum_bijective (f g) (Function.Involutive.bijective
      (fun h => funext fun i => ha (g i) (h i))) _ _ (fun _ => rfl)
  change twirl bellTwirlUnitary (bellTwirl k A) = bellTwirl k A
  rw [twirl_apply]
  simp only [hinv, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (show (Fintype.card (Fin k → Fin 4) : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

end Quantum.Symmetry
