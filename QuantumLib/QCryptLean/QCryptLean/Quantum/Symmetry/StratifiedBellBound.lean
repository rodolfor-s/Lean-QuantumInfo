import QCryptLean.Math.LinearAlgebra.Matrix.DiagonalFiber
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.BellDickeCore
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellDicke
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.BellSpectrum
import QCryptLean.Quantum.Symmetry.Stratified
import QCryptLean.Quantum.Symmetry.StratifiedBell

/-! # Stratified Bell Bound -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

open private exists_perm_comp_of_map_eq
  from QCryptLean.Quantum.Symmetry.BellDickeCore

open scoped ComplexOrder in
/-- Product-prefactor Bell domination on the actual dependent stratum register. -/
theorem stratified_marginal_dominated {k : ℕ} (n : Fin k → ℕ)
    (A : Op ((j : Fin k) → Fin (n j) → Bool × Bool)) (hA : A.PosSemidef)
    (ht : A.trace.re ≤ 1)
    (hy : ∀ g : ∀ j, Equiv.Perm (Fin (n j)),
      youngRepresentation n g * A = A * youngRepresentation n g)
    (hb : IsStratifiedBellDiagonal n A) :
    ((stratifiedDeFinettiPrefactor n : ℂ) •
      (stratifiedBellDeFinettiDensity n).toOp - A).PosSemidef := by
  classical
  let V := stratifiedBellRotation n
  let M := V * A * Vᴴ
  have hV : Vᴴ * V = 1 := by
    rw [show V = piTensorProduct (fun j => bellRotation (n j)) from rfl,
      conjTranspose_piTensorProduct, piTensorProduct_mul]
    simp only [bellRotation_unitary, piTensorProduct_one]
  have hM : M.PosSemidef := hA.mul_mul_conjTranspose_same V
  have htM : M.trace.re ≤ 1 := by
    dsimp [M]
    rw [trace_mul_cycle, hV, Matrix.one_mul]
    exact ht
  have hentry (g : ∀ j, Equiv.Perm (Fin (n j))) (x y : (j : Fin k) → Fin (n j) → Fin 4) :
      youngRepresentation n g x y =
        if x = (fun j => y j ∘ (g j).symm) then (1 : ℂ) else 0 := by
    simp only [youngRepresentation, piTensorProduct_apply, permutationRepresentation,
      tensorPermutation, Matrix.of_apply, Fintype.prod_boole, ← funext_iff]
  have hc (g : ∀ j, Equiv.Perm (Fin (n j))) :
      youngRepresentation (X := Fin 4) n g * V =
        V * youngRepresentation (X := Bool × Bool) n g := by
    change piTensorProduct _ * piTensorProduct _ = piTensorProduct _ * piTensorProduct _
    rw [piTensorProduct_mul, piTensorProduct_mul]
    apply congrArg piTensorProduct
    funext j
    exact tensorPermutation_mul_piTensorProduct_const (g j) bellSinglePairRotation
  have horbit (i j : (a : Fin k) → Fin (n a) → Fin 4)
      (hij : (fun a => bellTypeOfIndex (i a)) = (fun a => bellTypeOfIndex (j a))) :
      M i i = M j j := by
    have hh (a : Fin k) : ∃ σ : Equiv.Perm (Fin (n a)), j a ∘ σ = i a :=
      exists_perm_comp_of_map_eq (congrArg Subtype.val (congrFun hij a))
    choose g hg using hh
    let B := youngRepresentation (X := Fin 4) n g
    let C := youngRepresentation (X := Bool × Bool) n g
    have hr : Vᴴ * Bᴴ = Cᴴ * Vᴴ := by
      simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose (hc g)
    have hu : C * Cᴴ = 1 := by
      dsimp [C, youngRepresentation]
      rw [conjTranspose_piTensorProduct, piTensorProduct_mul]
      simp only [permutationRepresentation, (tensorPermutation_unitary _).2, piTensorProduct_one]
    have he : B * M * Bᴴ = M := by
      change B * (V * A * Vᴴ) * Bᴴ = M
      calc _ = (B * V) * A * (Vᴴ * Bᴴ) := by simp only [Matrix.mul_assoc]
           _ = (V * C) * A * (Cᴴ * Vᴴ) := by rw [hc g, hr]
           _ = V * (C * A * Cᴴ) * Vᴴ := by simp only [Matrix.mul_assoc]
           _ = M := by
             rw [show C * A = A * C from hy g, Matrix.mul_assoc A C Cᴴ, hu, Matrix.mul_one]
    have he' : (B * M * Bᴴ) j j = M (fun a => j a ∘ g a) (fun a => j a ∘ g a) := by
      have hi (x : (a : Fin k) → Fin (n a) → Fin 4) :
          j = (fun a => x a ∘ (g a).symm) ↔ (fun a => j a ∘ g a) = x := by
        constructor
        · intro h
          funext a
          exact (eq_comp_symm_iff (j a) (x a) (g a)).mp (congrFun h a)
        · intro h
          funext a
          exact (eq_comp_symm_iff (j a) (x a) (g a)).mpr (congrFun h a)
      simp [Matrix.mul_apply, conjTranspose_apply, B, hentry, hi]
    rw [show (fun a => j a ∘ g a) = i from funext hg] at he'
    exact he'.symm.trans (congrFun (congrFun he j) j)
  let f (i : (a : Fin k) → Fin (n a) → Fin 4) := fun a => bellTypeOfIndex (i a)
  have hcard (i : (a : Fin k) → Fin (n a) → Fin 4) :
      (Finset.univ.filter (fun j => f j = f i)).card =
        ∏ a, bellTypeMult (n a) (bellTypeOfIndex (i a)) := by
    have he : Finset.univ.filter (fun j => f j = f i) =
        Fintype.piFinset (fun a => Finset.univ.filter
          (fun j : Fin (n a) → Fin 4 => bellTypeOfIndex j = bellTypeOfIndex (i a))) := by
      ext j
      simp [Fintype.mem_piFinset, f, funext_iff]
    rw [he, Fintype.card_piFinset]
    rfl
  have hdiag : M = diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp only [diagonal_apply, ite_eq_right hij]
      exact hb i j hij
  have hs : V * (stratifiedBellDeFinettiDensity n).toOp * Vᴴ =
      diagonal (fun i => ∏ a, ((n a + 3).choose 3 : ℂ)⁻¹ *
        symmetricProjector (Fin 4) (n a) (i a) (i a)) := by
    change piTensorProduct _ * piTensorProduct _ * (piTensorProduct _)ᴴ = _
    rw [conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
    simp only [bellRotation_conj_bellDeFinettiDensity_eq_diagonal]
    exact piTensorProduct_diagonal _
  have hscalar (i : (a : Fin k) → Fin (n a) → Fin 4) :
      (stratifiedDeFinettiPrefactor n : ℂ) *
        (∏ a, ((n a + 3).choose 3 : ℂ)⁻¹ * symmetricProjector (Fin 4) (n a) (i a) (i a)) =
      ((Finset.univ.filter (fun j => f j = f i)).card : ℂ)⁻¹ := by
    rw [hcard]
    simp only [stratifiedDeFinettiPrefactor, Nat.cast_prod, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, symmetricProjector_apply_eq_typeIndicator, ite_true]
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact Finset.prod_ne_zero_iff.mpr (fun a _ => Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (Nat.choose_pos (by omega))))
  let D := (stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp - A
  have hd : (V * D * Vᴴ).PosSemidef := by
    change (V * ((stratifiedDeFinettiPrefactor n : ℂ) • _ - A) * Vᴴ).PosSemidef
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hs,
      show V * A * Vᴴ = diagonal (fun i => M i i) from hdiag,
      ← diagonal_smul, diagonal_sub]
    apply PosSemidef.diagonal
    intro i
    change 0 ≤ (stratifiedDeFinettiPrefactor n : ℂ) * _ - M i i
    rw [hscalar, sub_nonneg]
    exact hM.diag_le_inv_card_fiber htM f horbit i
  have hh := hd.mul_mul_conjTranspose_same Vᴴ
  rw [conjTranspose_conjTranspose] at hh
  have he : Vᴴ * (V * D * Vᴴ) * V = D := by
    calc _ = (Vᴴ * V) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
         _ = D := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  rwa [he] at hh

end Quantum.Symmetry
