import QCryptLean.Math.LinearAlgebra.Matrix.Columns
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.QKD.KeyedOutputRegister.FlagBlocks
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacement
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Key replacement on matrix units and public extensions

These identities hold on the entire padded operator space, including abort key
coherences. A public extension is a structural reassociation of product types.
-/

open Quantum.Operators Quantum.Channels Matrix
open scoped Kronecker

noncomputable section

namespace QKD

variable (ℓ : ℕ) (D : Type*) [Fintype D] [DecidableEq D]

/-- A fresh-key branch reads the old key pair and prepares its own common key. -/
theorem freshKeyKraus_mul_single {X : Type*} [DecidableEq X]
    (k a b : Fin ℓ → Fin 2) (p : KeyedOutput ℓ D) (w : X) :
    freshKeyKraus ℓ D k a b * Matrix.single p w (1 : ℂ) =
      Matrix.single ((k, k), (true, p.2.2)) w
        (if a = p.1.1 ∧ b = p.1.2 ∧ p.2.1 = true then
          ((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℂ) else 0) := by
  apply Matrix.mul_single_eq_single_of_apply_eq_ite
  intro i
  simp only [freshKeyKraus, acceptFlagOp, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all [Prod.ext_iff, Complex.ofReal_inv]

/-- Key replacement on a matrix unit keeps abort coherences and uniformly replaces equal keys. -/
theorem keyReplace_single (p q : KeyedOutput ℓ D) (c : ℂ) :
    keyReplace ℓ D (Matrix.single p q c) =
      (if p.2.1 = true ∧ q.2.1 = true ∧ p.1 = q.1 then
        ((2 : ℂ) ^ ℓ)⁻¹ • ∑ k : Fin ℓ → Fin 2,
          Matrix.single ((k, k), (true, p.2.2)) ((k, k), (true, q.2.2)) c
      else 0) +
      (if p.2.1 = false ∧ q.2.1 = false then Matrix.single p q c else 0) := by
  have h (k a b : Fin ℓ → Fin 2) :
      Matrix.conjLinearMap (freshKeyKraus ℓ D k a b) (Matrix.single p q c) =
      if a = p.1.1 ∧ b = p.1.2 ∧ p.2.1 = true ∧
          a = q.1.1 ∧ b = q.1.2 ∧ q.2.1 = true then
        ((2 : ℂ) ^ ℓ)⁻¹ •
          Matrix.single ((k, k), (true, p.2.2)) ((k, k), (true, q.2.2)) c
      else 0 := by
    have hp := freshKeyKraus_mul_single ℓ D k a b p q
    rw [Matrix.conjLinearMap_apply]
    have hs : Matrix.single p q c = c • Matrix.single p q (1 : ℂ) := by simp
    rw [hs, Matrix.mul_smul, Matrix.smul_mul, hp]
    have hr : Matrix.single ((k, k), (true, p.2.2)) q (1 : ℂ) *
        (freshKeyKraus ℓ D k a b)ᴴ =
      Matrix.single ((k, k), (true, p.2.2)) ((k, k), (true, q.2.2))
        (if a = q.1.1 ∧ b = q.1.2 ∧ q.2.1 = true then
          ((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℂ) else 0) := by
      have hh := congrArg Matrix.conjTranspose
        (freshKeyKraus_mul_single ℓ D k a b q ((k, k), (true, p.2.2)))
      simpa [apply_ite] using hh
    have hs' (z : ℂ) : Matrix.single ((k, k), (true, p.2.2)) q z =
        z • Matrix.single ((k, k), (true, p.2.2)) q (1 : ℂ) := by simp
    rw [hs', Matrix.smul_mul, hr]
    have hc : (↑(Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℂ) *
        (↑(Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℂ) = ((2 : ℂ) ^ ℓ)⁻¹ := by
      calc
        _ = (↑((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ *
            (Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹) : ℂ) := by push_cast; rfl
        _ = _ := by
          rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
          push_cast
          rfl
    clear hp hs hs' hr
    push_cast at hc
    split_ifs <;> simp_all [Matrix.smul_single, mul_comm]
    all_goals aesop
  rw [keyReplace, LinearMap.add_apply, keyReplaceAccept, LinearMap.sum_apply]
  simp_rw [Fintype.sum_prod_type, h]
  have ha : abortSandwich ℓ D (Matrix.single p q c) =
      if p.2.1 = false ∧ q.2.1 = false then Matrix.single p q c else 0 := by
    rw [abortSandwich, Matrix.conjLinearMap_apply, abortProjOp_conjTranspose,
      abortProjOp_eq_diagonal]
    ext i j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Matrix.single_apply]
    split_ifs <;> simp_all [Matrix.single_apply, Prod.ext_iff]
  rw [ha]
  congr 1
  simp only [ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  by_cases hp : p.2.1 = true <;> by_cases hq : q.2.1 = true <;>
    by_cases hk : p.1 = q.1 <;> simp_all [Prod.ext_iff, Finset.smul_sum]

variable (E : Type*) [Fintype E] [DecidableEq E]

omit [Fintype D] [Fintype E] in
/-- Public reassociation leaves every key-replacement Kraus operator unchanged. -/
theorem reindex_keyReplaceKraus (o : Option ((Fin ℓ → Fin 2) ×
    (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2))) :
    Matrix.reindex (KeyedOutput.prodEquiv ℓ D E) (KeyedOutput.prodEquiv ℓ D E)
      (keyReplaceKraus ℓ D o ⊗ₖ (1 : Op E)) = keyReplaceKraus ℓ (D × E) o := by
  cases o <;> ext p q <;>
    by_cases hd : p.2.2.1 = q.2.2.1 <;> by_cases he : p.2.2.2 = q.2.2.2 <;>
    simp [keyReplaceKraus, freshKeyKraus, abortProjOp, abortFlagOp, acceptFlagOp,
      KeyedOutput.prodEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.ext_iff, ite_and, mul_assoc, hd, he]

/-- Key replacement commutes with retaining an arbitrary public register, on all operators. -/
theorem keyReplace_reindex_prod (A : Op (KeyedOutput ℓ D × E)) :
    keyReplace ℓ (D × E)
      (Matrix.reindex (KeyedOutput.prodEquiv ℓ D E) (KeyedOutput.prodEquiv ℓ D E) A) =
    Matrix.reindex (KeyedOutput.prodEquiv ℓ D E) (KeyedOutput.prodEquiv ℓ D E)
      (mapTensorId (keyReplace ℓ D) E A) := by
  rw [keyReplace_eq_krausMap, keyReplace_eq_krausMap, mapTensorId_krausMap]
  let e := KeyedOutput.prodEquiv ℓ D E
  have h := congrArg (fun Φ => Φ (Matrix.reindex e e A))
    (krausMap_reindex e e (fun o => keyReplaceKraus ℓ D o ⊗ₖ (1 : Op E)))
  simp only [e, reindex_keyReplaceKraus] at h
  change krausMap (keyReplaceKraus ℓ (D × E)) (Matrix.reindex e e A) =
    Matrix.reindex e e (krausMap (fun o => keyReplaceKraus ℓ D o ⊗ₖ (1 : Op E))
      ((Matrix.reindex e e A).submatrix e e)) at h
  have hA : (Matrix.reindex e e A).submatrix e e = A := by
    ext p q
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hA] at h
  have hi : (1 : Op E) = (letI : DecidableEq E := Classical.decEq E; (1 : Op E)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hi] at h
  exact h

/-- Appending a public operator commutes with replacing the two keys. -/
theorem keyReplace_reindex_kronecker (A : Op (KeyedOutput ℓ D)) (B : Op E) :
    keyReplace ℓ (D × E)
      (Matrix.reindex (KeyedOutput.prodEquiv ℓ D E) (KeyedOutput.prodEquiv ℓ D E) (A ⊗ₖ B)) =
    Matrix.reindex (KeyedOutput.prodEquiv ℓ D E) (KeyedOutput.prodEquiv ℓ D E)
      (keyReplace ℓ D A ⊗ₖ B) := by
  rw [keyReplace_reindex_prod, mapTensorId_kronecker]

end QKD
