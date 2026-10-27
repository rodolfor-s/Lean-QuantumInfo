import QCryptLean.Math.CodingTheory.CSS.Codes
import QCryptLean.Math.CodingTheory.CSS.ErrorModel
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.CodingTheory.CSS
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis

/-! # CSSMeasurement -/


noncomputable section

namespace Quantum.CodingTheory

open Matrix Quantum.Operators Quantum.Symmetry Math.CodingTheory.CSS

/-- The multi-qubit phase-sensitive Pauli product rule. Native proof. -/
theorem pauliError_mul {n : ℕ} (e₁ e₂ : PauliError n) :
    pauliErrorOp e₁ * pauliErrorOp e₂ =
      Math.CodingTheory.CSS.pauliCommutationSign e₁.zPattern e₂.xPattern •
        pauliErrorOp ⟨e₁.xPattern + e₂.xPattern, e₁.zPattern + e₂.zPattern⟩ := by
  have hsingle (a b c d : ZMod 2) : singleQubitPauli a b * singleQubitPauli c d =
      (if b * c = 1 then (-1 : ℂ) else 1) • singleQubitPauli (a + c) (b + d) := by
    have h01 (x : ZMod 2) : x = 0 ∨ x = 1 := by
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
      rcases h01 c with rfl | rfl <;> rcases h01 d with rfl | rfl <;>
      simp only [add_zero, zero_add, h11, mul_zero, mul_one] <;>
      norm_num [singleQubitPauli] <;>
      ext i j <;> cases i <;> cases j <;>
      norm_num [pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply]
  have hsign {k : ℕ} (a b : Fin k → ZMod 2) :
      pauliCommutationSign a b = ∏ i, if a i * b i = 1 then (-1 : ℂ) else 1 := by
    induction k with
    | zero => simp [pauliCommutationSign, symplecticInnerProduct]
    | succ k ih => rw [pauliCommutationSign_succ, Fin.prod_univ_succ, ih]; rfl
  unfold pauliErrorOp
  rw [Matrix.piTensorProduct_mul]
  simp_rw [hsingle]
  ext x y
  simp only [Matrix.piTensorProduct_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, hsign, Pi.add_apply]

/-- Stabilizer-equivalent errors act with the original relative phase. Native proof. -/
theorem equiv_act_same {n : ℕ} (code : CSSCode n) (e₁ e₂ : PauliError n)
    (he : e₁.EquivOnCode code e₂) (ψ : Ket (Fin n → Bool)) (hψ : InCodeSpace code ψ) :
    pauliErrorOp e₁ * ψ =
      Math.CodingTheory.CSS.pauliCommutationSign e₂.zPattern (e₁.xPattern - e₂.xPattern) •
        (pauliErrorOp e₂ * ψ) := by
  let sx := e₁.xPattern - e₂.xPattern
  let sz := e₁.zPattern - e₂.zPattern
  let c := pauliCommutationSign e₂.zPattern sx
  have hmul (A B : Op (Fin n → Bool)) (v : Ket (Fin n → Bool)) :
      (A * B) * v = A * (B * v) := Ket.ext (Matrix.mulVec_mulVec _ _ _).symm
  have hsmul (a : ℂ) (A : Op (Fin n → Bool)) (v : Ket (Fin n → Bool)) :
      (a • A) * v = a • (A * v) := Ket.ext (Matrix.smul_mulVec _ _ _)
  have hfactor : pauliErrorOp ⟨sx, 0⟩ * pauliErrorOp ⟨0, sz⟩ = pauliErrorOp ⟨sx, sz⟩ := by
    rw [pauliError_mul]
    simp [pauliCommutationSign, symplecticInnerProduct]
  have hfix : pauliErrorOp ⟨sx, sz⟩ * ψ = ψ := by
    rw [← hfactor, hmul]
    have hz : pauliErrorOp ⟨0, sz⟩ * ψ = ψ := hψ.2 sz he.2
    rw [hz]
    exact hψ.1 sx he.1
  have heq : pauliErrorOp e₂ * pauliErrorOp ⟨sx, sz⟩ = c • pauliErrorOp e₁ := by
    rw [pauliError_mul]
    have hx : e₂.xPattern + sx = e₁.xPattern := by dsimp [sx]; abel
    have hz : e₂.zPattern + sz = e₁.zPattern := by dsimp [sz]; abel
    rw [hx, hz]
  have hv : pauliErrorOp e₂ * ψ = c • (pauliErrorOp e₁ * ψ) := by
    rw [← hfix, ← hmul, heq, hsmul, hfix]
  have hc : c * c = 1 := by dsimp [c, pauliCommutationSign]; split <;> norm_num
  change pauliErrorOp e₁ * ψ = c • (pauliErrorOp e₂ * ψ)
  rw [hv, smul_smul, hc, one_smul]

/-- A CSS code corrects every bounded-weight Pauli error, up to a unit-modulus phase.
The syndrome-only correction function chooses a bounded representative. Its action follows
from the Pauli product rule and classical syndrome equivalence. -/
theorem corrects_errors {n : ℕ} (code : CSSCode n) (t : ℕ) (ht : 2 * t + 1 ≤ code.distance) :
    ∃ correction : PauliError n → PauliError n,
      (∀ e₁ e₂, e₁.SameXSyndrome code e₂ → e₁.SameZSyndrome code e₂ →
        correction e₁ = correction e₂) ∧
      (∀ e, e.xWeight ≤ t → e.zWeight ≤ t → ∀ ψ : Ket (Fin n → Bool),
        InCodeSpace code ψ → ∃ phase : ℂ, ‖phase‖ = 1 ∧
          pauliErrorOp (correction e) * (pauliErrorOp e * ψ) = phase • ψ) := by
  classical
  let chooseError (s : code.Syndrome) : PauliError n :=
    if h : ∃ e : PauliError n, e.syndrome code = s ∧ e.xWeight ≤ t ∧ e.zWeight ≤ t
    then h.choose else ⟨0, 0⟩
  refine ⟨fun e => chooseError (e.syndrome code), ?_, ?_⟩
  · intro e₁ e₂ hx hz
    exact congrArg chooseError ((PauliError.syndrome_eq_iff code e₁ e₂).mpr ⟨hx, hz⟩)
  · intro e hx hz ψ hψ
    have hex : ∃ c : PauliError n,
        c.syndrome code = e.syndrome code ∧ c.xWeight ≤ t ∧ c.zWeight ≤ t := ⟨e, rfl, hx, hz⟩
    let c := chooseError (e.syndrome code)
    have hc : c.syndrome code = e.syndrome code ∧ c.xWeight ≤ t ∧ c.zWeight ≤ t := by
      simpa only [c, chooseError, dite_eq_left hex] using hex.choose_spec
    have hs := (PauliError.syndrome_eq_iff code e c).mp hc.1.symm
    have he := code.syndrome_determines_equivalence t ht e c hx hc.2.1 hz hc.2.2 hs.1 hs.2
    have hv := equiv_act_same code e c he ψ hψ
    let a := pauliCommutationSign c.zPattern (e.xPattern - c.xPattern)
    let b := pauliCommutationSign c.zPattern c.xPattern
    have hzero : pauliErrorOp (⟨0, 0⟩ : PauliError n) = 1 := by
      simp [pauliErrorOp, singleQubitPauli, piTensorProduct_one]
    have hcc : pauliErrorOp c * pauliErrorOp c = b • (1 : Op (Fin n → Bool)) := by
      rw [pauliError_mul,
      show c.xPattern + c.xPattern = 0 by ext i; exact CharTwo.add_self_eq_zero _,
      show c.zPattern + c.zPattern = 0 by ext i; exact CharTwo.add_self_eq_zero _, hzero]
    refine ⟨a * b, ?_, ?_⟩
    · dsimp [a, b, pauliCommutationSign]
      split <;> split <;> norm_num
    · change pauliErrorOp c * (pauliErrorOp e * ψ) = (a * b) • ψ
      rw [hv]
      apply Ket.ext
      change pauliErrorOp c *ᵥ (a • (pauliErrorOp c *ᵥ ψ.vec)) = (a * b) • ψ.vec
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hcc, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul]

end Quantum.CodingTheory
