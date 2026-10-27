import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Operators.Basic

/-! # Flag Blocks -/


open Quantum.Operators Matrix
open scoped Kronecker

noncomputable section

namespace QKD

variable (ℓ : ℕ) (D : Type*) [DecidableEq D]

/-- The acceptance projector on the flag and retained register. -/
def acceptFlagOp : Op (Bool × D) :=
  Matrix.single true true (1 : ℂ) ⊗ₖ (1 : Op D)

/-- The abort projector on the flag and retained register. -/
def abortFlagOp : Op (Bool × D) :=
  Matrix.single false false (1 : ℂ) ⊗ₖ (1 : Op D)

/-- The acceptance projector on both keys, the flag, and the retained register. -/
def acceptProjOp : Op (KeyedOutput ℓ D) :=
  (1 : Op ((Fin ℓ → Fin 2) × (Fin ℓ → Fin 2))) ⊗ₖ acceptFlagOp D

/-- The abort projector on both keys, the flag, and the retained register. -/
def abortProjOp : Op (KeyedOutput ℓ D) :=
  (1 : Op ((Fin ℓ → Fin 2) × (Fin ℓ → Fin 2))) ⊗ₖ abortFlagOp D

/-- Selecting a flag value gives the corresponding diagonal projector. -/
theorem flagBlock_eq_diagonal {S : Type*} [DecidableEq S] (f : Bool) :
    (1 : Op S) ⊗ₖ (Matrix.single f f (1 : ℂ) ⊗ₖ (1 : Op D)) =
      Matrix.diagonal (fun i : S × (Bool × D) => if i.2.1 = f then 1 else 0) := by
  ext ⟨a, g, t⟩ ⟨b, h, u⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.diagonal_apply, Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals aesop

/-- The acceptance projector reads the Boolean flag directly. -/
theorem acceptProjOp_eq_diagonal :
    acceptProjOp ℓ D = Matrix.diagonal (fun i : KeyedOutput ℓ D =>
      if i.2.1 = true then 1 else 0) :=
  flagBlock_eq_diagonal D true

/-- The abort projector reads the Boolean flag directly. -/
theorem abortProjOp_eq_diagonal :
    abortProjOp ℓ D = Matrix.diagonal (fun i : KeyedOutput ℓ D =>
      if i.2.1 = false then 1 else 0) :=
  flagBlock_eq_diagonal D false

/-- Acceptance and abort exhaust the flag register. -/
theorem acceptProjOp_add_abortProjOp :
    acceptProjOp ℓ D + abortProjOp ℓ D = 1 := by
  rw [acceptProjOp_eq_diagonal, abortProjOp_eq_diagonal, Matrix.diagonal_add,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  cases i.2.1 <;> simp

variable [Fintype D]

/-- The acceptance projector is idempotent. -/
theorem acceptProjOp_mul_self :
    acceptProjOp ℓ D * acceptProjOp ℓ D = acceptProjOp ℓ D := by
  rw [acceptProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

/-- The abort projector is idempotent. -/
theorem abortProjOp_mul_self :
    abortProjOp ℓ D * abortProjOp ℓ D = abortProjOp ℓ D := by
  rw [abortProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

/-- The acceptance and abort projectors have orthogonal ranges. -/
theorem acceptProjOp_mul_abortProjOp :
    acceptProjOp ℓ D * abortProjOp ℓ D = 0 := by
  rw [acceptProjOp_eq_diagonal, abortProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_zero]
  congr 1
  funext i
  cases i.2.1 <;> simp

omit [Fintype D] in
/-- The acceptance projector is self-adjoint. -/
theorem acceptProjOp_conjTranspose : (acceptProjOp ℓ D)ᴴ = acceptProjOp ℓ D := by
  rw [acceptProjOp_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

omit [Fintype D] in
/-- The abort projector is self-adjoint. -/
theorem abortProjOp_conjTranspose : (abortProjOp ℓ D)ᴴ = abortProjOp ℓ D := by
  rw [abortProjOp_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- The acceptance projector on the public register is idempotent. -/
theorem acceptFlagOp_mul_self : acceptFlagOp D * acceptFlagOp D = acceptFlagOp D := by
  rw [acceptFlagOp, ← Matrix.mul_kronecker_mul, Matrix.single_mul_single_same,
    one_mul, Matrix.one_mul]

omit [Fintype D] in
/-- The acceptance projector on the public register is self-adjoint. -/
theorem acceptFlagOp_conjTranspose : (acceptFlagOp D)ᴴ = acceptFlagOp D := by
  simp only [acceptFlagOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_single,
    star_one, Matrix.conjTranspose_one]

/-- Acceptance and abort on the public register are orthogonal. -/
theorem acceptFlagOp_mul_abortFlagOp : acceptFlagOp D * abortFlagOp D = 0 := by
  rw [acceptFlagOp, abortFlagOp, ← Matrix.mul_kronecker_mul]
  simp

/-- Diagonality in the public register, allowing arbitrary coherences in the other factor. -/
def TranscriptDiag {S T : Type*} (M : Op (S × T)) : Prop :=
  ∀ i j, i.2 ≠ j.2 → M i j = 0

/-- Finite sums preserve public-register diagonality. -/
theorem transcriptDiag_sum {S T I : Type*} [Fintype I] (f : I → Op (S × T))
    (h : ∀ x, TranscriptDiag (f x)) : TranscriptDiag (∑ x, f x) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun x _ => h x i j hij

end QKD
