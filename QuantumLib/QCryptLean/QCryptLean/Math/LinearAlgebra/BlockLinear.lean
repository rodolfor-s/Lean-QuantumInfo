import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Block

/-!
# Linearity of the upper-left matrix block

Linearity of the upper-left matrix block.
-/

noncomputable section

@[simp]
lemma _root_.Matrix.toBlocks₁₁_add {n m : Type*} (A B : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (A + B).toBlocks₁₁ = A.toBlocks₁₁ + B.toBlocks₁₁ :=
  rfl

@[simp]
lemma _root_.Matrix.toBlocks₁₁_smul {n m : Type*} (c : ℂ) (A : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ :=
  rfl

end
