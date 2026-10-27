import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Adjoint -/


namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]

omit [Fintype X] [Fintype Y] in
/-- Complete positivity preserves adjoints, by the intrinsic finite Kraus representation. -/
theorem IsCompletelyPositive.conjTranspose_apply [Finite X] [Finite Y] {Φ : Operation X Y}
    (h : IsCompletelyPositive Φ) (A : Op X) : Φ Aᴴ = (Φ A)ᴴ := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  obtain ⟨K, rfl⟩ := h.exists_kraus
  change (∑ i, K i * Aᴴ * (K i)ᴴ) = (∑ i, K i * A * (K i)ᴴ)ᴴ
  simp only [conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [Fintype X] [Fintype Y] in
/-- Differences of completely positive maps preserve adjoints. -/
theorem IsCompletelyPositive.sub_conjTranspose [Finite X] [Finite Y] {Φ Ψ : Operation X Y}
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) (A : Op X) :
    (Φ - Ψ) Aᴴ = ((Φ - Ψ) A)ᴴ := by
  simp only [LinearMap.sub_apply, hΦ.conjTranspose_apply, hΨ.conjTranspose_apply, conjTranspose_sub]

/-- Channel preprocessing and postprocessing preserve the middle map's adjoint property. -/
theorem comp_comp_conjTranspose_of_isChannel (Δ : Operation X Y)
    (hΔ : ∀ M, Δ Mᴴ = (Δ M)ᴴ) (A : Operation Y Z) (hA : IsChannel A)
    (B : Operation W X) (hB : IsChannel B) (M : Op W) :
    (A.comp (Δ.comp B)) Mᴴ = ((A.comp (Δ.comp B)) M)ᴴ := by
  simp only [LinearMap.comp_apply, hB.1.conjTranspose_apply, hΔ, hA.1.conjTranspose_apply]

end Quantum.Channels
