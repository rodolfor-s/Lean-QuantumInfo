import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-! # Indistinguishable -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics

variable {I X Y Z R : Type*} [Fintype I] [Fintype X] [Fintype Y] [Fintype Z] [Fintype R]
variable [Nonempty I] [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty R]

omit [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty R] in
/-- Channel wrappers preserve the arbitrary-reference diamond bound by amplified contraction. -/
theorem traceNorm_mapTensorId_sandwich_le_diamondNorm
    (Δ : Operation X Y) (hΔ : ∀ M, Δ Mᴴ = (Δ M)ᴴ)
    (A : Operation Y Z) (hA : IsChannel A) (B : Operation I X) (hB : IsChannel B)
    (W : Op (I × R)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A.comp (Δ.comp B)) R W) ≤ diamondNorm Δ := by
  obtain ⟨_i⟩ := (inferInstance : Nonempty I)
  rw [mapTensorId_comp, LinearMap.comp_apply, mapTensorId_comp, LinearMap.comp_apply]
  exact (traceNorm_mapTensorId_le A hA _).trans
    (traceNorm_mapTensorId_le_diamondNorm_of_map_conjTranspose Δ hΔ _
      ((traceNorm_mapTensorId_le B hB W).trans hW))

omit [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty R] in
/-- Two postprocessings equal on the ideal differ by at most twice the real/ideal error. -/
theorem traceNorm_mapTensorId_sandwichPair_le
    (Φreal Φideal : Operation X Y)
    (hstar : ∀ M, (Φreal - Φideal) Mᴴ = ((Φreal - Φideal) M)ᴴ)
    (A₀ A₁ : Operation Y Z) (hA₀ : IsChannel A₀) (hA₁ : IsChannel A₁)
    (B : Operation I X) (hB : IsChannel B)
    (hideal : A₀.comp (Φideal.comp B) = A₁.comp (Φideal.comp B))
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (I × R)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀.comp (Φreal.comp B)) R W -
      mapTensorId (A₁.comp (Φreal.comp B)) R W) ≤ 2 * ε := by
  let Δ := Φreal - Φideal
  have h₀ := (traceNorm_mapTensorId_sandwich_le_diamondNorm Δ hstar A₀ hA₀ B hB W hW).trans hε
  have h₁ := (traceNorm_mapTensorId_sandwich_le_diamondNorm Δ hstar A₁ hA₁ B hB W hW).trans hε
  have he : A₀.comp (Φreal.comp B) - A₁.comp (Φreal.comp B) =
      A₀.comp (Δ.comp B) - A₁.comp (Δ.comp B) := by
    dsimp only [Δ]
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub, hideal]
    abel
  change traceNorm ((mapTensorId (A₀.comp (Φreal.comp B)) R -
    mapTensorId (A₁.comp (Φreal.comp B)) R) W) ≤ _
  rw [← mapTensorId_sub, he, mapTensorId_sub]
  change traceNorm (mapTensorId (A₀.comp (Δ.comp B)) R W -
    mapTensorId (A₁.comp (Δ.comp B)) R W) ≤ _
  exact (traceNorm_sub_le _ _).trans (by linarith)

omit [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty R] in
/-- The two-channel version needs no additional adjoint hypothesis. -/
theorem traceNorm_mapTensorId_sandwichPair_le_of_isChannel
    (Φreal Φideal : Operation X Y) (hreal : IsChannel Φreal) (hideal' : IsChannel Φideal)
    (A₀ A₁ : Operation Y Z) (hA₀ : IsChannel A₀) (hA₁ : IsChannel A₁)
    (B : Operation I X) (hB : IsChannel B)
    (hideal : A₀.comp (Φideal.comp B) = A₁.comp (Φideal.comp B))
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (I × R)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀.comp (Φreal.comp B)) R W -
      mapTensorId (A₁.comp (Φreal.comp B)) R W) ≤ 2 * ε :=
  traceNorm_mapTensorId_sandwichPair_le Φreal Φideal
    (hreal.1.sub_conjTranspose hideal'.1) A₀ A₁ hA₀ hA₁ B hB hideal ε hε W hW

end Quantum.Channels
