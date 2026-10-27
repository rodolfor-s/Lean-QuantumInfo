import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-!
# Amplification on a left reference register

The matrix blocks are indexed directly by the reference type. The channel and
no-signaling proofs are native and work on empty finite registers as well.
-/

noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped Kronecker

variable {X Y Z R I : Type*}

/-- Apply an operation to the second factor, leaving the left reference untouched. -/
def mapIdTensor (R : Type*) (Φ : Operation X Y) : Operation (R × X) (R × Y) where
  toFun A p q := Φ (fun i j => A (p.1, i) (q.1, j)) p.2 q.2
  map_add' A B := by ext p q; exact congrFun (congrFun (map_add Φ _ _) p.2) q.2
  map_smul' c A := by ext p q; exact congrFun (congrFun (map_smul Φ c _) p.2) q.2

/-- Left amplification respects operation composition. -/
theorem mapIdTensor_comp (Φ : Operation X Y) (Ψ : Operation Y Z) :
    mapIdTensor R (Ψ.comp Φ) = (mapIdTensor R Ψ).comp (mapIdTensor R Φ) := rfl

variable [Fintype X] [Fintype Y] [Fintype R] [Fintype I]

omit [Fintype Y] in
open scoped Classical in
/-- Left amplification tensors Kraus operators with a reference identity. -/
theorem mapIdTensor_krausMap (K : I → Matrix Y X ℂ) :
    mapIdTensor R (krausMap K) = krausMap (fun i => (1 : Op R) ⊗ₖ K i) := by
  classical
  ext A p q
  change (∑ i, K i * (Matrix.of fun x y => A (p.1, x) (q.1, y)) * (K i)ᴴ) p.2 q.2 =
    (∑ i, ((1 : Op R) ⊗ₖ K i) * A * ((1 : Op R) ⊗ₖ K i)ᴴ) p q
  simp [mul_apply, conjTranspose_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.of_apply, apply_ite]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype R] in
/-- Complete positivity is preserved by a finite left reference. -/
theorem IsCompletelyPositive.mapIdTensor [Finite X] [Finite Y] [Finite R]
    {Φ : Operation X Y} (h : IsCompletelyPositive Φ) :
    IsCompletelyPositive (mapIdTensor R Φ) := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  let := Fintype.ofFinite R
  obtain ⟨K, rfl⟩ := h.exists_kraus
  rw [mapIdTensor_krausMap]
  exact isCompletelyPositive_krausMap _

omit [Fintype I] [Fintype R] in
/-- A trace-preserving operation does not change the untouched reference marginal. -/
theorem IsTracePreserving.partialTraceRight_mapIdTensor {Φ : Operation X Y}
    (h : IsTracePreserving Φ) (A : Op (R × X)) :
    partialTraceRight (mapIdTensor R Φ A) = partialTraceRight A := by
  ext r s
  exact h (fun i j => A (r, i) (s, j))

omit [Fintype I] in
/-- Trace preservation is preserved by a finite left reference. -/
theorem IsTracePreserving.mapIdTensor {Φ : Operation X Y} (h : IsTracePreserving Φ) :
    IsTracePreserving (mapIdTensor R Φ) := by
  intro A
  rw [← trace_partialTraceRight, h.partialTraceRight_mapIdTensor, trace_partialTraceRight]

omit [Fintype I] in
/-- Channels remain channels with any finite left reference. -/
theorem IsChannel.mapIdTensor {Φ : Operation X Y} (h : IsChannel Φ) :
    IsChannel (mapIdTensor R Φ) := ⟨h.1.mapIdTensor, h.2.mapIdTensor⟩

end Quantum.Channels
