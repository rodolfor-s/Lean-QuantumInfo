import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Amplification -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder

variable {X Y I Z : Type*} [Fintype X] [Fintype Y] [Fintype I] [Fintype Z]

omit [Fintype Y] in
open scoped Classical in
/-- Amplification tensors every Kraus operator with the reference identity. -/
theorem mapTensorId_krausMap (K : I → Matrix Y X ℂ) :
    mapTensorId (krausMap K) Z = krausMap (fun i => K i ⊗ₖ (1 : Op Z)) := by
  classical
  ext A p q
  change (∑ i, K i * (Matrix.of fun x y => A (x, p.2) (y, q.2)) * (K i)ᴴ) p.1 q.1 =
    (∑ i, (K i ⊗ₖ (1 : Op Z)) * A * (K i ⊗ₖ (1 : Op Z))ᴴ) p q
  simp [mul_apply, conjTranspose_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.of_apply, apply_ite]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype Z] in
/-- Complete positivity persists under any finite amplification. -/
theorem IsCompletelyPositive.mapTensorId [Finite X] [Finite Y] [Finite Z]
    {Φ : Operation X Y} (h : IsCompletelyPositive Φ) :
    IsCompletelyPositive (mapTensorId Φ Z) := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  let := Fintype.ofFinite Z
  obtain ⟨K, rfl⟩ := h.exists_kraus
  rw [mapTensorId_krausMap]
  exact isCompletelyPositive_krausMap _

omit [Fintype I] in
/-- Trace preservation persists under amplification on an arbitrary finite reference. -/
theorem IsTracePreserving.mapTensorId {Φ : Operation X Y} (h : IsTracePreserving Φ) :
    IsTracePreserving (mapTensorId Φ Z) := by
  intro A
  change (∑ p : Y × Z, Φ (fun i j => A (i, p.2) (j, p.2)) p.1 p.1) =
    ∑ p : X × Z, A p p
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i z => A (i, z) (i, z))]
  apply Finset.sum_congr rfl
  intro z _
  exact h (fun i j => A (i, z) (j, z))

omit [Fintype I] in
/-- Channels remain channels after adjoining a finite reference register. -/
theorem IsChannel.mapTensorId {Φ : Operation X Y} (h : IsChannel Φ) :
    IsChannel (mapTensorId Φ Z) := ⟨h.1.mapTensorId, h.2.mapTensorId⟩

omit [Fintype I] [Fintype Z] [Fintype X] [Fintype Y] in
/-- Positivity with an input-sized reference already implies Choi positivity. -/
theorem isCompletelyPositive_of_mapTensorId_posSemidef [Finite X] (Φ : Operation X Y)
    (h : ∀ A : Op (X × X), A.PosSemidef → (mapTensorId Φ X A).PosSemidef) :
    IsCompletelyPositive Φ := by
  classical
  let w : X × X → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hp := (h (vecMulVec w (star w)) (posSemidef_vecMulVec_self_star w)).submatrix
    (Prod.swap : X × Y → Y × X)
  have he : (mapTensorId Φ X (vecMulVec w (star w))).submatrix Prod.swap Prod.swap =
      choiMatrix Φ := by
    ext p q
    change Φ (fun i j => w (i, p.1) * star (w (j, q.1))) p.2 q.2 =
      Φ (single p.1 q.1 1) p.2 q.2
    have hs : (fun i j => w (i, p.1) * star (w (j, q.1))) =
        (single p.1 q.1 1 : Op X) := by
      ext i j
      by_cases hi : i = p.1 <;> by_cases hj : j = q.1 <;>
        simp [w, hi, hj, eq_comm]
    rw [hs]
  exact show (choiMatrix Φ).PosSemidef from he ▸ hp

omit [Fintype I] [Fintype Z] [Fintype X] [Fintype Y] in
/-- Composition preserves complete positivity of operations. -/
theorem IsCompletelyPositive.comp [Finite X] [Finite Y] {W : Type*} [Finite W]
    {Φ : Operation X Y} {Ψ : Operation Y W}
    (hΨ : IsCompletelyPositive Ψ) (hΦ : IsCompletelyPositive Φ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  apply isCompletelyPositive_of_mapTensorId_posSemidef
  intro A hA
  rw [mapTensorId_comp]
  exact hΨ.mapTensorId.posSemidef (hΦ.mapTensorId.posSemidef hA)

omit [Fintype I] [Fintype Z] in
/-- Composition preserves channels. -/
theorem IsChannel.comp {W : Type*} [Fintype W]
    {Φ : Operation X Y} {Ψ : Operation Y W} (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ) :
    IsChannel (Ψ.comp Φ) :=
  ⟨hΨ.1.comp hΦ.1, fun A => (hΨ.2 (Φ A)).trans (hΦ.2 A)⟩

omit [Fintype Y] [Fintype I] [Fintype Z] in
/-- The identity operation is a channel, including on the empty register. -/
theorem isChannel_id : IsChannel (LinearMap.id : Operation X X) := by
  refine ⟨isCompletelyPositive_of_mapTensorId_posSemidef _ ?_, fun _ => rfl⟩
  intro A hA
  exact hA

end Quantum.Channels
