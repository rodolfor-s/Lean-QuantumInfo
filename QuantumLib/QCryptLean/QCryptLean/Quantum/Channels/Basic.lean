import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Basic -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X Y Z W : Type*}

/-- A quantum operation is a complex linear map, with no norm or order instances. -/
abbrev Operation (X Y : Type*) := Op X →ₗ[ℂ] Op Y

open scoped Classical in
/-- Unnormalized Choi matrix, with the input register first. -/
def choiMatrix (Φ : Operation X Y) : Op (X × Y) :=
  fun p q => Φ (single p.1 q.1 1) p.2 q.2

/-- Complete positivity of a linear map, in its finite-dimensional Choi formulation. -/
def IsCompletelyPositive (Φ : Operation X Y) : Prop := (choiMatrix Φ).PosSemidef

/-- Trace preservation on every operator. -/
def IsTracePreserving [Fintype X] [Fintype Y] (Φ : Operation X Y) : Prop :=
  ∀ A, (Φ A).trace = A.trace

/-- A channel is a completely positive, trace-preserving linear operation. -/
def IsChannel [Fintype X] [Fintype Y] (Φ : Operation X Y) : Prop :=
  IsCompletelyPositive Φ ∧ IsTracePreserving Φ

/-- Amplify on a right reference register by applying the map to each block. -/
def mapTensorId (Φ : Operation X Y) (Z : Type*) : Operation (X × Z) (Y × Z) where
  toFun A p q := Φ (fun i j => A (i, p.2) (j, q.2)) p.1 q.1
  map_add' A B := by ext p q; exact congrFun (congrFun (map_add Φ _ _) p.1) q.1
  map_smul' c A := by ext p q; exact congrFun (congrFun (map_smul Φ c _) p.1) q.1

/-- Amplification preserves composition, including empty reference registers. -/
theorem mapTensorId_comp (Φ : Operation X Y) (Ψ : Operation Y W) :
    mapTensorId (Ψ.comp Φ) Z = (mapTensorId Ψ Z).comp (mapTensorId Φ Z) := rfl

/-- Amplification is additive in its operation. -/
theorem mapTensorId_add (Φ Ψ : Operation X Y) :
    mapTensorId (Φ + Ψ) Z = mapTensorId Φ Z + mapTensorId Ψ Z := rfl

/-- Amplification commutes with subtraction of operations. -/
theorem mapTensorId_sub (Φ Ψ : Operation X Y) :
    mapTensorId (Φ - Ψ) Z = mapTensorId Φ Z - mapTensorId Ψ Z := rfl

open scoped Classical in
/-- Matrix units determine a linear operation. -/
theorem operation_ext [Finite X] {Φ Ψ : Operation X Y}
    (h : ∀ i j, Φ (single i j 1) = Ψ (single i j 1)) : Φ = Ψ := by
  classical
  let := Fintype.ofFinite X
  ext A a b
  have hA : A = ∑ i, ∑ j, A i j • single i j 1 := by
    simpa only [smul_single, smul_eq_mul, mul_one] using matrix_eq_sum_single A
  rw [hA]
  simp only [map_sum, map_smul, h]

open scoped ComplexOrder in
/-- A nonnegative scalar multiple of a completely positive operation is completely positive. -/
theorem IsCompletelyPositive.smul {Φ : Operation X Y} (hΦ : IsCompletelyPositive Φ)
    {c : ℂ} (hc : 0 ≤ c) : IsCompletelyPositive (c • Φ) := by
  change (c • choiMatrix Φ).PosSemidef
  exact Matrix.PosSemidef.smul hΦ hc

/-- A linear map is determined by its Choi matrix. -/
theorem choiMatrix_injective [Finite X] : Function.Injective (choiMatrix : Operation X Y → _) := by
  classical
  intro Φ Ψ h
  apply operation_ext
  intro i j
  ext a b
  exact congrFun (congrFun h (i, a)) (j, b)

open scoped Classical in
/-- Partial trace of the Choi matrix evaluates traces on matrix units. -/
theorem partialTraceRight_choiMatrix [Fintype Y] (Φ : Operation X Y) (i j : X) :
    partialTraceRight (choiMatrix Φ) i j = (Φ (single i j 1)).trace := rfl

variable [Fintype X] [Fintype Y]

open scoped Classical in
/-- Trace preservation is equivalent to the identity output marginal of the Choi matrix. -/
theorem isTracePreserving_iff_partialTraceRight_choiMatrix (Φ : Operation X Y) :
    IsTracePreserving Φ ↔ partialTraceRight (choiMatrix Φ) = 1 := by
  classical
  constructor
  · intro h
    ext i j
    rw [partialTraceRight_choiMatrix, h]
    by_cases hij : i = j
    · subst j; simp
    · simp [one_apply, hij]
  · intro h A
    have he (i j : X) : (Φ (single i j 1)).trace = if i = j then 1 else 0 := by
      simpa only [partialTraceRight_choiMatrix, one_apply] using congrFun (congrFun h i) j
    have hA : A = ∑ i, ∑ j, A i j • single i j 1 := by
      simpa only [smul_single, smul_eq_mul, mul_one] using matrix_eq_sum_single A
    conv_lhs => rw [hA]
    simp only [map_sum, map_smul, trace_sum, trace_smul, he]
    simp [trace, diag, smul_eq_mul]

open scoped Classical in
/-- Choi characterization of channels, with linearity enforced by the type. -/
theorem isChannel_iff (Φ : Operation X Y) :
    IsChannel Φ ↔ (choiMatrix Φ).PosSemidef ∧ partialTraceRight (choiMatrix Φ) = 1 := by
  rw [IsChannel, isTracePreserving_iff_partialTraceRight_choiMatrix]
  rfl

end Quantum.Channels
