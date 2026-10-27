import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Stinespring -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]

open scoped Classical in
/-- An isometric dilation of a linear operation through a finite environment. -/
structure StinespringRepresentation (Φ : Operation X Y) (E : Type*) [Fintype E] where
  /-- The isometry into output and environment. -/
  isometry : Matrix (Y × E) X ℂ
  /-- Isometry in the input register. -/
  isometry_adj_mul : isometryᴴ * isometry = 1
  /-- Tracing out the environment recovers the operation on every matrix. -/
  recovers : ∀ A, Φ A = partialTraceRight (isometry * A * isometryᴴ)

/-- Stack a Kraus family into a matrix with a environment. -/
def krausIsometry (K : E → Matrix Y X ℂ) : Matrix (Y × E) X ℂ := fun p i => K p.2 p.1 i

omit [Fintype X] in
/-- The Gram matrix of the stacked family is its completeness sum. -/
theorem krausIsometry_adj_mul (K : E → Matrix Y X ℂ) :
    (krausIsometry K)ᴴ * krausIsometry K = ∑ k, (K k)ᴴ * K k := by
  ext i j
  simp only [mul_apply, conjTranspose_apply, krausIsometry, Fintype.sum_prod_type,
    Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype Y] in
/-- Tracing out a stacked Kraus environment gives the Kraus operation. -/
theorem partialTraceRight_krausIsometry (K : E → Matrix Y X ℂ) (A : Op X) :
    partialTraceRight (krausIsometry K * A * (krausIsometry K)ᴴ) = krausMap K A := by
  ext a b
  simp only [partialTraceRight_apply, krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, mul_apply, conjTranspose_apply, krausIsometry]

/-- Every complete Kraus family gives a Stinespring representation with its index as environment. -/
def KrausRepresentation.stinespring (K : KrausRepresentation X Y E) :
    StinespringRepresentation K.toOperation E where
  isometry := krausIsometry K.operators
  isometry_adj_mul := (krausIsometry_adj_mul K.operators).trans K.completeness
  recovers A := (partialTraceRight_krausIsometry K.operators A).symm

/-- The columns at a fixed environment value are the corresponding Kraus operator. -/
def StinespringRepresentation.kraus {Φ : Operation X Y} (V : StinespringRepresentation Φ E) :
    KrausRepresentation X Y E where
  operators k a i := V.isometry (a, k) i
  completeness := (krausIsometry_adj_mul _).symm.trans V.isometry_adj_mul

/-- Every Stinespring representation recovers its channel as a Kraus map. -/
theorem StinespringRepresentation.kraus_toOperation {Φ : Operation X Y}
    (V : StinespringRepresentation Φ E) : V.kraus.toOperation = Φ := by
  apply LinearMap.ext
  intro A
  let K : E → Matrix Y X ℂ := fun k => V.isometry.submatrix (fun a => (a, k)) id
  have h := partialTraceRight_krausIsometry K A
  change partialTraceRight (V.isometry * A * V.isometryᴴ) = V.kraus.toOperation A at h
  exact h.symm.trans (V.recovers A).symm

/-- An isometric dilation certifies complete positivity and trace preservation. -/
theorem StinespringRepresentation.isChannel {Φ : Operation X Y}
    (V : StinespringRepresentation Φ E) : IsChannel Φ := by
  rw [← V.kraus_toOperation]
  exact V.kraus.isChannel

omit [Fintype E] in
/-- Every channel has a dilation on the finite environment `X × Y`. -/
theorem IsChannel.exists_stinespring {Φ : Operation X Y} (h : IsChannel Φ) :
    Nonempty (StinespringRepresentation Φ (X × Y)) := by
  obtain ⟨K, rfl⟩ := h.exists_kraus
  exact ⟨K.stinespring⟩

end Quantum.Channels
