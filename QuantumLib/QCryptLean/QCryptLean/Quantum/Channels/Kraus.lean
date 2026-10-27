import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Kraus -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- The linear operation associated to a finite family of rectangular Kraus operators. -/
def krausMap (K : I → Matrix Y X ℂ) : Operation X Y where
  toFun A := ∑ i, K i * A * (K i)ᴴ
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype Y] in
/-- A finite Kraus map preserves positivity without any completeness assumption. -/
theorem posSemidef_krausMap [Finite Y] (K : I → Matrix Y X ℂ) {A : Op X} (h : A.PosSemidef) :
    (krausMap K A).PosSemidef :=
  posSemidef_sum _ fun i _ => h.mul_mul_conjTranspose_same (K i)

/-- Trace cycling for a finite family of rectangular Kraus operators. -/
theorem trace_krausMap (K : I → Matrix Y X ℂ) (A : Op X) :
    (krausMap K A).trace = ((∑ i, (K i)ᴴ * K i) * A).trace := by
  simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_mul_comm, ← Matrix.mul_assoc]

omit [Fintype Y] in
/-- The Choi matrix of a Kraus map is a sum of vectorized rank-one positive matrices. -/
theorem choiMatrix_krausMap (K : I → Matrix Y X ℂ) :
    choiMatrix (krausMap K) = ∑ i,
      vecMulVec (fun p : X × Y => K i p.2 p.1) (star (fun p : X × Y => K i p.2 p.1)) := by
  classical
  ext p q
  simp only [choiMatrix, krausMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    vecMulVec_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_apply, single_apply, conjTranspose_apply, ite_and]

omit [Fintype Y] in
/-- Every finite Kraus map is completely positive. -/
theorem isCompletelyPositive_krausMap [Finite Y] (K : I → Matrix Y X ℂ) :
    IsCompletelyPositive (krausMap K) := by
  unfold IsCompletelyPositive
  rw [choiMatrix_krausMap]
  exact posSemidef_sum _ fun i _ => posSemidef_vecMulVec_self_star _

open scoped Classical in
/-- Completeness is exactly trace preservation of a Kraus map. -/
theorem isTracePreserving_krausMap_iff (K : I → Matrix Y X ℂ) :
    IsTracePreserving (krausMap K) ↔ ∑ i, (K i)ᴴ * K i = 1 := by
  classical
  constructor
  · intro h
    ext i j
    have he := h (single j i 1)
    rw [trace_krausMap, trace_mul_comm, trace_single_mul] at he
    by_cases hij : i = j
    · subst j; simpa using he
    · simpa [one_apply, hij, Ne.symm hij] using he
  · intro h A
    rw [trace_krausMap, h, one_mul]

open scoped Classical in
/-- A complete finite Kraus family describes a channel. -/
structure KrausRepresentation (X Y I : Type*) [Fintype X] [Fintype Y] [Fintype I] where
  /-- The rectangular operators, with output rows and input columns. -/
  operators : I → Matrix Y X ℂ
  /-- The completeness relation. -/
  completeness : ∑ i, (operators i)ᴴ * operators i = 1

/-- The operation of a bundled Kraus representation. -/
def KrausRepresentation.toOperation (K : KrausRepresentation X Y I) : Operation X Y :=
  krausMap K.operators

/-- Completeness and positivity certify the represented channel. -/
theorem KrausRepresentation.isChannel (K : KrausRepresentation X Y I) :
    IsChannel K.toOperation :=
  ⟨isCompletelyPositive_krausMap _, (isTracePreserving_krausMap_iff _).mpr K.completeness⟩

omit [Fintype I] in
/-- The PSD Choi matrix supplies a Kraus family indexed by input-output pairs. -/
theorem IsCompletelyPositive.exists_kraus {Φ : Operation X Y} (h : IsCompletelyPositive Φ) :
    ∃ K : X × Y → Matrix Y X ℂ, krausMap K = Φ := by
  classical
  let K : X × Y → Matrix Y X ℂ := fun k a i => CFC.sqrt (choiMatrix Φ) (i, a) k
  refine ⟨K, choiMatrix_injective ?_⟩
  rw [choiMatrix_krausMap]
  exact (h.eq_sum_cfcSqrt_vecMulVec).symm

omit [Fintype I] in
/-- Every channel has a complete Kraus representation with a finite product index. -/
theorem IsChannel.exists_kraus {Φ : Operation X Y} (h : IsChannel Φ) :
    ∃ K : KrausRepresentation X Y (X × Y), K.toOperation = Φ := by
  obtain ⟨K, hK⟩ := h.1.exists_kraus
  exact ⟨⟨K, (isTracePreserving_krausMap_iff K).mp (hK ▸ h.2)⟩, hK⟩

omit [Fintype I] [Fintype X] [Fintype Y] in
/-- Complete positivity implies positivity on operators. -/
theorem IsCompletelyPositive.posSemidef [Finite X] [Finite Y] {Φ : Operation X Y}
    (h : IsCompletelyPositive Φ)
    {A : Op X} (hA : A.PosSemidef) : (Φ A).PosSemidef := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  obtain ⟨K, rfl⟩ := h.exists_kraus
  exact posSemidef_krausMap K hA

omit [Fintype I] in
/-- A channel acts on density operators. -/
def IsChannel.applyDensity {Φ : Operation X Y} (h : IsChannel Φ) (ρ : DensityOp X) :
    DensityOp Y := ⟨Φ ρ.toOp, h.1.posSemidef ρ.posSemidef, (h.2 _).trans ρ.trace_one⟩

omit [Fintype I] in
/-- A channel acts on sub-density operators without changing their trace mass. -/
def IsChannel.applySubDensity {Φ : Operation X Y} (h : IsChannel Φ) (ρ : SubDensityOp X) :
    SubDensityOp Y :=
  ⟨Φ ρ.toOp, h.1.posSemidef ρ.posSemidef, by rw [h.2]; exact ρ.trace_le_one⟩

end Quantum.Channels
