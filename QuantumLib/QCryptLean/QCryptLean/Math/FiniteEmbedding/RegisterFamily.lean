import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Prod

/-! # Register Family -/


open scoped BigOperators

/-- Expand a finite sum along any duplicate-free exhaustive list of its indices. -/
theorem Fintype.sum_univ_eq_list_sum {X : Type*} [Fintype X]
    {M : Type*} [AddCommMonoid M] (l : List X) (hnd : l.Nodup)
    (hcov : ∀ x : X, x ∈ l) (f : X → M) : ∑ x, f x = (l.map f).sum := by
  classical
  have huniv : (Finset.univ : Finset X) = l.toFinset :=
    (Finset.eq_univ_iff_forall.mpr fun x => List.mem_toFinset.mpr (hcov x)).symm
  rw [huniv, List.sum_toFinset _ hnd]

namespace Math

/-- A possibly-empty register with stored computational instances. -/
structure FiniteRegister where
  /-- The register's underlying type. -/
  carrier : Type
  /-- The finite enumeration stored with the register carrier. -/
  [fin : Fintype carrier]
  /-- Decidable equality of computational register labels. -/
  [dec : DecidableEq carrier]

instance : CoeSort FiniteRegister Type := ⟨FiniteRegister.carrier⟩

/-- Finiteness is available without unfolding a register-valued family. -/
instance FiniteRegister.instFintypeCarrier (X : FiniteRegister) : Fintype X.carrier := X.fin

/-- Decidable equality is available without unfolding a register-valued family. -/
instance FiniteRegister.instDecidableEqCarrier (X : FiniteRegister) : DecidableEq X.carrier :=
  X.dec

/-- A finite indexed family of possibly-empty finite register types. -/
structure FiniteRegisterFamily (P : Type) [Fintype P] [DecidableEq P] where
  /-- The register at each index. -/
  reg : P → Type
  [finReg : ∀ i, Fintype (reg i)]
  [decReg : ∀ i, DecidableEq (reg i)]

attribute [instance] FiniteRegisterFamily.finReg FiniteRegisterFamily.decReg

namespace FiniteRegisterFamily

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The joint register is the dependent product of all local registers. -/
abbrev total (R : FiniteRegisterFamily P) : Type := ∀ i, R.reg i

instance (R : FiniteRegisterFamily P) : Fintype R.total := Pi.instFintype
instance (R : FiniteRegisterFamily P) : DecidableEq R.total := Fintype.decidablePiFintype

/-- All registers except the one at index `i`. -/
abbrev rest (R : FiniteRegisterFamily P) (i : P) : Type :=
  ∀ j : {j : P // j ≠ i}, R.reg j

instance (R : FiniteRegisterFamily P) (i : P) : Fintype (R.rest i) := Pi.instFintype
instance (R : FiniteRegisterFamily P) (i : P) : DecidableEq (R.rest i) :=
  Fintype.decidablePiFintype

/-- Assemble one coordinate and the remaining coordinates into a joint configuration. -/
def consAt (R : FiniteRegisterFamily P) (i : P) (a : R.reg i) (y : R.rest i) : R.total :=
  fun j => if h : j = i then h ▸ a else y ⟨j, h⟩

/-- Assembly recovers the distinguished coordinate. -/
@[simp] theorem consAt_self (R : FiniteRegisterFamily P) (i : P) (a : R.reg i)
    (y : R.rest i) : R.consAt i a y i = a := by
  simp [consAt]

/-- Assembly recovers every other coordinate. -/
@[simp] theorem consAt_of_ne (R : FiniteRegisterFamily P) (i : P) (a : R.reg i)
    (y : R.rest i) {j : P} (h : j ≠ i) : R.consAt i a y j = y ⟨j, h⟩ := by
  simp [consAt, h]

/-- Reassembling a configuration from its own coordinates leaves it unchanged. -/
@[simp] theorem consAt_apply_rest (R : FiniteRegisterFamily P) (i : P) (x : R.total) :
    R.consAt i (x i) (fun j => x j) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Split a joint configuration into one coordinate and the remaining coordinates. -/
def splitAt (R : FiniteRegisterFamily P) (i : P) : R.total ≃ R.reg i × R.rest i :=
  Equiv.piSplitAt i R.reg

/-- The inverse of splitting is coordinate assembly. -/
theorem splitAt_symm_apply (R : FiniteRegisterFamily P) (i : P) (p : R.reg i × R.rest i) :
    (R.splitAt i).symm p = R.consAt i p.1 p.2 := rfl

/-- Decompose a joint-register sum into the sum over one coordinate and all the others. -/
theorem sum_univ_total_splitAt {M : Type*} [AddCommMonoid M] (R : FiniteRegisterFamily P)
    (i : P) (f : R.total → M) :
    ∑ x, f x = ∑ a : R.reg i, ∑ y : R.rest i, f (R.consAt i a y) := by
  rw [← Equiv.sum_comp (R.splitAt i).symm f, Fintype.sum_prod_type]
  rfl

/-- Decompose a complex matrix trace along one coordinate of its dependent-product index. -/
theorem trace_eq_sum_splitAt (R : FiniteRegisterFamily P) (i : P)
    (M : Matrix R.total R.total ℂ) :
    M.trace = ∑ a : R.reg i, ∑ y : R.rest i, M (R.consAt i a y) (R.consAt i a y) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact sum_univ_total_splitAt R i _

/-- Build a family from bundled registers, projecting the stored instances at each index.

Reducibility lets this constructor participate in computational instance inference when the
family supplied by the caller is itself reducible. -/
@[reducible] def ofFam (F : P → FiniteRegister) : FiniteRegisterFamily P where
  reg i := (F i).carrier

/-- Bundled construction retains the underlying register at each index. -/
@[simp] theorem ofFam_reg (F : P → FiniteRegister) (i : P) :
    (ofFam F).reg i = (F i).carrier := rfl

/-- Read a register family as a family of bundles, retaining its stored instances. -/
def toFam (R : FiniteRegisterFamily P) : P → FiniteRegister := fun i => ⟨R.reg i⟩

/-- Bundling and reconstructing a family is the identity, including its stored instances. -/
theorem ofFam_toFam (R : FiniteRegisterFamily P) : ofFam R.toFam = R := rfl

/-- Constructing and then bundling a family is the identity. -/
theorem toFam_ofFam (F : P → FiniteRegister) : (ofFam F).toFam = F := rfl

end FiniteRegisterFamily
end Math
