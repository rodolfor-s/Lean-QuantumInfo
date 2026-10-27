import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Bra Ket -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X Y : Type*}

/-- A column vector with a named basis type. -/
@[ext] structure Ket (X : Type*) where
  /-- The column's coefficients in the register basis. -/
  vec : X → ℂ

/-- A row vector with a named basis type. -/
@[ext] structure Bra (X : Type*) where
  /-- The row's coefficients in the register basis. -/
  vec : X → ℂ

/-- Pointwise zero. -/
instance : Zero (Ket X) := ⟨⟨0⟩⟩

/-- Pointwise addition. -/
instance : Add (Ket X) := ⟨fun x y => ⟨x.vec + y.vec⟩⟩

/-- Pointwise negation. -/
instance : Neg (Ket X) := ⟨fun x => ⟨-x.vec⟩⟩

/-- Pointwise subtraction. -/
instance : Sub (Ket X) := ⟨fun x y => ⟨x.vec - y.vec⟩⟩

/-- Pointwise scalar multiplication. -/
instance {S : Type*} [SMul S ℂ] : SMul S (Ket X) := ⟨fun s x => ⟨s • x.vec⟩⟩

/-- The additive structure is inherited from the component functions. -/
instance : AddCommGroup (Ket X) :=
  Function.Injective.addCommGroup Ket.vec (fun _ _ h => Ket.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The scalar module structure is inherited from the component functions. -/
instance {S : Type*} [Semiring S] [Module S ℂ] : Module S (Ket X) :=
  Function.Injective.module S
    { toFun := Ket.vec, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => Ket.ext h) (fun _ _ => rfl)

/-- Transport a vector by relabelling its basis. -/
def Ket.reindex (e : X ≃ Y) (v : Ket X) : Ket Y := ⟨v.vec ∘ e.symm⟩

/-- Pointwise zero. -/
instance : Zero (Bra X) := ⟨⟨0⟩⟩

/-- Pointwise addition. -/
instance : Add (Bra X) := ⟨fun x y => ⟨x.vec + y.vec⟩⟩

/-- Pointwise negation. -/
instance : Neg (Bra X) := ⟨fun x => ⟨-x.vec⟩⟩

/-- Pointwise subtraction. -/
instance : Sub (Bra X) := ⟨fun x y => ⟨x.vec - y.vec⟩⟩

/-- Pointwise scalar multiplication. -/
instance {S : Type*} [SMul S ℂ] : SMul S (Bra X) := ⟨fun s x => ⟨s • x.vec⟩⟩

/-- The additive structure is inherited from the component functions. -/
instance : AddCommGroup (Bra X) :=
  Function.Injective.addCommGroup Bra.vec (fun _ _ h => Bra.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The scalar module structure is inherited from the component functions. -/
instance {S : Type*} [Semiring S] [Module S ℂ] : Module S (Bra X) :=
  Function.Injective.module S
    { toFun := Bra.vec, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => Bra.ext h) (fun _ _ => rfl)

/-- Transport a vector by relabelling its basis. -/
def Bra.reindex (e : X ≃ Y) (v : Bra X) : Bra Y := ⟨v.vec ∘ e.symm⟩

/-- The adjoint of a column vector is its conjugate row. -/
def Ket.dag (v : Ket X) : Bra X := ⟨star v.vec⟩

/-- The adjoint of a row vector is its conjugate column. -/
def Bra.dag (v : Bra X) : Ket X := ⟨star v.vec⟩

/-- The outer product can have different row and column registers. -/
instance : HMul (Ket X) (Bra Y) (Matrix X Y ℂ) :=
  ⟨fun v w => vecMulVec v.vec w.vec⟩

/-- Contract a row with a column on the same register. -/
instance [Fintype X] : HMul (Bra X) (Ket X) ℂ := ⟨fun v w => v.vec ⬝ᵥ w.vec⟩

/-- A rectangular operator acts on a column vector. -/
instance [Fintype Y] : HMul (Matrix X Y ℂ) (Ket Y) (Ket X) :=
  ⟨fun A v => ⟨A *ᵥ v.vec⟩⟩

/-- A row vector acts on a rectangular operator. -/
instance [Fintype X] : HMul (Bra X) (Matrix X Y ℂ) (Bra Y) :=
  ⟨fun v A => ⟨v.vec ᵥ* A⟩⟩

/-- Taking the adjoint twice restores a ket. -/
@[simp] theorem Ket.dag_dag (v : Ket X) : v.dag.dag = v := by
  ext x
  exact star_star _

/-- Taking the adjoint twice restores a bra. -/
@[simp] theorem Bra.dag_dag (v : Bra X) : v.dag.dag = v := by
  ext x
  exact star_star _

/-- The positive rank-one matrix determined by a ket. -/
def Ket.projector (v : Ket X) : Op X := v * v.dag

/-- Acting on a ket conjugates its rank-one projector by the acting matrix. -/
theorem Ket.projector_mul [Fintype Y] (A : Matrix X Y ℂ) (v : Ket Y) :
    (A * v).projector = A * v.projector * Aᴴ := by
  change vecMulVec (A *ᵥ v.vec) (star (A *ᵥ v.vec)) =
    A * vecMulVec v.vec (star v.vec) * Aᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- Rank-one ket projectors are positive semidefinite. -/
theorem Ket.posSemidef_projector [Finite X] (v : Ket X) : v.projector.PosSemidef :=
  posSemidef_vecMulVec_self_star v.vec

/-- Tensor two kets by retaining their two component indices. -/
def Ket.kronecker (v : Ket X) (w : Ket Y) : Ket (X × Y) :=
  ⟨fun p => v.vec p.1 * w.vec p.2⟩

/-- Tensor two bras by retaining their two component indices. -/
def Bra.kronecker (v : Bra X) (w : Bra Y) : Bra (X × Y) :=
  ⟨fun p => v.vec p.1 * w.vec p.2⟩

/-- The trace of a rank-one ket projector is the squared norm of the ket. -/
theorem Ket.trace_projector [Fintype X] (v : Ket X) :
    v.projector.trace = (v.dag * v : ℂ) := by
  change (∑ x, v.vec x * star (v.vec x)) = ∑ x, star (v.vec x) * v.vec x
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- A ket is normalized when its self inner product is one. -/
def Ket.IsNormalized [Fintype X] (v : Ket X) : Prop := (v.dag * v : ℂ) = 1

/-- A normalized column vector, storing its exact complex normalization. -/
structure NormKet (X : Type*) [Fintype X] extends Ket X where
  normalized : toKet.IsNormalized

/-- Relabel a normalized ket along an equivalence of its basis indices. -/
def NormKet.reindex [Fintype X] [Fintype Y] (e : X ≃ Y) (v : NormKet X) : NormKet Y where
  toKet := v.toKet.reindex e
  normalized := by
    change (∑ y, star (v.vec (e.symm y)) * v.vec (e.symm y)) = 1
    exact (Equiv.sum_comp e.symm (fun x => star (v.vec x) * v.vec x)).trans v.normalized

/-- A normalized ket defines a density operator. -/
def NormKet.toDensityOp [Fintype X] (v : NormKet X) : DensityOp X where
  toOp := v.toKet.projector
  posSemidef := v.toKet.posSemidef_projector
  trace_one := v.toKet.trace_projector.trans v.normalized

/-- A computational-basis ket. -/
def stdKet [DecidableEq X] (x : X) : Ket X := ⟨Pi.single x 1⟩

/-- A computational-basis ket is normalized. -/
theorem stdKet_isNormalized [Fintype X] [DecidableEq X] (x : X) :
    (stdKet x).IsNormalized := by
  change (star (Pi.single x (1 : ℂ)) ⬝ᵥ Pi.single x (1 : ℂ)) = (1 : ℂ)
  simp [dotProduct, Pi.single_apply]

/-- A computational-basis normalized ket. -/
def stdNormKet [Fintype X] [DecidableEq X] (x : X) : NormKet X :=
  ⟨stdKet x, stdKet_isNormalized x⟩

end Quantum.Operators
