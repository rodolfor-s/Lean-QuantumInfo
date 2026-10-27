import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations

/-! # Tensor -/


namespace Quantum.Operators

open Matrix
open scoped Kronecker ComplexOrder

variable {I X Y : Type*} {D : I → Type*}

/-- Tensor two positive operators on a product register. -/
def PosSemidefOp.kronecker [Finite X] [Finite Y]
    (A : PosSemidefOp X) (B : PosSemidefOp Y) : PosSemidefOp (X × Y) :=
  ⟨A.val ⊗ₖ B.val, A.property.kronecker B.property⟩

/-- Tensor two Hermitian operators using Mathlib's self-adjoint bundle. -/
def HermitianOp.kronecker (A : HermitianOp X) (B : HermitianOp Y) : HermitianOp (X × Y) :=
  ⟨A.val ⊗ₖ B.val, A.isHermitian.kronecker B.isHermitian⟩

/-- Tensor two unitary operators with the inherited unitary-group structure. -/
def UnitaryOp.kronecker [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (U : UnitaryOp X) (V : UnitaryOp Y) : UnitaryOp (X × Y) :=
  ⟨U.val ⊗ₖ V.val, kronecker_mem_unitary U.property V.property⟩

/-- A dependent tensor family of normalized states. -/
def DensityOp.tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (ρ : ∀ i, DensityOp (D i)) : DensityOp ((i : I) → D i) where
  toOp := Matrix.piTensorProduct (fun i => (ρ i).toOp)
  posSemidef := Matrix.PosSemidef.piTensorProduct (fun i => (ρ i).posSemidef)
  trace_one := by simp [Matrix.trace_piTensorProduct, (ρ _).trace_one]

/-- A dependent tensor family of sub-normalized states. -/
def SubDensityOp.tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (ρ : ∀ i, SubDensityOp (D i)) : SubDensityOp ((i : I) → D i) where
  toOp := Matrix.piTensorProduct (fun i => (ρ i).toOp)
  posSemidef := Matrix.PosSemidef.piTensorProduct (fun i => (ρ i).posSemidef)
  trace_le_one := by
    rw [Matrix.trace_piTensorProduct]
    have hr (i : I) : (ρ i).toOp.trace = ((ρ i).trace : ℂ) := by
      apply Complex.ext <;> simp [SubDensityOp.trace, (ρ i).trace_im]
    simp_rw [hr]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
    exact Finset.prod_le_one₀ (fun i _ => (ρ i).trace_nonneg) (fun i _ => (ρ i).trace_le_one)

/-- The real trace of a family of positive blocks is the product of their real traces. -/
theorem SubDensityOp.trace_tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (ρ : ∀ i, SubDensityOp (D i)) :
    (SubDensityOp.tensorFamily ρ).trace = ∏ i, (ρ i).trace := by
  unfold SubDensityOp.trace SubDensityOp.tensorFamily
  rw [Matrix.trace_piTensorProduct]
  have hr (i : I) : (ρ i).toOp.trace = ((ρ i).trace : ℂ) := by
    apply Complex.ext <;> simp [SubDensityOp.trace, (ρ i).trace_im]
  simp_rw [hr]
  simp only [← Complex.ofReal_prod, Complex.ofReal_re]

/-- An operator tensor power indexed by its positions as functions. -/
def Op.tensorPow (A : Op X) (k : ℕ) : Op (Fin k → X) :=
  Matrix.piTensorProduct (fun _ : Fin k => A)

/-- A normalized tensor power. -/
def DensityOp.tensorPow [Fintype X] (ρ : DensityOp X) (k : ℕ) : DensityOp (Fin k → X) :=
  DensityOp.tensorFamily (fun _ : Fin k => ρ)

/-- A sub-normalized tensor power. -/
def SubDensityOp.tensorPow [Fintype X] (ρ : SubDensityOp X) (k : ℕ) :
    SubDensityOp (Fin k → X) := SubDensityOp.tensorFamily (fun _ : Fin k => ρ)

/-- Entries of an operator power are products of the single-site entries. -/
@[simp] theorem Op.tensorPow_apply (A : Op X) (k : ℕ) (x y : Fin k → X) :
    Op.tensorPow A k x y = ∏ i, A (x i) (y i) := rfl

/-- Multiplication of powers is sitewise. -/
theorem Op.tensorPow_mul [Fintype X] (A B : Op X) (k : ℕ) :
    Op.tensorPow (A * B) k = Op.tensorPow A k * Op.tensorPow B k :=
  (Matrix.piTensorProduct_mul _ _).symm

/-- The trace of a tensor power is the power of the trace. -/
theorem Op.trace_tensorPow [Fintype X] (A : Op X) (k : ℕ) :
    (Op.tensorPow A k).trace = A.trace ^ k := by
  simp [Op.tensorPow, Matrix.trace_piTensorProduct]

/-- A tensor family of kets on dependent registers. -/
def Ket.tensorFamily [Fintype I] (v : ∀ i, Ket (D i)) : Ket ((i : I) → D i) :=
  ⟨fun x => ∏ i, (v i).vec (x i)⟩

/-- A tensor family of bras on dependent registers. -/
def Bra.tensorFamily [Fintype I] (v : ∀ i, Bra (D i)) : Bra ((i : I) → D i) :=
  ⟨fun x => ∏ i, (v i).vec (x i)⟩

/-- A tensor family of normalized vectors is normalized. -/
def NormKet.tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (v : ∀ i, NormKet (D i)) : NormKet ((i : I) → D i) where
  toKet := Ket.tensorFamily (fun i => (v i).toKet)
  normalized := by
    change (∑ x : (i : I) → D i, star (∏ i, (v i).vec (x i)) *
      ∏ i, (v i).vec (x i)) = 1
    simp only [star_prod, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i x => star ((v i).vec x) * (v i).vec x)).symm.trans
      (Finset.prod_eq_one (fun i _ => (v i).normalized))

/-- The projector of a tensor ket is the tensor of its projectors. -/
theorem Ket.projector_kronecker (v : Ket X) (w : Ket Y) :
    (v.kronecker w).projector = v.projector ⊗ₖ w.projector := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  change (v.vec x * w.vec y) * star (v.vec x' * w.vec y') =
    (v.vec x * star (v.vec x')) * (w.vec y * star (w.vec y'))
  rw [star_mul']
  ring

/-- Tensor two normalized vectors on their product register. -/
def NormKet.kronecker [Fintype X] [Fintype Y] (v : NormKet X) (w : NormKet Y) :
    NormKet (X × Y) where
  toKet := v.toKet.kronecker w.toKet
  normalized := by
    rw [Ket.IsNormalized, ← Ket.trace_projector, Ket.projector_kronecker,
      Matrix.trace_kronecker, Ket.trace_projector, Ket.trace_projector,
      v.normalized, w.normalized, mul_one]

/-- Vector and density product constructions agree. -/
theorem NormKet.toDensityOp_kronecker [Fintype X] [Fintype Y]
    (v : NormKet X) (w : NormKet Y) :
    (v.kronecker w).toDensityOp = v.toDensityOp.kronecker w.toDensityOp := by
  apply DensityOp.ext
  exact v.toKet.projector_kronecker w.toKet

/-- Product registers preserve purity of density states. -/
theorem DensityOp.isPure_kronecker [Fintype X] [Fintype Y]
    {ρ : DensityOp X} {σ : DensityOp Y} (hρ : ρ.IsPure) (hσ : σ.IsPure) :
    (ρ.kronecker σ).IsPure := by
  change (ρ.toOp ⊗ₖ σ.toOp) * (ρ.toOp ⊗ₖ σ.toOp) = _
  rw [← mul_kronecker_mul, hρ, hσ]
  rfl

/-- Purity of each component gives purity of the dependent family. -/
theorem DensityOp.isPure_tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    {ρ : ∀ i, DensityOp (D i)} (h : ∀ i, (ρ i).IsPure) :
    (DensityOp.tensorFamily ρ).IsPure := by
  change Matrix.piTensorProduct _ * Matrix.piTensorProduct _ = _
  rw [Matrix.piTensorProduct_mul]
  exact congrArg Matrix.piTensorProduct (funext h)

/-- Pure states have pure tensor powers, including the empty power. -/
theorem DensityOp.isPure_tensorPow [Fintype X] {ρ : DensityOp X} (h : ρ.IsPure) (k : ℕ) :
    (ρ.tensorPow k).IsPure := DensityOp.isPure_tensorFamily (fun _ => h)

/-- A tensor family of vector projectors is the projector of the tensor vector. -/
theorem Ket.projector_tensorFamily [Fintype I] (v : ∀ i, Ket (D i)) :
    (Ket.tensorFamily v).projector = Matrix.piTensorProduct (fun i => (v i).projector) := by
  ext x y
  change (∏ i, (v i).vec (x i)) * star (∏ i, (v i).vec (y i)) =
    ∏ i, (v i).vec (x i) * star ((v i).vec (y i))
  rw [star_prod, Finset.prod_mul_distrib]

/-- Normalized vector families and state families give the same density operator. -/
theorem NormKet.toDensityOp_tensorFamily [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (v : ∀ i, NormKet (D i)) :
    (NormKet.tensorFamily v).toDensityOp = DensityOp.tensorFamily (fun i => (v i).toDensityOp) := by
  apply DensityOp.ext
  exact Ket.projector_tensorFamily _

end Quantum.Operators
