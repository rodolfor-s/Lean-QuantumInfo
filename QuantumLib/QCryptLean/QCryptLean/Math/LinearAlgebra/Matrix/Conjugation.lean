import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Ring

/-! # Linear matrix conjugation and entry formulas

Rectangular matrices act on square matrices by conjugation. The coefficient
semiring is commutative with a star; no positivity, norm, or nonemptiness is used.
-/

namespace Matrix

open scoped BigOperators

variable {R : Type*} [CommSemiring R] [StarRing R]

/-- **Conjugation by a matrix**, `ρ ↦ K ρ Kᴴ`.
Linearity in `ρ` holds for every `K`; completeness is a condition on an instrument family. -/
noncomputable def conjLinearMap {Hin Hout : Type*} [Fintype Hin]
      (K : Matrix Hout Hin R) : Matrix Hin Hin R →ₗ[R] Matrix Hout Hout R where
  toFun ρ := K * ρ * Kᴴ
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul]

/-- Evaluate matrix conjugation on an operator. -/
@[simp] theorem conjLinearMap_apply {Hin Hout : Type*} [Fintype Hin]
    (K : Matrix Hout Hin R) (A : Matrix Hin Hin R) :
    conjLinearMap K A = K * A * Kᴴ := rfl

/-- Conjugation by a product is composition of the two conjugation maps.
This identifies successive conjugations with conjugation by the product. -/
theorem conjLinearMap_mul {Hin Hmid Hout : Type*}
    [Fintype Hin] [Fintype Hmid]
    (L : Matrix Hout Hmid R) (K : Matrix Hmid Hin R) :
    conjLinearMap (L * K) = (conjLinearMap L).comp (conjLinearMap K) := by
  ext ρ a b
  simp only [conjLinearMap, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- Entry of a matrix conjugation. -/
theorem conjLinearMap_apply_apply (K : Matrix B A R) (ρ : Matrix A A R) (y z : B) :
    conjLinearMap K ρ y z = ∑ q, ∑ p, K y p * ρ p q * star (K z q) := by
  simp only [conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_mul _ _ _

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- A conjugation `K ρ Kᴴ` has a zero `(y, z)` entry when every entry of row `y` of `K` times
every conjugated entry of row `z` vanishes. -/
theorem conjLinearMap_apply_eq_zero (K : Matrix B A R) (ρ : Matrix A A R) (y z : B)
    (h : ∀ x x', K y x * star (K z x') = 0) : conjLinearMap K ρ y z = 0 := by
  rw [conjLinearMap_apply_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [mul_right_comm, h p q, zero_mul]

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- A conjugation has a zero row wherever the Kraus matrix has one. -/
theorem conjLinearMap_apply_eq_zero_of_row_left (K : Matrix B A R) (ρ : Matrix A A R) {y : B}
    (hy : K y = 0) (z : B) : conjLinearMap K ρ y z = 0 := by
  rw [conjLinearMap_apply_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show K y p = 0 from congrFun hy p, zero_mul, zero_mul]

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- A conjugation has a zero column wherever the Kraus matrix has a zero row. -/
theorem conjLinearMap_apply_eq_zero_of_row_right (K : Matrix B A R) (ρ : Matrix A A R) (y : B)
    {z : B} (hz : K z = 0) : conjLinearMap K ρ y z = 0 := by
  rw [conjLinearMap_apply_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show K z q = 0 from congrFun hz q, star_zero, mul_zero]

omit [Fintype B] [DecidableEq B] in
/-- The entry of a conjugation between two rows of the Kraus matrix that each have a single
nonzero entry. -/
theorem conjLinearMap_apply_of_row_eq_single (K : Matrix B A R) (ρ : Matrix A A R) {y z : B}
    {p q : A} {c d : R} (hy : K y = Pi.single p c) (hz : K z = Pi.single q d) :
    conjLinearMap K ρ y z = c * ρ p q * star d := by
  have hrow : ∀ q', ∑ p', K y p' * ρ p' q' * star (K z q') = c * ρ p q' * star (K z q') := by
    intro q'
    rw [Finset.sum_eq_single p (fun p' _ hp' => by rw [hy, Pi.single_eq_of_ne hp', zero_mul,
      zero_mul]) (fun h => absurd (Finset.mem_univ p) h), hy, Pi.single_eq_same]
  rw [conjLinearMap_apply_apply, Finset.sum_congr rfl fun q' _ => hrow q',
    Finset.sum_eq_single q (fun q' _ hq' => by rw [hz, Pi.single_eq_of_ne hq', star_zero,
      mul_zero]) (fun h => absurd (Finset.mem_univ q) h), hz, Pi.single_eq_same]

omit [Fintype B] [DecidableEq B] in
/-- **Pullback of a conjugation along rows of single entries.**  If, along `o`, the rows of the
Kraus matrix are the rows of the identity along `i` scaled by `c`, the conjugation reads back the
input operator along `i`, weighted by `star c * c`. -/
theorem conjLinearMap_submatrix_of_row_eq_single {U : Type*} (K : Matrix B A R) (ρ : Matrix A A R)
    (o : U → B) (i : U → A) (c : R) (hK : ∀ u, K (o u) = Pi.single (i u) c) :
    (conjLinearMap K ρ).submatrix o o = (star c * c) • ρ.submatrix i i := by
  ext u v
  rw [Matrix.submatrix_apply, conjLinearMap_apply_of_row_eq_single K ρ (hK u) (hK v),
    Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
  ring

omit [Fintype B] in
/-- **Conjugation by a matrix unit** reads one diagonal input entry and prepares one output
coordinate. -/
theorem conjLinearMap_single (y : B) (x : A) (c : R) (ρ : Matrix A A R) :
    conjLinearMap (Matrix.single y x c) ρ = Matrix.single y y (c * ρ x x * star c) := by
  simp only [conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single]


end Matrix
