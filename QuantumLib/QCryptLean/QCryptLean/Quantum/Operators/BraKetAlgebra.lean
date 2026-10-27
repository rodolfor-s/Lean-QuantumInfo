import QCryptLean.Quantum.Operators.BraKet

/-! # Algebra of kets and bras -/
namespace Quantum.Operators
open Matrix
open scoped ComplexConjugate

/-- The zero ket has zero components. -/
@[simp] theorem Ket.zero_vec {X : Type*} (x : X) : (0 : Ket X).vec x = 0 := rfl

/-- Expand ψ * φ (Ket × Bra) -/
@[simp] lemma ket_mul_bra_apply {n : Type*} (ψ : Ket n) (φ : Bra n) (i j : n) :
    (ψ * φ : Op n) i j = ψ.vec i * φ.vec j := rfl

/-- Expand a bra-ket product to a coordinate sum. This expansion is explicit so that simp
can extract scalars and contract elementary products without introducing a sum. -/
lemma bra_mul_ket_eq {n : Type*} [Fintype n] (φ : Bra n) (ψ : Ket n) :
    (φ * ψ : ℂ) = ∑ i, φ.vec i * ψ.vec i := rfl

/-- Expand A * ψ (Op × Ket) -/
@[simp] lemma op_mul_ket_vec {n : Type*} [Fintype n] (A : Op n) (ψ : Ket n) :
    (A * ψ : Ket n).vec = A.mulVec ψ.vec := rfl

/-- Expand φ * A (Bra × Op) -/
@[simp] lemma bra_mul_op_vec {n : Type*} [Fintype n] (φ : Bra n) (A : Op n) (j : n) :
    (φ * A : Bra n).vec j = ∑ i, φ.vec i * A i j := rfl

/-- The identity operator acts trivially on a ket: `(1 : Op n) * ψ = ψ`. -/
@[simp] theorem one_op_mul_ket {n : Type*} [Fintype n] [DecidableEq n] (ψ : Ket n) :
    (1 : Op n) * ψ = ψ := by
  ext i
  simp only [op_mul_ket_vec, Matrix.one_mulVec]

/-- Op * (Ket * Bra) = (Op * Ket) * Bra -/
theorem op_mul_ketbra {n : Type*} [Fintype n] (A : Op n) (ψ : Ket n) (φ : Bra n) :
    A * (ψ * φ) = (A * ψ) * φ := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-- (Ket * Bra) * Op = Ket * (Bra * Op) -/
theorem ketbra_mul_op {n : Type*} [Fintype n] (ψ : Ket n) (φ : Bra n) (A : Op n) :
    (ψ * φ) * A = ψ * (φ * A) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_op_vec]
  rw [Finset.mul_sum]
  congr 1
  ext k
  ring

/-- (Bra * Op) * Ket = Bra * (Op * Ket) -/
theorem braop_mul_ket {n : Type*} [Fintype n] (φ : Bra n) (A : Op n) (ψ : Ket n) :
    (φ * A) * ψ = φ * (A * ψ) := by
  simp only [bra_mul_ket_eq, bra_mul_op_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  conv_lhs =>
    arg 2; ext j
    rw [Finset.sum_mul]
  conv_rhs =>
    arg 2; ext i
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- Bra * (Ket * Bra) = (Bra * Ket) * Bra
    Fundamental: ⟨φ|(|χ⟩⟨ξ|) = ⟨φ|χ⟩⟨ξ| -/
theorem bra_mul_ketbra {n : Type*} [Fintype n] (φ : Bra n) (χ : Ket n) (ξ : Bra n) :
    φ * (χ * ξ) = (φ * χ) • ξ := by
  ext j
  simp only [bra_mul_op_vec, ket_mul_bra_apply, bra_mul_ket_eq]
  trans (∑ x, (φ.vec x * χ.vec x) * ξ.vec j)
  · congr 1; funext k; ring
  rw [← Finset.sum_mul]
  rfl

/-- Helper: (c • ψ).vec = c • ψ.vec -/
@[simp]
lemma Ket.smul_vec {n : Type*} (c : ℂ) (ψ : Ket n) : (c • ψ).vec = c • ψ.vec := rfl

/-- Helper: (c • φ).vec = c • φ.vec for Bra -/
@[simp]
lemma Bra.smul_vec {n : Type*} (c : ℂ) (φ : Bra n) : (c • φ).vec = c • φ.vec := rfl

/-- (c • A) * ψ = c • (A * ψ) -/
@[simp]
theorem smul_op_mul_ket {n : Type*} [Fintype n] (c : ℂ) (A : Op n) (ψ : Ket n) :
    (c • A) * ψ = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

/-- A * (c • ψ) = c • (A * ψ) -/
@[simp]
theorem op_mul_smul_ket {n : Type*} [Fintype n] (A : Op n) (c : ℂ) (ψ : Ket n) :
    A * (c • ψ) = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec,
             Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- (c • ψ) * φ = c • (ψ * φ) -/
@[simp]
theorem smul_ket_mul_bra {n : Type*} (c : ℂ) (ψ : Ket n) (φ : Bra n) :
    (c • ψ) * φ = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.smul_vec, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- ψ * (c • φ) = c • (ψ * φ) -/
@[simp]
theorem ket_mul_smul_bra {n : Type*} (ψ : Ket n) (c : ℂ) (φ : Bra n) :
    ψ * (c • φ) = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Matrix.smul_apply, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  ring

/-- (c • φ) * ψ = c • (φ * ψ) -/
@[simp]
theorem smul_bra_mul_ket {n : Type*} [Fintype n] (c : ℂ) (φ : Bra n) (ψ : Ket n) :
    (c • φ) * ψ = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- φ * (c • ψ) = c • (φ * ψ) -/
@[simp]
theorem bra_mul_smul_ket {n : Type*} [Fintype n] (φ : Bra n) (c : ℂ) (ψ : Ket n) :
    φ * (c • ψ) = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, φ.vec i * (c * ψ.vec i))
  · rfl
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- (⟨ψ| + ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ + ⟨φ|χ⟩ (left distributivity) -/
theorem bra_add_mul_ket {n : Type*} [Fintype n] (ψ φ : Bra n) (χ : Ket n) :
    (ψ + φ) * χ = ψ * χ + φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ + φ).vec i = ψ.vec i + φ.vec i from rfl, add_mul]
  rw [Finset.sum_add_distrib]

/-- ⟨ψ|(|φ⟩ + |χ⟩) = ⟨ψ|φ⟩ + ⟨ψ|χ⟩ (right distributivity) -/
theorem bra_mul_add_ket {n : Type*} [Fintype n] (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ + χ) = ψ * φ + ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ + χ).vec i = φ.vec i + χ.vec i from rfl, mul_add]
  rw [Finset.sum_add_distrib]

/-- (⟨ψ| - ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ - ⟨φ|χ⟩ (left distributivity for subtraction) -/
theorem bra_sub_mul_ket {n : Type*} [Fintype n] (ψ φ : Bra n) (χ : Ket n) :
    (ψ - φ) * χ = ψ * χ - φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ - φ).vec i = ψ.vec i - φ.vec i from rfl, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- ⟨ψ|(|φ⟩ - |χ⟩) = ⟨ψ|φ⟩ - ⟨ψ|χ⟩ (right distributivity for subtraction) -/
theorem bra_mul_sub_ket {n : Type*} [Fintype n] (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ - χ) = ψ * φ - ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ - χ).vec i = φ.vec i - χ.vec i from rfl, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Physics: (|ψ⟩⟨φ|)(|χ⟩⟨ξ|) = ⟨φ|χ⟩ • |ψ⟩⟨ξ|

    Direct proof by matrix calculation.
-/
theorem ketbra_mul_ketbra {n : Type*} [Fintype n] (ψ χ : Ket n) (φ ξ : Bra n) :
    (ψ * φ) * (χ * ξ) = (φ * χ) • (ψ * ξ) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_ket_eq, Matrix.smul_apply, smul_eq_mul]
  trans (∑ x, (φ.vec x * χ.vec x) * (ψ.vec i * ξ.vec j))
  · congr 1; funext x; ring
  · rw [← Finset.sum_mul]

/-- Zero ket times any bra is zero matrix -/
@[simp]
lemma zero_ket_mul_bra {n : Type*} (φ : Bra n) : (0 : Ket n) * φ = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Zero bra component -/
@[simp]
lemma Bra.zero_vec {n : Type*} (j : n) : (0 : Bra n).vec j = 0 := rfl

/-- Any ket times zero bra is zero matrix -/
@[simp]
lemma ket_mul_zero_bra {n : Type*} (ψ : Ket n) : ψ * (0 : Bra n) = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Ket addition at component level -/
@[simp]
lemma Ket.add_vec {n : Type*} (ψ φ : Ket n) (i : n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra addition at component level -/
@[simp]
lemma Bra.add_vec {n : Type*} (ψ φ : Bra n) (i : n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra subtraction at component level -/
@[simp]
lemma Bra.sub_vec {n : Type*} (ψ φ : Bra n) (i : n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Bra negation at component level -/
@[simp]
lemma Bra.neg_vec {n : Type*} (φ : Bra n) (i : n) : (-φ).vec i = -φ.vec i := rfl

/-- Ket subtraction at component level -/
@[simp]
lemma Ket.sub_vec {n : Type*} (ψ φ : Ket n) (i : n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Ket negation at component level -/
@[simp]
lemma Ket.neg_vec {n : Type*} (ψ : Ket n) (i : n) : (-ψ).vec i = -ψ.vec i := rfl

/-- The zero operator annihilates every ket. -/
@[simp]
lemma zero_op_mul_ket {n : Type*} [Fintype n] (ψ : Ket n) : (0 : Op n) * ψ = 0 := by
  ext i
  simp

/-- An operator annihilates the zero ket. -/
@[simp]
lemma op_mul_zero_ket {n : Type*} [Fintype n] (A : Op n) : A * (0 : Ket n) = 0 := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- A zero bra has zero inner product with every ket. -/
@[simp]
lemma zero_bra_mul_ket {n : Type*} [Fintype n] (ψ : Ket n) : (0 : Bra n) * ψ = (0 : ℂ) := by
  simp [bra_mul_ket_eq]

/-- Every bra has zero inner product with the zero ket. -/
@[simp]
lemma bra_mul_zero_ket {n : Type*} [Fintype n] (β : Bra n) : β * (0 : Ket n) = (0 : ℂ) := by
  simp [bra_mul_ket_eq]

/-- The zero bra remains zero under an operator action. -/
@[simp]
lemma zero_bra_mul_op {n : Type*} [Fintype n] (A : Op n) : (0 : Bra n) * A = 0 := by
  ext i
  simp

/-- The zero operator annihilates every bra. -/
@[simp]
lemma bra_mul_zero_op {n : Type*} [Fintype n] (β : Bra n) : β * (0 : Op n) = 0 := by
  ext i
  simp

/-- Negation passes through the product. -/
@[simp]
lemma neg_op_mul_ket {n : Type*} [Fintype n] (A : Op n) (ψ : Ket n) : (-A) * ψ = -(A * ψ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Negation passes through the product. -/
@[simp]
lemma op_mul_neg_ket {n : Type*} [Fintype n] (A : Op n) (ψ : Ket n) : A * (-ψ) = -(A * ψ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Negation passes through the product. -/
@[simp]
lemma neg_ket_mul_bra {n : Type*} (ψ : Ket n) (β : Bra n) : (-ψ) * β = -(ψ * β) := by
  ext i j
  simp

/-- Negation passes through the product. -/
@[simp]
lemma ket_mul_neg_bra {n : Type*} (ψ : Ket n) (β : Bra n) : ψ * (-β) = -(ψ * β) := by
  ext i j
  simp

/-- Negation passes through the product. -/
@[simp]
lemma neg_bra_mul_ket {n : Type*} [Fintype n] (β : Bra n) (ψ : Ket n) : (-β) * ψ = -(β * ψ) := by
  simp [bra_mul_ket_eq]

/-- Negation passes through the product. -/
@[simp]
lemma bra_mul_neg_ket {n : Type*} [Fintype n] (β : Bra n) (ψ : Ket n) : β * (-ψ) = -(β * ψ) := by
  simp [bra_mul_ket_eq]

/-- Physics: |ψ⟩⟨φ| acting on |χ⟩ gives ⟨φ|χ⟩·|ψ⟩ -/
theorem ketbra_mul_ket {n : Type*} [Fintype n] (ψ χ : Ket n) (φ : Bra n) :
    (ψ * φ) * χ = (φ * χ) • ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul,
             bra_mul_ket_eq, ket_mul_bra_apply, Matrix.mulVec, dotProduct]
  trans (ψ.vec i * ∑ x, φ.vec x * χ.vec x)
  · rw [Finset.mul_sum]; congr 1; funext x; ring
  · ring

/-- Physics: Addition of operators distributes over ket multiplication -/
theorem add_op_mul_ket {n : Type*} [Fintype n] (A B : Op n) (ψ : Ket n) :
    (A + B) * ψ = A * ψ + B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.add_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Physics: Subtraction of operators distributes over ket multiplication -/
theorem sub_op_mul_ket {n : Type*} [Fintype n] (A B : Op n) (ψ : Ket n) :
    (A - B) * ψ = A * ψ - B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.sub_vec, Matrix.sub_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring

/-- Physics: A(|ψ⟩ + |φ⟩) = A|ψ⟩ + A|φ⟩ (right linearity of operator action) -/
theorem op_mul_add_ket {n : Type*} [Fintype n] (A : Op n) (ψ φ : Ket n) :
    A * (ψ + φ) = A * ψ + A * φ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Expand ψ.dag.vec -/
@[simp] lemma Ket.dag_vec {n : Type*} (ψ : Ket n) (i : n) :
    ψ.dag.vec i = conj (ψ.vec i) := rfl

/-- Expand φ.dag.vec -/
@[simp] lemma Bra.dag_vec {n : Type*} (φ : Bra n) (i : n) :
    φ.dag.vec i = conj (φ.vec i) := rfl

/-- Physics: (c|ψ⟩)† = c*⟨ψ| (conjugate-linearity of dagger) -/
@[simp]
theorem Ket.dag_smul {n : Type*} (c : ℂ) (ψ : Ket n) : (c • ψ).dag = star c • ψ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.smul_vec, Pi.smul_apply, Bra.smul_vec, starRingEnd_apply,
             smul_eq_mul, star_mul']

/-- Physics: (|ψ⟩ + |φ⟩)† = ⟨ψ| + ⟨φ| (linearity of dagger for addition) -/
@[simp]
theorem Ket.dag_add {n : Type*} (ψ φ : Ket n) : (ψ + φ).dag = ψ.dag + φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.add_vec, map_add, Bra.add_vec]

/-- Physics: (|ψ⟩ - |φ⟩)† = ⟨ψ| - ⟨φ| (linearity of dagger for subtraction) -/
@[simp]
theorem Ket.dag_sub {n : Type*} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.sub_vec, Bra.sub_vec, map_sub]

/-- Dagger preserves zero. -/
@[simp]
lemma Ket.dag_zero {n : Type*} : (0 : Ket n).dag = 0 := by
  ext i
  simp

/-- Dagger commutes with negation. -/
@[simp]
lemma Ket.dag_neg {n : Type*} (ψ : Ket n) : (-ψ).dag = -ψ.dag := by
  ext i
  simp

/-- Dagger preserves addition of bras. -/
@[simp]
lemma Bra.dag_add {n : Type*} (β γ : Bra n) : (β + γ).dag = β.dag + γ.dag := by
  ext i
  simp only [Bra.dag_vec, Bra.add_vec, Ket.add_vec, map_add]

/-- Dagger preserves subtraction of bras. -/
@[simp]
lemma Bra.dag_sub {n : Type*} (β γ : Bra n) : (β - γ).dag = β.dag - γ.dag := by
  ext i
  simp only [Bra.dag_vec, Bra.sub_vec, Ket.sub_vec, map_sub]

/-- Dagger preserves zero. -/
@[simp]
lemma Bra.dag_zero {n : Type*} : (0 : Bra n).dag = 0 := by
  ext i
  simp

/-- Dagger commutes with negation. -/
@[simp]
lemma Bra.dag_neg {n : Type*} (β : Bra n) : (-β).dag = -β.dag := by
  ext i
  simp

/-- Dagger conjugates a bra scalar factor. -/
@[simp]
lemma Bra.dag_smul {n : Type*} (c : ℂ) (β : Bra n) : (c • β).dag = star c • β.dag := by
  ext i
  simp

end Quantum.Operators
