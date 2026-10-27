import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor

/-! # Finite Group -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped Kronecker

/-- A unitary representation, given by a multiplicative family of unitary operators. -/
def IsUnitaryRep {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X]
    (π : G → Op X) : Prop :=
  (∀ g h : G, π (g * h) = π g * π h) ∧ ∀ g : G, (π g)ᴴ * π g = 1

/-- The scalar-commutant form of irreducibility: every operator in the commutant is scalar. -/
def IsIrreducibleRep {G : Type*} {X : Type*} [Fintype X] [DecidableEq X]
    (π : G → Op X) : Prop :=
  ∀ T : Op X, (∀ g : G, π g * T = T * π g) → ∃ c : ℂ, T = c • (1 : Op X)

/-- Entrywise complex conjugation of an operator. -/
def entryConj {X : Type*} (M : Op X) : Op X :=
  Matrix.of fun i j => star (M i j)

/-- The uniform average of `π₁(g) ⊗ conj(π₂(g))`. For unitary representations
this is the orthogonal projection onto the invariant vectors of the paired action. -/
def groupTwirlProjectorPair {G : Type*} [Fintype G] {X Y : Type*} (π₁ : G → Op X)
    (π₂ : G → Op Y) : Op (X × Y) :=
  ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))

/-- The paired twirl of a representation with itself. Its range corresponds to
the commutant of the representation under vectorization. -/
def groupTwirlProjector {G : Type*} [Fintype G] {X : Type*} (π : G → Op X) :
    Op (X × X) :=
  groupTwirlProjectorPair π π


/-- `entryConj` preserves multiplication: entrywise conjugation is applied to each entry of a
matrix product, and conjugation on ℂ is a ring homomorphism (`star_sum`, `star_mul'`). -/
lemma entryConj_mul {X : Type*} [Fintype X] (A B : Op X) :
    entryConj (A * B) = entryConj A * entryConj B := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.mul_apply, star_sum, star_mul']

/-- `entryConj` commutes with the conjugate transpose: the two conjugations commute
(entrywise conjugation vs. conjugate-transposition). -/
lemma entryConj_conjTranspose {X : Type*} (A : Op X) :
    (entryConj A)ᴴ = entryConj Aᴴ := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.conjTranspose_apply, star_star]

/-- `entryConj` fixes the identity matrix. -/
lemma entryConj_one {X : Type*} [DecidableEq X] : entryConj (1 : Op X) = 1 := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.one_apply]
  split <;> simp

/-- Entrywise conjugation distributes over the Kronecker product: `conj(A ⊗ B) = conj(A) ⊗
conj(B)` (entries: `star (A i j * B k l) = star (A i j) * star (B k l)`, `star_mul'`). -/
lemma entryConj_kronecker {X Y : Type*} (A : Op X) (B : Op Y) :
    entryConj (Matrix.kronecker A B) = Matrix.kronecker (entryConj A) (entryConj B) := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, star_mul']

/-- Transposing the entrywise conjugate gives the conjugate transpose:
    `(conj M)ᵀ = Mᴴ` (both have entries `conj(M j i)`). -/
lemma entryConj_transpose {X : Type*} (M : Op X) : (entryConj M).transpose = Mᴴ := by
  ext i j
  simp [entryConj, Matrix.conjTranspose_apply]

/-- A unitary representation sends the group identity to the identity operator: `π 1` is
idempotent (`π (1 · 1) = π 1 · π 1`) and unitary, and a unitary idempotent is `1`. -/
lemma IsUnitaryRep.one {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X]
    {π : G → Op X} (hπ : IsUnitaryRep π) :
    π 1 = 1 := by
  have h1 : π 1 * π 1 = π 1 := by rw [← hπ.1 1 1, one_mul]
  have h2 : (π 1)ᴴ * (π 1 * π 1) = 1 := by rw [h1, hπ.2 1]
  have h3 : (π 1)ᴴ * (π 1 * π 1) = π 1 := by rw [← Matrix.mul_assoc, hπ.2 1, one_mul]
  exact h3.symm.trans h2

/-- In a unitary representation, `π g⁻¹ = (π g)ᴴ`: `π g⁻¹` is the two-sided inverse of `π g`
(since `π g · π g⁻¹ = π 1 = 1`), and `(π g)ᴴ` is a left inverse by unitarity. -/
lemma IsUnitaryRep.inv {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X]
    {π : G → Op X} (hπ : IsUnitaryRep π)
    (g : G) : π g⁻¹ = (π g)ᴴ := by
  have h1 : (π g)ᴴ * (π g * π g⁻¹) = (π g)ᴴ := by
    rw [← hπ.1 g g⁻¹, mul_inv_cancel, IsUnitaryRep.one hπ, mul_one]
  rw [← Matrix.mul_assoc, hπ.2 g, one_mul] at h1
  exact h1

/-- The paired twirl of two unitary representations is the orthogonal
projection onto the invariant subspace of their paired action. -/
theorem groupTwirlProjectorPair_conjTranspose_and_mul_self {G : Type*} [Group G] [Fintype G]
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (π₁ : G → Op X) (π₂ : G → Op Y) (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂) :
    (groupTwirlProjectorPair π₁ π₂)ᴴ = groupTwirlProjectorPair π₁ π₂ ∧
      groupTwirlProjectorPair π₁ π₂ * groupTwirlProjectorPair π₁ π₂ =
        groupTwirlProjectorPair π₁ π₂ := by
  have hc0 : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Product and adjoint of the twirl summands
  have key_mul : ∀ g h : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)) *
      Matrix.kronecker (π₁ h) (entryConj (π₂ h)) =
      Matrix.kronecker (π₁ (g * h)) (entryConj (π₂ (g * h))) := by
    intro g h
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← hπ₁.1 g h, ← entryConj_mul, ← hπ₂.1 g h]
  have key_inv : ∀ g : G, (Matrix.kronecker (π₁ g) (entryConj (π₂ g)))ᴴ =
      Matrix.kronecker (π₁ g⁻¹) (entryConj (π₂ g⁻¹)) := by
    intro g
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, entryConj_conjTranspose, IsUnitaryRep.inv hπ₁ g,
      IsUnitaryRep.inv hπ₂ g]
  -- Left-multiplication invariance of the sum (reindex `g ↦ h · g`)
  have key_sum : ∀ h : G, ∑ g : G, (Matrix.kronecker (π₁ h) (entryConj (π₂ h)) *
      Matrix.kronecker (π₁ g) (entryConj (π₂ g))) =
      ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)) := fun h =>
    Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => key_mul h g
  have hSadj : (∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)))ᴴ
      = ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)) := by
    rw [Matrix.conjTranspose_sum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => key_inv g
  -- Right-multiplication invariance of the sum (reindex `g ↦ g · h`)
  have key_sumR : ∀ h : G, ∑ g : G, Matrix.kronecker (π₁ (g * h)) (entryConj (π₂ (g * h)))
      = ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)) := fun h =>
    Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl
  -- The sum squares to `|G| • Σ` (each factor appears `|G|` times)
  have hSS : (∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))) *
      (∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)))
      = ((Fintype.card G : ℕ) : ℂ) • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, key_mul, key_sumR, Finset.sum_const,
      Nat.cast_smul_eq_nsmul ℂ, Finset.card_univ]
  constructor
  · -- Πᴴ = Π: conjugation fixes the positive scalar and reverses the sum to itself
    change (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)))ᴴ
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))
    rw [conjTranspose_smul, hSadj, star_inv₀, star_natCast]
  · -- Π · Π = Π: average the invariance `T h · S = S` over `h`
    change (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))) *
      (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g)))
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))
    rw [smul_mul_assoc, mul_smul_comm, hSS,
      smul_smul (((Fintype.card G : ℕ) : ℂ)⁻¹) (((Fintype.card G : ℕ) : ℂ)⁻¹)
        (((Fintype.card G : ℕ) : ℂ) • ∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))),
      smul_smul (((Fintype.card G : ℕ) : ℂ)⁻¹ * ((Fintype.card G : ℕ) : ℂ)⁻¹)
        ((Fintype.card G : ℕ) : ℂ) (∑ g : G, Matrix.kronecker (π₁ g) (entryConj (π₂ g))),
      mul_assoc, inv_mul_cancel₀ hc0, mul_one]


end Quantum.Symmetry
