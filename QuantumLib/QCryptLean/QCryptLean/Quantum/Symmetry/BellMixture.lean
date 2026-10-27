import Mathlib.Data.Sym.Card
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellReference

/-! # Bell Mixture -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

/-- The Bell basis, with the classical order `(phase, bit) = 00, 01, 10, 11`. -/
def bellLabelKet : Fin 4 → Ket (Bool × Bool) :=
  ![bellKet false false, bellKet false true, bellKet true false, bellKet true true]

/-- The rectangular change from Boolean-pair coordinates to Bell labels. -/
def bellSinglePairRotation : Matrix (Fin 4) (Bool × Bool) ℂ :=
  fun i j => star ((bellLabelKet i).vec j)

/-- The Bell rotation is real entrywise. -/
theorem bellSinglePairRotation_star (i : Fin 4) (j : Bool × Bool) :
    star (bellSinglePairRotation i j) = bellSinglePairRotation i j := by
  obtain ⟨a, b⟩ := j
  fin_cases i <;> cases a <;> cases b <;>
    norm_num [bellSinglePairRotation, bellLabelKet, bellKet, Complex.star_def]

/-- The Bell rows form an orthonormal family. -/
theorem bellSinglePairRotation_mul_conjTranspose :
    bellSinglePairRotation * bellSinglePairRotationᴴ = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      bellSinglePairRotation, bellLabelKet, bellKet, conjTranspose_apply, one_apply,
      Complex.star_def, mul_add, add_mul] <;> field_simp <;> linear_combination -hs

/-- The Bell columns form an orthonormal family. -/
theorem bellSinglePairRotation_conjTranspose_mul :
    bellSinglePairRotationᴴ * bellSinglePairRotation = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, bellSinglePairRotation, bellLabelKet,
      bellKet, conjTranspose_apply, one_apply, Complex.star_def, mul_add, add_mul] <;>
    field_simp <;> linear_combination -hs

/-- The Bell kets are orthonormal, expressed through their rectangular rotation. -/
theorem bellLabelKet_orthonormal (i j : Fin 4) :
    ((bellLabelKet i).dag * bellLabelKet j : ℂ) = if i = j then 1 else 0 := by
  change (∑ x, star ((bellLabelKet i).vec x) * (bellLabelKet j).vec x) = _
  have h := congrFun (congrFun bellSinglePairRotation_mul_conjTranspose i) j
  simpa only [Matrix.mul_apply, bellSinglePairRotation, conjTranspose_apply, star_star,
    Matrix.one_apply] using h

/-- The Bell projectors resolve the identity on the Boolean pair register. -/
theorem bellLabelKet_projectors_sum : (∑ i, (bellLabelKet i).projector) = 1 := by
  ext x y
  change (∑ i, (bellLabelKet i).vec x * star ((bellLabelKet i).vec y)) = _
  have h := congrFun (congrFun bellSinglePairRotation_conjTranspose_mul x) y
  simpa only [Matrix.mul_apply, bellSinglePairRotation, conjTranspose_apply, star_star,
    Matrix.sum_apply] using h

/-- Every Bell label defines a normalized ket on a Boolean pair. -/
def bellNormKet (i : Fin 4) : NormKet (Bool × Bool) where
  toKet := bellLabelKet i
  normalized := by simpa only [Ket.IsNormalized, ite_true] using bellLabelKet_orthonormal i i

/-- The density operator of the Bell ket with the given classical label. -/
def bellDensity (i : Fin 4) : DensityOp (Bool × Bool) := (bellNormKet i).toDensityOp

/-- Each Bell density operator is pure. -/
theorem isPure_bellDensity (i : Fin 4) : (bellDensity i).IsPure :=
  (bellNormKet i).isPure_toDensityOp

/-- The Bell rotation on a function register is a pointwise tensor family. -/
def bellRotation (k : ℕ) : Matrix (Fin k → Fin 4) (Fin k → Bool × Bool) ℂ :=
  piTensorProduct (fun _ => bellSinglePairRotation)

/-- Repeated Bell rotations are real entrywise, including the empty tensor. -/
theorem bellRotation_star (k : ℕ) (i : Fin k → Fin 4) (j : Fin k → Bool × Bool) :
    star (bellRotation k i j) = bellRotation k i j := by
  simp only [bellRotation, piTensorProduct, Matrix.of_apply, star_prod]
  exact Finset.prod_congr rfl fun t _ => bellSinglePairRotation_star (i t) (j t)

/-- Repeated Bell rows remain orthonormal, including at zero sites. -/
theorem bellRotation_mul_conjTranspose (k : ℕ) :
    bellRotation k * (bellRotation k)ᴴ = 1 := by
  rw [bellRotation, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [bellSinglePairRotation_mul_conjTranspose, piTensorProduct_one]

/-- Repeated Bell columns remain orthonormal. -/
theorem bellRotation_unitary (k : ℕ) : (bellRotation k)ᴴ * bellRotation k = 1 := by
  rw [bellRotation, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [bellSinglePairRotation_conjTranspose_mul, piTensorProduct_one]

/-- The occupation type of a word of Bell labels. -/
def bellTypeOfIndex {k : ℕ} (i : Fin k → Fin 4) : Sym (Fin 4) k :=
  ⟨Finset.univ.val.map i, by simp⟩

/-- The diagonal projector onto words with a specified Bell occupation type. -/
def bellTypeDiagProjector (k : ℕ) (T : Sym (Fin 4) k) : Op (Fin k → Fin 4) :=
  Matrix.diagonal (fun i => if bellTypeOfIndex i = T then (1 : ℂ) else 0)
/-- The computational-basis Bell-type projector is Hermitian (real diagonal). -/
theorem isHermitian_bellTypeDiagProjector (n : ℕ) (T : Sym (Fin 4) n) :
    (bellTypeDiagProjector n T).IsHermitian := by
  unfold Matrix.IsHermitian bellTypeDiagProjector
  rw [Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal ?_
  funext i
  simp only [Pi.star_apply, apply_ite (Star.star : ℂ → ℂ), star_one, star_zero]

/-- The computational-basis Bell-type projector is idempotent (`0/1` diagonal). -/
theorem bellTypeDiagProjector_mul_self (n : ℕ) (T : Sym (Fin 4) n) :
    bellTypeDiagProjector n T * bellTypeDiagProjector n T = bellTypeDiagProjector n T := by
  unfold bellTypeDiagProjector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

/-- The computational-basis Bell-type projectors resolve the identity: `∑_T P_T = 𝟙` (every joint
index has exactly one Bell type). -/
theorem bellTypeDiagProjector_sum (n : ℕ) :
    ∑ T : Sym (Fin 4) n, bellTypeDiagProjector n T = 1 := by
  ext i j
  simp only [Matrix.sum_apply, bellTypeDiagProjector, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [Finset.sum_ite_eq Finset.univ (bellTypeOfIndex i) (fun _ => (1 : ℂ))]
    simp
  · simp [hij]

/-- **The joint-Bell-basis Bell-type sector projector** `Q_T = V^{⊗n}†·P_T·V^{⊗n}`: the orthogonal
projector onto the joint Bell strings of type `T`, obtained by conjugating the computational-basis
type indicator `P_T` back through the Bell rotation `V^{⊗n} = bellRotation n`. -/
def bellTypeProjector (n : ℕ) (T : Sym (Fin 4) n) : Op (Fin n → Bool × Bool) :=
  (bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n

/-- The Bell-type sector projector is Hermitian. -/
theorem isHermitian_bellTypeProjector (n : ℕ) (T : Sym (Fin 4) n) :
    (bellTypeProjector n T).IsHermitian := by
  have hP := isHermitian_bellTypeDiagProjector n T
  unfold Matrix.IsHermitian bellTypeProjector
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

/-- The Bell-type sector projector is idempotent (uses `V^{⊗n}·V^{⊗n}† = 1` and `P_T² = P_T`). -/
theorem bellTypeProjector_mul_self (n : ℕ) (T : Sym (Fin 4) n) :
    bellTypeProjector n T * bellTypeProjector n T = bellTypeProjector n T := by
  unfold bellTypeProjector
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bellRotation n), bellRotation_mul_conjTranspose, Matrix.one_mul,
    ← Matrix.mul_assoc (bellTypeDiagProjector n T), bellTypeDiagProjector_mul_self]

/-- The Bell-type sector projectors resolve the identity: `∑_T Q_T = 𝟙` (uses `∑_T P_T = 𝟙` and
`V^{⊗n}†·V^{⊗n} = 1`). -/
theorem bellTypeProjector_sum (n : ℕ) :
    ∑ T : Sym (Fin 4) n, bellTypeProjector n T = 1 := by
  unfold bellTypeProjector
  simp_rw [Matrix.mul_assoc]
  rw [← Matrix.mul_sum, ← Matrix.sum_mul, bellTypeDiagProjector_sum, Matrix.one_mul,
    bellRotation_unitary]


/-- The Bell type-coherent Kraus matrix. -/
def bellPairedKraus (k : ℕ) (T : Sym (Fin 4) k) : Op (Fin k → Bool × Bool) :=
  CFC.sqrt (bellDeFinettiDensity k).toOp * bellTypeProjector k T

/-- The Kraus left Gram matrices sum to the Bell reference. -/
theorem bellPairedKraus_mul_conjTranspose_sum (k : ℕ) :
    ∑ T, bellPairedKraus k T * (bellPairedKraus k T)ᴴ = (bellDeFinettiDensity k).toOp := by
  let A := (bellDeFinettiDensity k).toOp
  have hA := (bellDeFinettiDensity k).posSemidef
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have ht (T : Sym (Fin 4) k) : bellPairedKraus k T * (bellPairedKraus k T)ᴴ =
      CFC.sqrt A * bellTypeProjector k T * CFC.sqrt A := by
    change (CFC.sqrt A * _) * (CFC.sqrt A * _)ᴴ = _
    rw [conjTranspose_mul, isHermitian_bellTypeProjector, hs]
    calc _ = CFC.sqrt A * (bellTypeProjector k T * bellTypeProjector k T) * CFC.sqrt A := by
           noncomm_ring
         _ = _ := by rw [bellTypeProjector_mul_self]
  simp_rw [ht]
  rw [← Finset.sum_mul, ← Finset.mul_sum, bellTypeProjector_sum, Matrix.mul_one]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- The type-coherent joint Bell mixture is a sum of vectorized Kraus projectors. -/
def bellPairedDeFinettiStateOp (k : ℕ) :
    Op ((Fin k → Bool × Bool) × (Fin k → Bool × Bool)) :=
  ∑ T, (Ket.vectorize (bellPairedKraus k T)).projector

/-- The type mixture is positive as a finite sum of rank-one projectors. -/
theorem posSemidef_bellPairedDeFinettiStateOp (k : ℕ) :
    (bellPairedDeFinettiStateOp k).PosSemidef := by
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun _ _ => Ket.posSemidef_projector _)

/-- Discarding the joint mixture's reference gives the Bell de Finetti state. -/
theorem bellPairedDeFinettiStateOp_partialTraceRight (k : ℕ) :
    partialTraceRight (bellPairedDeFinettiStateOp k) = (bellDeFinettiDensity k).toOp := by
  simp only [bellPairedDeFinettiStateOp, partialTraceRight_sum,
    Ket.partialTraceRight_vectorize, bellPairedKraus_mul_conjTranspose_sum]

/-- The joint mixture has trace one. -/
theorem bellPairedDeFinettiStateOp_trace (k : ℕ) :
    (bellPairedDeFinettiStateOp k).trace = 1 := by
  rw [← trace_partialTraceRight, bellPairedDeFinettiStateOp_partialTraceRight]
  exact (bellDeFinettiDensity k).trace_one

/-- The bundled type-coherent Bell mixture. -/
def bellPairedDeFinettiState (k : ℕ) :
    DensityOp ((Fin k → Bool × Bool) × (Fin k → Bool × Bool)) where
  toOp := bellPairedDeFinettiStateOp k
  posSemidef := posSemidef_bellPairedDeFinettiStateOp k
  trace_one := bellPairedDeFinettiStateOp_trace k

/-- The bundled joint mixture has the required Bell marginal. -/
theorem bellPairedDeFinettiState_partialTraceRight (k : ℕ) :
    (bellPairedDeFinettiState k).partialTraceRight = bellDeFinettiDensity k := by
  apply DensityOp.ext
  exact bellPairedDeFinettiStateOp_partialTraceRight k

/-- The joint mixture has at most one independent vector per Bell occupation type. -/
theorem rank_bellPairedDeFinettiState_le (k : ℕ) :
    (bellPairedDeFinettiState k).toOp.rank ≤ (k + 3).choose 3 := by
  let C : Matrix ((Fin k → Bool × Bool) × (Fin k → Bool × Bool)) (Sym (Fin 4) k) ℂ :=
    fun i T => (bellPairedKraus k T) i.1 i.2
  have hC : (bellPairedDeFinettiState k).toOp = C * Cᴴ := by
    ext i j
    change (∑ T, (Ket.vectorize (bellPairedKraus k T)).projector) i j = _
    rw [Matrix.sum_apply, Matrix.mul_apply]
    rfl
  rw [hC]
  calc (C * Cᴴ).rank ≤ C.rank := Matrix.rank_mul_le_left C Cᴴ
       _ ≤ Fintype.card (Sym (Fin 4) k) := Matrix.rank_le_card_width C
       _ = (k + 3).choose 3 := by
         rw [Sym.card_sym_eq_choose, Fintype.card_fin,
           show 4 + k - 1 = k + 3 from by omega]
         have h := Nat.choose_symm (by omega : 3 ≤ k + 3)
         simpa using h

end Quantum.Symmetry
