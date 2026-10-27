import Mathlib.Analysis.InnerProductSpace.PiL2
import QCryptLean.InfoTheory.SmoothMinEntropy.Bipartite
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.IsometryConjugation
import QCryptLean.Quantum.Operators.StateOperations

/-! # Measurement -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix
open scoped Kronecker

namespace RankOneProjectiveBasis

variable {A : Type*} [Fintype A]

/-- View a vector of a Mathlib orthonormal basis as a ket. -/
def vec (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x : A) : Ket A := ⟨P x⟩

/-- The rank-one measurement projector associated to an outcome. -/
def proj (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x : A) : Op A :=
  (vec P x).projector

/-- The coherent triple copy of a basis vector. -/
def dilationKet (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x : A) : Ket ((A × A) × A) :=
  ((vec P x).kronecker (vec P x)).kronecker (vec P x)

/-- The rectangular coherent measurement dilation. -/
def dilationIso (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : Matrix ((A × A) × A) A ℂ :=
  fun i j => ∑ x, (dilationKet P x).vec i * star ((vec P x).vec j)

/-- Basis orthonormality in the ket/bras used by the operator layer. -/
theorem inner_vec [DecidableEq A] (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x y : A) :
    ((vec P x).dag * vec P y : ℂ) = if x = y then 1 else 0 := by
  change (∑ i, star ((P x) i) * (P y) i) = _
  simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm]
    using P.inner_eq_ite x y

/-- The basis projectors resolve the identity. -/
theorem sum_proj [DecidableEq A] (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    ∑ x, proj P x = 1 := by
  ext i j
  rw [Matrix.sum_apply, Matrix.one_apply]
  change (∑ x, (P x) i * star ((P x) j)) = if i = j then 1 else 0
  have h := P.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    PiLp.single_apply, map_one, one_mul, starRingEnd_apply, apply_ite star, star_one, star_zero,
    eq_comm] using h.symm

/-- Triple copies remain orthonormal. -/
theorem dilationKet_inner [DecidableEq A]
    (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (x y : A) :
    ((dilationKet P x).dag * dilationKet P y : ℂ) = if x = y then 1 else 0 := by
  have h := inner_vec P x y
  change (∑ i, star ((vec P x).vec i) * (vec P y).vec i) = _ at h
  change (∑ p : (A × A) × A,
    star (((vec P x).vec p.1.1 * (vec P x).vec p.1.2) * (vec P x).vec p.2) *
      (((vec P y).vec p.1.1 * (vec P y).vec p.1.2) * (vec P y).vec p.2)) = _
  calc
    _ = (∑ i, star ((vec P x).vec i) * (vec P y).vec i) ^ 3 := by
      simp only [pow_succ, pow_zero, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum, star_mul']
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [h]; split_ifs <;> norm_num

/-- The coherent measurement dilation is an isometry. -/
theorem dilationIso_isometry [DecidableEq A]
    (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) :
    (dilationIso P)ᴴ * dilationIso P = 1 := by
  ext c c'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dilationIso, star_sum,
    star_mul', star_star, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  have hinner (i j : A) :
      (∑ x, star ((dilationKet P i).vec x) * (vec P i).vec c *
        ((dilationKet P j).vec x * star ((vec P j).vec c'))) =
      ((vec P i).vec c * star ((vec P j).vec c')) * (if i = j then 1 else 0) := by
    rw [← dilationKet_inner P i j]
    change _ = _ * ∑ x, star ((dilationKet P i).vec x) * (dilationKet P j).vec x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hinner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h := congrFun (congrFun (sum_proj P) c) c'
  rw [Matrix.sum_apply] at h
  change (∑ x, (vec P x).vec c * star ((vec P x).vec c')) = (1 : Op A) c c' at h
  exact h

/-- The largest squared overlap of two finite nonempty bases. -/
def overlapConst [Nonempty A] (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun p : A × A => Complex.normSq ((vec P p.1).dag * vec Q p.2 : ℂ))

/-- Preparation quality in bits. -/
def preparationQuality [Nonempty A]
    (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : ℝ :=
  -Real.log (overlapConst P Q) / Real.log 2

/-- The partial isometry between the two coherent measurement ranges. -/
def partialIsometryW (P Q : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) : Op ((A × A) × A) :=
  dilationIso P * (dilationIso Q)ᴴ

end RankOneProjectiveBasis

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Coherently measure the first register, carrying the second register along. -/
def measDilate (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (ρ : SubDensityOp (A × B)) :
    SubDensityOp (((A × A) × A) × B) :=
  ρ.isometryConjugate (RankOneProjectiveBasis.dilationIso P ⊗ₖ (1 : Op B)) (by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      RankOneProjectiveBasis.dilationIso_isometry, Matrix.one_mul, Matrix.one_kronecker_one])

/-- The register permutation exposing the two registers to discard. -/
def measTraceEquiv : (((A × A) × A) × B) ≃ ((A × B) × (A × A)) where
  toFun p := ((p.1.1.1, p.2), (p.1.1.2, p.1.2))
  invFun p := (((p.1.1, p.2.1), p.2.2), p.1.2)

/-- Put the measured register first in the conditional entropy layout. -/
def measEntropyEquiv : (((A × A) × A) × B) ≃ (A × ((A × A) × B)) where
  toFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  invFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)

/-- The measured marginal, discarding the two extra coherent registers. -/
def xMeasuredMarginal (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ : SubDensityOp (A × B)) : SubDensityOp (A × B) :=
  ((measDilate P ρ).reindex measTraceEquiv).partialTraceRight

/-- The coherent state in the system-first conditional entropy layout. -/
def zDilatedState (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ : SubDensityOp (A × B)) : SubDensityOp (A × ((A × A) × B)) :=
  (measDilate P ρ).reindex measEntropyEquiv

/-- Coherent measurement preserves total weight. -/
theorem measDilate_trace (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ : SubDensityOp (A × B)) : (measDilate P ρ).trace = ρ.trace :=
  SubDensityOp.trace_isometryConjugate _ _ _

/-- The conditional entropy layout preserves total weight. -/
theorem zDilatedState_trace (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ : SubDensityOp (A × B)) : (zDilatedState P ρ).trace = ρ.trace := by
  change (Matrix.reindex _ _ (measDilate P ρ).toOp).trace.re = _
  rw [Matrix.reindex_trace]
  exact measDilate_trace P ρ

/-- The measured marginal preserves total weight. -/
theorem xMeasuredMarginal_trace (P : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (ρ : SubDensityOp (A × B)) : (xMeasuredMarginal P ρ).trace = ρ.trace := by
  change (Matrix.partialTraceRight (Matrix.reindex _ _ (measDilate P ρ).toOp)).trace.re = _
  rw [Matrix.trace_partialTraceRight, Matrix.reindex_trace]
  exact measDilate_trace P ρ

end InfoTheory.SmoothMinEntropy
