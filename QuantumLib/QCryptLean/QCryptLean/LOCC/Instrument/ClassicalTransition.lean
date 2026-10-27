import Mathlib.Probability.ProbabilityMassFunction.Constructions
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.ClassicalPreservation
import QCryptLean.LOCC.Instrument.OperationalEquivalence
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-!
# Classical transition kernels of finite instruments

An observed instrument branch is a completely positive map, as in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. On an input that is
classical in the instrument's basis, its diagonal entries define an outcome-retaining stochastic
transition. The CQ predicate below is the finite-matrix form of Renner's `classform` condition
in quant-ph/0512258v2.

The canonical replacement realizes the same transition with basis-to-basis Kraus matrices. Its
agreement with the original instrument is restricted to CQ inputs; no equality on coherent
inputs is asserted.
-/

open Quantum.Channels (
  krausMap
  krausMap_eq_sum_conjLinearMap
  mapTensorId
  mapTensorId_apply)

open scoped Matrix BigOperators ENNReal NNReal
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

/-- An operator is classical on its first finite register, with no restriction on either of the
independently indexed reference coordinates. -/
def IsClassicalOnFirst {Alpha Ref : Type}
    (rho : Op (Alpha × Ref)) : Prop :=
  ∀ x x' e e', x ≠ x' → rho (x, e) (x', e') = 0

/-- Relabelling the classical register of a CQ operator preserves its CQ structure, with the
reference row and column coordinates still independent. -/
theorem IsClassicalOnFirst.reindexOp
    {Alpha Beta Ref : Type}
    {rho : Op (Alpha × Ref)}
    (hrho : IsClassicalOnFirst (Alpha := Alpha) (Ref := Ref) rho)
    (e : Alpha ≃ Beta) :
    IsClassicalOnFirst (Alpha := Beta) (Ref := Ref)
    (mapTensorId ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) Ref rho) := by
  intro b b' r r' hbb'
  rw [mapTensorId_apply]
  exact hrho (e.symm b) (e.symm b') r r' (e.symm.injective.ne hbb')

namespace Instrument

variable {Hin Hout Outcome Ref : Type}
  [Fintype Hin] [DecidableEq Hin]
  [Fintype Hout] [DecidableEq Hout]
  [Fintype Outcome]

/-- The real weight of observed outcome `y` and output basis value `b`, conditional on input
basis value `a`. -/
def classicalWeight (I : Instrument Hin Hout Outcome) (a : Hin)
    (yb : Outcome × Hout) : ℝ :=
  ((I.operation yb.1 (Matrix.single a a 1)) yb.2 yb.2).re

/-- The canonical weight is the hidden-Kraus sum of squared moduli. -/
theorem classicalWeight_eq_sum_normSq (I : Instrument Hin Hout Outcome)
    (a : Hin) (y : Outcome) (b : Hout) :
    I.classicalWeight a (y, b) = ∑ r, Complex.normSq (I.kraus y r b a) := by
  simp only [classicalWeight, Instrument.operation, krausMap_eq_sum_conjLinearMap,
    LinearMap.sum_apply, Matrix.sum_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hterm :
    (Matrix.conjLinearMap (I.kraus y r) (Matrix.single a a 1)) b b =
        I.kraus y r b a * star (I.kraus y r b a) := by
    simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.single_apply]
    · intro x _ hxa
      simp [hxa.symm]
    · simp
  rw [hterm]
  simp [Complex.normSq_apply]

/-- Canonical transition weights are nonnegative. -/
theorem classicalWeight_nonneg (I : Instrument Hin Hout Outcome)
    (a : Hin) (yb : Outcome × Hout) :
    0 ≤ I.classicalWeight a yb := by
  rw [classicalWeight_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Canonical transition weights are normalized jointly over observed outcomes and output basis
values. -/
theorem sum_classicalWeight (I : Instrument Hin Hout Outcome) (a : Hin) :
    ∑ y, ∑ b, I.classicalWeight a (y, b) = 1 := by
  have htrace := I.channel_trace_eq (Matrix.single a a (1 : ℂ))
  have hrhs : (∑ i : Hin, Matrix.single a a (1 : ℂ) i i) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [hba.symm]
    · simp
  rw [hrhs] at htrace
  have hre := congrArg Complex.re htrace
  simp only [Instrument.channel_eq_sum, LinearMap.sum_apply, Matrix.sum_apply, Complex.re_sum,
    Complex.one_re] at hre
  rw [Finset.sum_comm] at hre
  simpa only [classicalWeight] using hre

/-- The `ENNReal` weights used to construct the canonical transition are normalized. -/
theorem sum_ofReal_classicalWeight (I : Instrument Hin Hout Outcome) (a : Hin) :
    ∑ yb : Outcome × Hout, ENNReal.ofReal (I.classicalWeight a yb) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg
    (fun b _ => I.classicalWeight_nonneg a (_, b))]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [I.sum_classicalWeight a]
    norm_num
  · intro y _
    exact Finset.sum_nonneg fun b _ => I.classicalWeight_nonneg a (y, b)

/-- The outcome-retaining stochastic transition implemented by a finite instrument on a basis
input. -/
def classicalTransition (I : Instrument Hin Hout Outcome) (a : Hin) :
    PMF (Outcome × Hout) :=
  PMF.ofFintype
    (fun yb => ENNReal.ofReal (I.classicalWeight a yb))
    (I.sum_ofReal_classicalWeight a)

/-- The canonical transition has exactly the real diagonal-entry weights. -/
theorem classicalTransition_apply_toReal (I : Instrument Hin Hout Outcome)
    (a : Hin) (yb : Outcome × Hout) :
    (I.classicalTransition a yb).toReal = I.classicalWeight a yb := by
  simp [classicalTransition, I.classicalWeight_nonneg a yb]

/-- Outcome-by-outcome diagonal preservation is equivalent to the canonical stochastic formula
on every complex diagonal operator. -/
theorem preservesDiagonalBranches_iff_classicalWeight
    (I : Instrument Hin Hout Outcome) :
    I.PreservesDiagonalBranches ↔
      ∀ y (d : Hin → ℂ) b b',
        I.operation y (Matrix.diagonal d) b b' =
          if b = b' then
            ∑ a, (I.classicalWeight a (y, b) : ℂ) * d a
          else 0 := by
  constructor
  · intro hI y d b b'
    by_cases hbb' : b = b'
    · subst b'
      rw [← Matrix.sum_single_eq_diagonal d]
      simp only [map_sum, Matrix.sum_apply, ite_true]
      apply Finset.sum_congr rfl
      intro a _
      have hsingle :
          Matrix.single a a (d a) =
            d a • Matrix.single a a (1 : ℂ) := by
        ext i j
        simp [Matrix.single_apply]
      rw [hsingle, map_smul, Matrix.smul_apply]
      have hdiag :
          I.operation y (Matrix.single a a 1) b b =
            (I.classicalWeight a (y, b) : ℂ) := by
        rw [classicalWeight_eq_sum_normSq]
        simp only [Instrument.operation, krausMap_eq_sum_conjLinearMap, LinearMap.sum_apply,
          Matrix.sum_apply,
          Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro r _
        have hterm :
    (Matrix.conjLinearMap (I.kraus y r) (Matrix.single a a 1)) b b =
              I.kraus y r b a * star (I.kraus y r b a) := by
          simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.mul_apply, Matrix.conjTranspose_apply]
          rw [Finset.sum_eq_single a]
          · simp [Matrix.single_apply]
          · intro x _ hxa
            simp [hxa.symm]
          · simp
        rw [hterm]
        change _ = ((Complex.normSq _ : ℝ) : ℂ)
        rw [Complex.normSq_eq_conj_mul_self]
        simp [mul_comm]
      rw [hdiag]
      simp [smul_eq_mul, mul_comm]
    · rw [ite_eq_right hbb']
      exact hI y (Matrix.diagonal d)
        (fun a a' haa' => Matrix.diagonal_apply_ne _ haa') b b' hbb'
  · intro h y rho hrho b b' hbb'
    have hrhoDiag : rho = Matrix.diagonal (fun a => rho a a) := by
      ext a a'
      by_cases haa' : a = a'
      · subst a'
        simp
      · rw [Matrix.diagonal_apply_ne _ haa', hrho a a' haa']
    rw [hrhoDiag, h y, ite_eq_right hbb']

/-- A diagonal-preserving observed operation acts on an arbitrary-reference CQ operator by its
canonical stochastic transition, independently in every reference row/column block. -/
theorem PreservesDiagonalBranches.operation_tensorId_apply
    (I : Instrument Hin Hout Outcome) (hI : I.PreservesDiagonalBranches)
    (rho : Op (Hin × Ref))
    (hrho : IsClassicalOnFirst (Alpha := Hin) (Ref := Ref) rho)
    (y : Outcome) (b b' : Hout) (e e' : Ref) :
    mapTensorId (I.operation y) Ref rho (b, e) (b', e') =
      if b = b' then
        ∑ a, (I.classicalWeight a (y, b) : ℂ) * rho (a, e) (a, e')
      else 0 := by
  rw [mapTensorId_apply]
  have hblock :
      rho.submatrix (fun a => (a, e)) (fun a => (a, e')) =
        Matrix.diagonal (fun a => rho (a, e) (a, e')) := by
    ext a a'
    by_cases haa' : a = a'
    · subst a'
      simp
    · rw [Matrix.diagonal_apply_ne _ haa']
      exact hrho a a' e e' haa'
  rw [hblock]
  exact (I.preservesDiagonalBranches_iff_classicalWeight.mp hI) y
    (fun a => rho (a, e) (a, e')) b b'

/-- Every observed operation of a diagonal-preserving instrument preserves CQ structure against
an arbitrary finite reference. -/
theorem PreservesDiagonalBranches.operation_tensorId_isClassicalOnFirst
    (I : Instrument Hin Hout Outcome) (hI : I.PreservesDiagonalBranches)
    (rho : Op (Hin × Ref))
    (hrho : IsClassicalOnFirst (Alpha := Hin) (Ref := Ref) rho) (y : Outcome) :
    IsClassicalOnFirst (Alpha := Hout) (Ref := Ref)
    (mapTensorId (I.operation y) Ref rho) := by
  intro b b' e e' hne
  rw [hI.operation_tensorId_apply I rho hrho y b b' e e', ite_eq_right hne]

/-- Outcome-level diagonal preservation is invariant under operational equivalence. -/
theorem OperationallyEquivalent.preservesDiagonalBranches_iff
    {I J : Instrument Hin Hout Outcome} (hIJ : I.OperationallyEquivalent J) :
    I.PreservesDiagonalBranches ↔ J.PreservesDiagonalBranches := by
  constructor
  · intro hI y rho hrho b b' hne
    rw [← hIJ y]
    exact hI y rho hrho b b' hne
  · intro hJ y rho hrho b b' hne
    rw [hIJ y]
    exact hJ y rho hrho b b' hne

/-- The canonical stochastic transition is invariant under operational equivalence. -/
theorem OperationallyEquivalent.classicalTransition_eq
    {I J : Instrument Hin Hout Outcome} (hIJ : I.OperationallyEquivalent J) (a : Hin) :
    I.classicalTransition a = J.classicalTransition a := by
  ext yb
  simp [classicalTransition, classicalWeight, hIJ yb.1]

/-- Every hidden Kraus matrix has basis-to-basis columns. This is a representation-level
certificate for a manifest classical realization, not the representation-independent semantic
notion of diagonal preservation. -/
def HasClassicalKraus (I : Instrument Hin Hout Outcome) : Prop :=
  ∀ y r a, ∃ b c, ∀ b', I.kraus y r b' a = if b' = b then c else 0

/-- One basis-to-basis Kraus matrix of the canonical replacement. -/
def classicalReplacementKraus (I : Instrument Hin Hout Outcome)
    (y : Outcome) (ab : Hin × Hout) : Matrix Hout Hin ℂ :=
  Matrix.single ab.2 ab.1
    ((Real.sqrt (I.classicalWeight ab.1 (y, ab.2)) : ℝ) : ℂ)

/-- The canonical replacement Kraus family is complete. -/
theorem classicalReplacementKraus_complete (I : Instrument Hin Hout Outcome) :
    ∑ y, ∑ ab : Hin × Hout,
      (I.classicalReplacementKraus y ab)ᴴ * I.classicalReplacementKraus y ab = 1 := by
  simp only [classicalReplacementKraus]
  simp only [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  simp_rw [Fintype.sum_prod_type]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [RCLike.star_def, Complex.conj_ofReal, one_apply_eq]
    simp_rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (I.classicalWeight_nonneg _ _)]
    convert congrArg (fun x : ℝ => (x : ℂ))
      (I.sum_classicalWeight i) using 1
    · simp [Matrix.sum_apply, Matrix.single_apply]
  · simp only [Matrix.sum_apply, Matrix.one_apply, hij, ite_false]
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.single_apply_of_ne]
    intro h
    exact hij (h.1.symm.trans h.2)

/-- A canonical basis-to-basis Kraus realization of the stochastic transition of `I`. It has
the same observed outcomes, while its hidden fibre records an input/output basis pair. -/
def classicalReplacement (I : Instrument Hin Hout Outcome) :
    Instrument Hin Hout Outcome where
  krausIndex _ := Hin × Hout
  kraus := I.classicalReplacementKraus
  complete := I.classicalReplacementKraus_complete

/-- The canonical replacement has manifestly classical hidden Kraus matrices. -/
theorem classicalReplacement_hasClassicalKraus (I : Instrument Hin Hout Outcome) :
    I.classicalReplacement.HasClassicalKraus := by
  intro y ab a
  refine ⟨ab.2, I.classicalReplacement.kraus y ab ab.2 a, ?_⟩
  intro b'
  by_cases h : b' = ab.2
  · subst b'
    simp
  · have h' : ab.2 ≠ b' := fun hb => h hb.symm
    simp [classicalReplacement, classicalReplacementKraus, h, h']

/-- Every observed branch of the canonical replacement preserves diagonality. -/
theorem classicalReplacement_preservesDiagonalBranches (I : Instrument Hin Hout Outcome) :
    I.classicalReplacement.PreservesDiagonalBranches := by
  intro y rho _ b b' hne
  simp only [Instrument.operation, krausMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp only [classicalReplacement, classicalReplacementKraus, Matrix.conjTranspose_single,
    RCLike.star_def,
    Complex.conj_ofReal, Matrix.single_mul_mul_single]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro ab _
  rw [Matrix.single_apply_of_ne]
  intro h
  exact hne (h.1.symm.trans h.2)

/-- If `I` preserves diagonality outcome by outcome, its canonical classical replacement has the
same observed operations on every diagonal input. -/
theorem PreservesDiagonalBranches.classicalReplacement_operation_diagonal
    (I : Instrument Hin Hout Outcome) (hI : I.PreservesDiagonalBranches)
    (y : Outcome) (d : Hin → ℂ) :
    I.classicalReplacement.operation y (Matrix.diagonal d) =
      I.operation y (Matrix.diagonal d) := by
  have hweight (a : Hin) (b : Hout) :
      I.classicalReplacement.classicalWeight a (y, b) =
        I.classicalWeight a (y, b) := by
    rw [classicalWeight_eq_sum_normSq]
    change (∑ ab : Hin × Hout, Complex.normSq (I.classicalReplacementKraus y ab b a)) = _
    simp only [classicalReplacementKraus,
      Matrix.single_apply]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simpa [Complex.normSq_apply] using
          Real.mul_self_sqrt (I.classicalWeight_nonneg a (y, b))
      · intro b' _ hb'
        simp [hb']
      · simp
    · intro a' _ ha'
      simp [ha']
    · simp
  ext b b'
  rw [(preservesDiagonalBranches_iff_classicalWeight
        (I := I.classicalReplacement)).mp
      I.classicalReplacement_preservesDiagonalBranches y d b b',
    (preservesDiagonalBranches_iff_classicalWeight (I := I)).mp hI y d b b']
  simp only [hweight]

/-- The canonical replacement and the original operation agree on all CQ inputs, retaining an
arbitrary finite reference and its independent row/column coordinates. -/
theorem PreservesDiagonalBranches.classicalReplacement_operation_tensorId
    (I : Instrument Hin Hout Outcome) (hI : I.PreservesDiagonalBranches)
    (rho : Op (Hin × Ref))
    (hrho : IsClassicalOnFirst (Alpha := Hin) (Ref := Ref) rho)
    (y : Outcome) :
    mapTensorId (I.classicalReplacement.operation y) Ref rho =
      mapTensorId (I.operation y) Ref rho := by
  ext p q
  rcases p with ⟨b, e⟩
  rcases q with ⟨b', e'⟩
  rw [mapTensorId_apply, mapTensorId_apply]
  have hblock :
      rho.submatrix (fun a => (a, e)) (fun a => (a, e')) =
        Matrix.diagonal (fun a => rho (a, e) (a, e')) := by
    ext a a'
    by_cases haa' : a = a'
    · subst a'
      simp
    · rw [Matrix.diagonal_apply_ne _ haa']
      exact hrho a a' e e' haa'
  rw [hblock, hI.classicalReplacement_operation_diagonal I y]

end Instrument
end LOCC
