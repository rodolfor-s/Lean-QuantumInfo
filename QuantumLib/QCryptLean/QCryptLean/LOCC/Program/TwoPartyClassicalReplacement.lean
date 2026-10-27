import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.ClassicalTransition
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-!
# Explicit classical realizations of two-party programs

The replacement below keeps the existing `Program` syntax and replaces each local action by
basis-to-basis Kraus matrices implementing its stochastic action on CQ inputs. It retains raw
outcomes, announcements, actors, dependent successor multipartite systems, continuations, and the
complete public boundary. The local-instrument interpretation is that of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2; the CQ domain is the finite
matrix form of Renner's `classform` condition in quant-ph/0512258v2.
-/

open Quantum.Channels (
  krausMap
  krausMap_eq_sum_conjLinearMap
  mapTensorId
  mapTensorId_apply)

open scoped Matrix BigOperators
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

namespace AnnouncedAction

variable {P Public : Type} [Fintype P] [DecidableEq P]
  [Fintype Public] [DecidableEq Public]

/-- The party-local CP operation at one raw outcome of a possibly dependent-output announced
action. -/
def localOperation {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome) :
    Op (R.reg A.actor) →ₗ[ℂ] Op (A.Output (A.announce o)) :=
  krausMap (A.kraus o)

/-- Canonical local transition weight for one raw outcome of an announced action. -/
def localClassicalWeight {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) : ℝ :=
  ((A.localOperation o (Matrix.single a a 1)) b b).re

/-- A raw announced-action transition weight is the sum of squared moduli over its hidden Kraus
fibre. -/
theorem localClassicalWeight_eq_sum_normSq {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) :
    A.localClassicalWeight o a b = ∑ r, Complex.normSq (A.kraus o r b a) := by
  simp only [localClassicalWeight, localOperation,
    krausMap_eq_sum_conjLinearMap, LinearMap.sum_apply,
    Matrix.sum_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hterm :
    (Matrix.conjLinearMap (A.kraus o r) (Matrix.single a a 1)) b b =
        A.kraus o r b a * star (A.kraus o r b a) := by
    simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.single_apply]
    · intro x _ hxa
      simp [hxa.symm]
    · simp
  rw [hterm]
  simp [Complex.normSq_apply]

/-- Raw announced-action transition weights are nonnegative. -/
theorem localClassicalWeight_nonneg {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) :
    0 ≤ A.localClassicalWeight o a b := by
  rw [A.localClassicalWeight_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Raw announced-action transition weights are normalized jointly across raw outcomes and their
dependent local output bases. -/
theorem sum_localClassicalWeight {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (a : R.reg A.actor) :
    ∑ o, ∑ b, A.localClassicalWeight o a b = 1 := by
  simp_rw [A.localClassicalWeight_eq_sum_normSq]
  calc
    (∑ o, ∑ b, ∑ r, Complex.normSq (A.kraus o r b a)) =
        ∑ o, ∑ r, ∑ b, Complex.normSq (A.kraus o r b a) := by
      apply Finset.sum_congr rfl
      intro o _
      exact Finset.sum_comm
    _ = 1 := by
      have h := congrArg (fun M => M a a) A.complete
      simp only [Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, ite_eq_left] at h
      have hre := congrArg Complex.re h
      simp only [Complex.re_sum, Complex.one_re] at hre
      simpa [Complex.normSq_apply] using hre

/-- One basis-to-basis Kraus matrix of an announced action's canonical replacement. -/
def classicalReplacementKraus {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (ab : R.reg A.actor × A.Output (A.announce o)) :
    Matrix (A.Output (A.announce o)) (R.reg A.actor) ℂ :=
  Matrix.single ab.2 ab.1
    ((Real.sqrt (A.localClassicalWeight o ab.1 ab.2) : ℝ) : ℂ)

/-- The announced replacement Kraus family is complete across all raw outcomes. -/
theorem classicalReplacementKraus_complete {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) :
    ∑ o, ∑ ab : R.reg A.actor × A.Output (A.announce o),
      (A.classicalReplacementKraus o ab)ᴴ * A.classicalReplacementKraus o ab = 1 := by
  simp only [classicalReplacementKraus]
  simp only [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  simp_rw [Fintype.sum_prod_type]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [RCLike.star_def, Complex.conj_ofReal, one_apply_eq]
    simp_rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (A.localClassicalWeight_nonneg _ _ _)]
    convert congrArg (fun x : ℝ => (x : ℂ))
      (A.sum_localClassicalWeight i) using 1
    · simp [Matrix.sum_apply, Matrix.single_apply]
  · simp only [Matrix.sum_apply, Matrix.one_apply, hij, ite_false]
    apply Finset.sum_eq_zero
    intro o _
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.single_apply_of_ne]
    intro h
    exact hij (h.1.symm.trans h.2)

/-- Replace each raw local operation by its canonical basis-to-basis realization while preserving
the actor, raw outcomes, announcement map, and dependent successor multipartite systems
definitionally. -/
@[reducible] def classicalReplacement {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) : AnnouncedAction R Public where
  actor := A.actor
  Output := A.Output
  Outcome := A.Outcome
  announce := A.announce
  krausIndex o := R.reg A.actor × A.Output (A.announce o)
  kraus := A.classicalReplacementKraus
  complete := A.classicalReplacementKraus_complete

@[simp] theorem classicalReplacement_actor {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) : A.classicalReplacement.actor = A.actor := rfl

@[simp] theorem classicalReplacement_announce {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome) :
    A.classicalReplacement.announce o = A.announce o := rfl

end AnnouncedAction

namespace PrivateAction

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Replace a private local instrument by its canonical basis-to-basis realization, preserving the
actor, private raw-outcome type, and input/output multipartite systems. -/
@[reducible] def classicalReplacement {R : MultipartiteSystem P} (A : PrivateAction R) :
    PrivateAction R :=
  PrivateAction.ofInstrument A.actor A.instrument.classicalReplacement

@[simp] theorem classicalReplacement_actor {R : MultipartiteSystem P} (A : PrivateAction R) :
    A.classicalReplacement.actor = A.actor := rfl

end PrivateAction

namespace AnnouncedAction

variable {P Public : Type} [Fintype P] [DecidableEq P]
  [Fintype Public] [DecidableEq Public]

/-- Entrywise action of one announced raw branch after adjoining spectator identities. -/
theorem liftedOperation_apply
    {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public)
    (o : A.Outcome) (rho : Op R.total)
    (q q' : (A.out (A.announce o)).total) :
    (A.liftedOperation o rho) q q' =
      (A.localOperation o
        (rho.submatrix
          (fun x =>
            (R.splitAt A.actor).symm
              (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
          (fun y =>
            (R.splitAt A.actor).symm
              (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2))))
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1 := by
  have hsum (f : R.total → ℂ) :
      (∑ x, f x) =
        ∑ p : R.reg A.actor × R.rest A.actor,
          f ((R.splitAt A.actor).symm p) := by
    exact (Equiv.sum_comp (R.splitAt A.actor).symm f).symm
  simp only [AnnouncedAction.liftedOperation, krausMap_eq_sum_conjLinearMap,
    AnnouncedAction.liftedKraus,
    localOperation, Matrix.conjLinearMap, LinearMap.coe_sum, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply,
    localKrausLift_apply, ite_mul, zero_mul, Matrix.conjTranspose_apply,
    RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Matrix.submatrix_apply]

/-- Every raw local operation of the announced replacement preserves diagonal matrices. -/
theorem classicalReplacement_localOperation_preservesDiagonal
    {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) :
    ∀ o rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' →
        (A.classicalReplacement.localOperation o rho) b b' = 0 := by
  intro o rho _ b b' hne
  change A.Outcome at o
  change Op (R.reg A.actor) at rho
  change A.Output (A.announce o) at b b'
  rw [localOperation, krausMap_eq_sum_conjLinearMap]
  change ((∑ ab : R.reg A.actor × A.Output (A.announce o),
    Matrix.conjLinearMap (A.classicalReplacementKraus o ab)) rho) b b' = 0
  simp only [Matrix.conjLinearMap,
    classicalReplacementKraus, Matrix.conjTranspose_single, RCLike.star_def,
    Complex.conj_ofReal, Matrix.single_mul_mul_single, LinearMap.coe_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro ab _
  rw [Matrix.single_apply_of_ne]
  intro h
  exact hne (h.1.symm.trans h.2)

/-- A diagonal-preserving announced raw operation is its stochastic transition on diagonals. -/
theorem localOperation_diagonal_apply
    {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public)
    (o : A.Outcome)
    (hlocal : ∀ rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o rho) b b' = 0)
    (d : R.reg A.actor → ℂ)
    (b b' : A.Output (A.announce o)) :
    A.localOperation o (Matrix.diagonal d) b b' =
      if b = b' then
        ∑ a, (A.localClassicalWeight o a b : ℂ) * d a
      else 0 := by
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
        A.localOperation o (Matrix.single a a 1) b b =
          (A.localClassicalWeight o a b : ℂ) := by
      rw [A.localClassicalWeight_eq_sum_normSq]
      simp only [localOperation, krausMap_eq_sum_conjLinearMap,
        LinearMap.sum_apply, Matrix.sum_apply,
        Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro r _
      have hterm :
    (Matrix.conjLinearMap (A.kraus o r) (Matrix.single a a 1)) b b =
            A.kraus o r b a * star (A.kraus o r b a) := by
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
    exact hlocal (Matrix.diagonal d)
      (fun a a' haa' => Matrix.diagonal_apply_ne _ haa') b b' hbb'

/-- The replacement and original raw local operations agree on diagonal inputs whenever the
original raw operation preserves diagonality. -/
theorem classicalReplacement_localOperation_diagonal
    {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public)
    (o : A.Outcome)
    (hlocal : ∀ rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o rho) b b' = 0)
    (d : R.reg A.actor → ℂ) :
    A.classicalReplacement.localOperation o (Matrix.diagonal d) =
      A.localOperation o (Matrix.diagonal d) := by
  have hweight (a : R.reg A.actor)
      (b : A.Output (A.announce o)) :
      A.classicalReplacement.localClassicalWeight o a b =
        A.localClassicalWeight o a b := by
    refine (localClassicalWeight_eq_sum_normSq A.classicalReplacement o a b).trans ?_
    change (∑ ab : R.reg A.actor × A.Output (A.announce o),
      Complex.normSq (A.classicalReplacementKraus o ab b a)) = _
    simp only [classicalReplacementKraus,
      Matrix.single_apply]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simpa [Complex.normSq_apply] using
          Real.mul_self_sqrt (A.localClassicalWeight_nonneg o a b)
      · intro b' _ hb'
        simp [hb']
      · simp
    · intro a' _ ha'
      simp [ha']
    · simp
  ext b b'
  rw [A.classicalReplacement.localOperation_diagonal_apply o
      (A.classicalReplacement_localOperation_preservesDiagonal o) d b b',
    A.localOperation_diagonal_apply o hlocal d b b']
  apply if_congr Iff.rfl
  · exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => (t : ℂ) * d a)
      (hweight a b))
  · rfl

/-- Honest-register preservation recovers the acting party's diagonal-preservation law once a
spectator basis point is fixed. -/
theorem PreservesHonestRegistersDiagonal.localOperation_preservesDiagonal_at
    {R : MultipartiteSystem TwoParty.Party}
    (A : AnnouncedAction R Public)
    (hA : A.PreservesHonestRegistersDiagonal)
    (s : R.rest A.actor) (o : A.Outcome) :
    ∀ sigma,
      (∀ a a', a ≠ a' → sigma a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o sigma) b b' = 0 := by
  intro sigma hsigma b b' hbb'
  let rho : Op R.total := fun q q' =>
    if ((R.splitAt A.actor) q).2 = s ∧
        ((R.splitAt A.actor) q').2 = s then
      sigma ((R.splitAt A.actor q).1) ((R.splitAt A.actor q').1)
    else 0
  have hrho : R.HonestRegistersDiagonal rho := by
    intro q q' hqq'
    by_cases hs :
        ((R.splitAt A.actor) q).2 = s ∧
          ((R.splitAt A.actor) q').2 = s
    · rw [show rho q q' =
          sigma ((R.splitAt A.actor q).1) ((R.splitAt A.actor q').1) by
        simp [rho, hs]]
      apply hsigma
      intro hlocal
      have hrest : ((R.splitAt A.actor) q).2 =
          ((R.splitAt A.actor) q').2 := hs.1.trans hs.2.symm
      have hq : q = q' :=
        (R.splitAt A.actor).injective (Prod.ext hlocal hrest)
      subst q'
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    · simp [rho, hs]
  let q := (R.splitAtSet A.actor (A.Output (A.announce o))).symm (b, s)
  let q' := (R.splitAtSet A.actor (A.Output (A.announce o))).symm (b', s)
  have hqne : q ≠ q' := by
    intro h
    apply hbb'
    have := congrArg (fun z =>
      ((R.splitAtSet A.actor (A.Output (A.announce o))) z).1) h
    simpa [q, q'] using this
  have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
    by_cases ha : q .alice = q' .alice
    · exact Or.inr (by
        intro hb
        apply hqne
        funext i
        cases i with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  have hzero := hA o rho hrho q q' hdiff
  rw [AnnouncedAction.liftedOperation_apply] at hzero
  have hslice :
      rho.submatrix
          (fun x => (R.splitAt A.actor).symm
            (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
          (fun y => (R.splitAt A.actor).symm
            (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) = sigma := by
    ext a a'
    have hq : ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2 = s :=
      congrArg Prod.snd ((R.splitAtSet A.actor (A.Output (A.announce o))).apply_symm_apply
        (b, s))
    have hq' : ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2 = s :=
      congrArg Prod.snd ((R.splitAtSet A.actor (A.Output (A.announce o))).apply_symm_apply
        (b', s))
    rw [hq, hq']
    change (if (R.splitAt A.actor ((R.splitAt A.actor).symm (a, s))).2 = s ∧
      (R.splitAt A.actor ((R.splitAt A.actor).symm (a', s))).2 = s then
        sigma (R.splitAt A.actor ((R.splitAt A.actor).symm (a, s))).1
          (R.splitAt A.actor ((R.splitAt A.actor).symm (a', s))).1 else 0) = sigma a a'
    simp only [Equiv.apply_symm_apply, and_self, ite_true]
  rw [hslice] at hzero
  simpa [q, q'] using hzero

/-- The canonical replacement of any announced action preserves honest-register diagonality on
every raw branch. -/
theorem classicalReplacement_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party}
    (A : AnnouncedAction R Public) :
    A.classicalReplacement.PreservesHonestRegistersDiagonal := by
  intro o rho hrho q q' hqq'
  rw [AnnouncedAction.liftedOperation_apply]
  let sigma : Op (R.reg A.actor) :=
    rho.submatrix
      (fun x => (R.splitAt A.actor).symm
        (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
      (fun y => (R.splitAt A.actor).symm
        (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2))
  have hsigma : ∀ a a', a ≠ a' → sigma a a' = 0 := by
    intro a a' haa'
    apply hrho
    have htotal :
        (R.splitAt A.actor).symm
            (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2) ≠
          (R.splitAt A.actor).symm
            (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2) := by
      intro h
      apply haa'
      have := congrArg (fun z => ((R.splitAt A.actor) z).1) h
      simpa using this
    by_cases ha :
        ((R.splitAt A.actor).symm
            (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2)) .alice =
          ((R.splitAt A.actor).symm
            (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) .alice
    · exact Or.inr (by
        intro hb
        apply htotal
        funext j
        cases j with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  by_cases hlocal :
      ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1 ≠
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1
  · exact A.classicalReplacement_localOperation_preservesDiagonal
      o sigma hsigma _ _ hlocal
  · have hlocalEq :
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1 =
          ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1 :=
      not_ne_iff.mp hlocal
    have hqne : q ≠ q' := by
      intro h
      subst h
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    have hrest :
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2 ≠
          ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2 := by
      intro h
      apply hqne
      apply (R.splitAtSet A.actor (A.Output (A.announce o))).injective
      exact Prod.ext hlocalEq h
    have hsigmaZero : sigma = 0 := by
      ext a a'
      apply hrho
      have htotal :
          (R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2) ≠
            (R.splitAt A.actor).symm
              (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2) := by
        intro h
        apply hrest
        have := congrArg (fun z => ((R.splitAt A.actor) z).2) h
        simpa using this
      by_cases ha :
          ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2)) .alice =
            ((R.splitAt A.actor).symm
              (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) .alice
      · exact Or.inr (by
          intro hb
          apply htotal
          funext j
          cases j with
          | alice => exact ha
          | bob => exact hb)
      · exact Or.inl ha
    change (A.classicalReplacement.localOperation o sigma) _ _ = 0
    rw [hsigmaZero]
    exact congrFun (congrFun (map_zero (A.classicalReplacement.localOperation o)) _) _

/-- On CQ inputs, a diagonality-preserving raw announced branch and its manifest classical
replacement have the same lifted operation, including arbitrary reference blocks. -/
theorem PreservesHonestRegistersDiagonal.classicalReplacement_liftedOperation_tensorId
    {R : MultipartiteSystem TwoParty.Party}
    (A : AnnouncedAction R Public)
    (hA : A.PreservesHonestRegistersDiagonal)
    {E : Type}
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho)
    (o : A.Outcome) :
    mapTensorId (A.classicalReplacement.liftedOperation o) E rho =
      mapTensorId (A.liftedOperation o) E rho := by
  rcases isEmpty_or_nonempty (R.rest A.actor) with hEmpty | hNonempty
  · let := hEmpty
    ext p q
    exact isEmptyElim
      (((R.splitAtSet A.actor (A.Output (A.announce o))) p.1).2)
  · rcases hNonempty with ⟨s⟩
    ext p q
    rcases p with ⟨qOut, e⟩
    rcases q with ⟨qOut', e'⟩
    change (A.out (A.announce o)).total at qOut qOut'
    refine (mapTensorId_apply (A.classicalReplacement.liftedOperation o)
      rho (qOut, e) (qOut', e')).trans ?_
    refine Eq.trans ?_ (mapTensorId_apply (A.liftedOperation o)
      rho (qOut, e) (qOut', e')).symm
    refine (AnnouncedAction.liftedOperation_apply A.classicalReplacement o
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))) qOut qOut').trans ?_
    refine Eq.trans ?_ (AnnouncedAction.liftedOperation_apply A o
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))) qOut qOut').symm
    let sigma : Op (R.reg A.actor) :=
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))).submatrix
        (fun x => (R.splitAt A.actor).symm
          (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut).2))
        (fun y => (R.splitAt A.actor).symm
          (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut').2))
    have hsigma :
        sigma = Matrix.diagonal (fun a =>
          rho
            ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut).2), e)
            ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut').2), e')) := by
      ext a a'
      by_cases haa' : a = a'
      · subst a'
        simp [sigma]
      · rw [Matrix.diagonal_apply_ne _ haa']
        exact hrho _ _ e e' (by
          intro h
          apply haa'
          have := congrArg (fun z => ((R.splitAt A.actor) z).1) h
          simpa using this)
    change
      (A.classicalReplacement.localOperation o sigma)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut).1)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut').1) =
        (A.localOperation o sigma)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut).1)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut').1)
    rw [hsigma]
    exact congrFun (congrFun (A.classicalReplacement_localOperation_diagonal o
      (hA.localOperation_preservesDiagonal_at A s o) _) _) _

end AnnouncedAction

namespace PrivateAction

/-- The canonical replacement of any private action preserves honest-register diagonality on
every raw branch. -/
theorem classicalReplacement_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (A : PrivateAction R) :
    A.classicalReplacement.PreservesHonestRegistersDiagonal := by
  simpa [PrivateAction.classicalReplacement] using
    PrivateAction.ofInstrument_preservesHonestRegistersDiagonal
      A.actor A.instrument.classicalReplacement
      A.instrument.classicalReplacement_preservesDiagonalBranches

/-- On CQ inputs, a diagonality-preserving private raw branch and its manifest classical
replacement have the same lifted operation, including arbitrary reference blocks. -/
theorem PreservesHonestRegistersDiagonal.classicalReplacement_liftedOperation_tensorId
    {R : MultipartiteSystem TwoParty.Party} (A : PrivateAction R)
    (hA : A.PreservesHonestRegistersDiagonal)
    {E : Type}
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho)
    (o : A.Outcome) :
    mapTensorId (A.classicalReplacement.liftedOperation o) E rho =
      mapTensorId (A.liftedOperation o) E rho := by
  let announced := AnnouncedAction.ofInstrument A.actor A.instrument (fun _ => ())
  have hAunit : announced.PreservesHonestRegistersDiagonal := hA
  have h := hAunit.classicalReplacement_liftedOperation_tensorId
    announced rho hrho o
  exact h

end PrivateAction

namespace Program

variable {End : MultipartiteSystem TwoParty.Party → Type 1}

/-- Replace every action by its canonical basis-to-basis local realization while recursing over
the existing program syntax. The public tree and terminal values are preserved. -/
def classicalReplacement
    {R : MultipartiteSystem TwoParty.Party} (p : Program R End) :
      Program R End :=
  match p with
  | .done value => .done value
  | @Syntax.announced _ _ _ _ _ _ Public _ _ A k =>
      .announced
        (AnnouncedAction.classicalReplacement (Public := Public) A)
        (fun y => classicalReplacement (k y))
  | .priv A k =>
      .priv A.classicalReplacement (classicalReplacement k)

/-- Replacing the local realization of each action preserves the public output tree. -/
@[simp] theorem boundary_classicalReplacement {R : MultipartiteSystem TwoParty.Party}
    (p : Program R End) : p.classicalReplacement.boundary = p.boundary := by
  induction p with
  | done value => rfl
  | priv A k ih => exact ih
  | announced A k ih => exact congrArg (Boundary.announce _) (funext ih)

/-- Equality of continuation boundaries commutes with their public block inclusions. -/
private theorem reindexOp_publicIncl_cast {Y : Type} [Fintype Y] [DecidableEq Y]
    (B C : Y → Boundary TwoParty.Party) (h : B = C) (y : Y) (rho : Op (B y).space) :
    (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space (congrArg (Boundary.announce
      Y) h))) (Equiv.cast (congrArg Boundary.space (congrArg (Boundary.announce Y) h)))).toLinearMap
    (Matrix.conjLinearMap (Boundary.publicInclKraus B y) rho) =
      Matrix.conjLinearMap (Boundary.publicInclKraus C y)
    ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg (fun D => (D y).space) h)) (Equiv.cast
    (congrArg (fun D => (D y).space) h))).toLinearMap rho) := by
  subst C
  rfl

/-- The canonical replacement of every program has an action-by-action honest-classical
certificate. -/
theorem isHonestClassical_classicalReplacement
    {R : MultipartiteSystem TwoParty.Party} (p : Program R End) :
    p.classicalReplacement.IsHonestClassical := by
  induction p with
  | done value => exact .done value
  | announced A k ih =>
      exact .announced _ _ A.classicalReplacement_preservesHonestRegistersDiagonal ih
  | priv A k ih =>
      exact .priv _ _ A.classicalReplacement_preservesHonestRegistersDiagonal ih

/-- A two-party honest-register diagonal operator becomes a CQ operator after adjoining the
unique reference coordinate. -/
private theorem honestRegistersDiagonal_isClassicalOnFirst_unit
    {R : MultipartiteSystem TwoParty.Party} (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    IsClassicalOnFirst (Alpha := R.total) (Ref := Unit)
      (fun p q => rho p.1 q.1) := by
  intro q q' _ _ hqq'
  apply hrho
  by_cases ha : q .alice = q' .alice
  · exact Or.inr (by
      intro hb
      apply hqq'
      funext i
      cases i with
      | alice => exact ha
      | bob => exact hb)
  · exact Or.inl ha

/-- Reference-free core of program replacement: induction follows raw outcomes before they are
coarse-grained, using the corresponding announced/private tensor-identity identity at each node. -/
private theorem IsHonestClassical.classicalReplacement_denote_eq
    {R : MultipartiteSystem TwoParty.Party} {p : Program R End}
    (hp : p.IsHonestClassical) (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space
      p.boundary_classicalReplacement)) (Equiv.cast (congrArg Boundary.space
      p.boundary_classicalReplacement))).toLinearMap
      (p.classicalReplacement.denote rho) = p.denote rho := by
  induction hp with
  | done value => rfl
  | @announced R Y _ _ A k hA hk ih =>
      change (Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap ((Program.announced
        A.classicalReplacement
        (fun y => classicalReplacement (k y))).denote rho) = _
      rw [denote_announced_eq_sum_liftedOperation,
        denote_announced_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
      apply Finset.sum_congr rfl
      intro o _
      change A.Outcome at o
      dsimp only [AnnouncedAction.classicalReplacement]
      change (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space
        (congrArg (Boundary.announce Y)
    (funext fun y => boundary_classicalReplacement (k y))))) (Equiv.cast (congrArg
            Boundary.space
    (congrArg (Boundary.announce Y)
    (funext fun y => boundary_classicalReplacement (k y)))))).toLinearMap _ = _
      rw [reindexOp_publicIncl_cast _ _
        (funext fun y => boundary_classicalReplacement (k y))]
      let rhoRef : Op (_ × Unit) := fun p q => rho p.1 q.1
      have hactionTensor :=
        hA.classicalReplacement_liftedOperation_tensorId A rhoRef
          (honestRegistersDiagonal_isClassicalOnFirst_unit rho hrho) o
      have haction : A.classicalReplacement.liftedOperation o rho =
          A.liftedOperation o rho := by
        ext q q'
        exact congrArg (fun M => M (q, ()) (q', ())) hactionTensor
      change Matrix.conjLinearMap _ ((Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap
    ((classicalReplacement (k (A.announce o))).denote
    ((Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap (A.classicalReplacement.liftedOperation o
          rho)))) = _
      rw [haction]
      exact congrArg _ (ih (A.announce o) _ ((hA o rho hrho).reindex _))
  | priv A k hA hk ih =>
      change (Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap ((Program.priv A.classicalReplacement
        (classicalReplacement k)).denote rho) = _
      rw [denote_priv_eq_sum_liftedOperation, denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
      apply Finset.sum_congr rfl
      intro o _
      let rhoRef : Op (_ × Unit) := fun p q => rho p.1 q.1
      have hactionTensor :=
        hA.classicalReplacement_liftedOperation_tensorId A rhoRef
          (honestRegistersDiagonal_isClassicalOnFirst_unit rho hrho) o
      have haction : A.classicalReplacement.liftedOperation o rho =
          A.liftedOperation o rho := by
        ext q q'
        exact congrArg (fun M => M (q, ()) (q', ())) hactionTensor
      change (Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap ((classicalReplacement k).denote
    ((Matrix.reindexLinearEquiv ℂ ℂ _ _).toLinearMap (A.classicalReplacement.liftedOperation o
          rho))) = _
      rw [haction]
      exact ih _ ((hA o rho hrho).reindex _)

/-- The explicit local classical replacement has the same complete public boundary and the same
CQ denotation as the authored program. Raw outcomes and announcements are retained at every
node. -/
theorem IsHonestClassical.tensorIdLinear_denote_classicalReplacement
    {R : MultipartiteSystem TwoParty.Party} {p : Program R End}
    (hp : p.IsHonestClassical)
    {E : Type}
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho) :
    mapTensorId (((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space
      p.boundary_classicalReplacement)) (Equiv.cast (congrArg Boundary.space
      p.boundary_classicalReplacement))).toLinearMap).comp
          p.classicalReplacement.denote) E rho =
      mapTensorId p.denote E rho := by
  ext x x'
  rcases x with ⟨q, e⟩
  rcases x' with ⟨q', e'⟩
  rw [mapTensorId_apply, mapTensorId_apply]
  let sigma : Op R.total :=
    rho.submatrix (fun a => (a, e)) (fun a => (a, e'))
  have hsigma : R.HonestRegistersDiagonal sigma := by
    intro a a' hdiff
    exact hrho a a' e e' (by
      intro h
      subst a'
      exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl))
  have hdenote := hp.classicalReplacement_denote_eq sigma hsigma
  exact congrArg (fun M => M q q') hdenote

/-- A recursively certified two-party program preserves full CQ structure, including its
complete public exit and both honest registers, against arbitrary independent reference
row/column indices. -/
theorem IsHonestClassical.denote_tensorId
    {R : MultipartiteSystem TwoParty.Party} {p : Program R End}
    (hp : p.IsHonestClassical)
    {E : Type}
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho) :
    IsClassicalOnFirst (Alpha := p.boundary.space) (Ref := E)
    (mapTensorId p.denote E rho) := by
  intro x x' e e' hxx
  rcases x with ⟨y, q⟩
  rcases x' with ⟨y', q'⟩
  rw [mapTensorId_apply]
  have hblock : R.HonestRegistersDiagonal
      (Matrix.of fun i j => rho (i, e) (j, e')) := by
    intro qIn qIn' hdiff
    exact hrho qIn qIn' e e' (by
      intro h
      subst qIn'
      exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl))
  by_cases hyy' : y = y'
  · subst y'
    have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
      by_cases hAlice : q .alice = q' .alice
      · right
        intro hBob
        apply hxx
        congr
        funext i
        cases i with
        | alice => exact hAlice
        | bob => exact hBob
      · exact Or.inl hAlice
    exact hp.denote (Matrix.of fun i j => rho (i, e) (j, e')) hblock y q q' hdiff
  · exact p.denote_isExitBlockDiagonal
      (Matrix.of fun i j => rho (i, e) (j, e')) y y' q q' hyy'

end Program
end LOCC
