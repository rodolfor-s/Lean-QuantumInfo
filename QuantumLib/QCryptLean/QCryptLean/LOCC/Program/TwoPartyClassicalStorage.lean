import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.ClassicalPreservation
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Operators.Basic

/-! # Two Party Classical Storage -/


noncomputable section

open Quantum.Operators (Op)

namespace LOCC

namespace MultipartiteSystem

/-- An operator has no off-diagonal entry in either named honest-party register. -/
def HonestRegistersDiagonal
    (R : MultipartiteSystem TwoParty.Party) (rho : Op R.total) : Prop :=
  ∀ q q', q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob → rho q q' = 0

/-- Two-party diagonality is preserved by a bijection of the joint register. -/
theorem HonestRegistersDiagonal.reindex
    {R S : MultipartiteSystem TwoParty.Party} {rho : Op R.total}
    (h : R.HonestRegistersDiagonal rho) (e : R.total ≃ S.total) :
    S.HonestRegistersDiagonal ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap rho) := by
  intro q q' hqq'
  apply h
  by_contra hn
  push Not at hn
  have heq : e.symm q = e.symm q' := by
    funext i
    cases i with
    | alice => exact hn.1
    | bob => exact hn.2
  have hq := e.symm.injective heq
  subst q'
  exact hqq'.elim (fun h => h rfl) (fun h => h rfl)

end MultipartiteSystem

namespace Boundary

/-- Within every fixed public exit, an output operator is diagonal in Alice's and Bob's
registers. -/
def HonestRegistersDiagonal
    (B : Boundary TwoParty.Party) (sigma : Op B.space) : Prop :=
  ∀ e (q q' : (B.system e).total),
    q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob → sigma ⟨e, q⟩ ⟨e, q'⟩ = 0

end Boundary

namespace PrivateAction

/-- Every private raw outcome preserves honest-register diagonality. -/
def PreservesHonestRegistersDiagonal {R : MultipartiteSystem TwoParty.Party}
    (A : PrivateAction R) : Prop :=
  ∀ o rho, R.HonestRegistersDiagonal rho →
    A.out.HonestRegistersDiagonal (A.liftedOperation o rho)

/-- A party-local instrument preserving its local diagonal also preserves the two-party predicate.

This is the `K ⊗ 1` lifting step in the finite local-instrument model of Chitambar et al.,
arXiv:1210.4583, Section 2. -/
theorem ofInstrument_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (i : TwoParty.Party)
    {HH : Type} [Fintype HH] [DecidableEq HH]
    {Y : Type} [Fintype Y] (I : Instrument (R.reg i) HH Y)
    (hI : I.PreservesDiagonalBranches) :
    (PrivateAction.ofInstrument i I).PreservesHonestRegistersDiagonal := by
  intro o rho hrho q q' hqq'
  change ((I.liftAt R i).operation o rho) q q' = 0
  rw [Instrument.liftAt_operation_apply (R := R) i I o rho q q']
  let sigma : Op (R.reg i) :=
    rho.submatrix
      (fun x => (R.splitAt i).symm
        (x, ((R.splitAtSet i HH) q).2))
      (fun y => (R.splitAt i).symm
        (y, ((R.splitAtSet i HH) q').2))
  have hsigma : ∀ a a', a ≠ a' → sigma a a' = 0 := by
    intro a a' haa'
    apply hrho
    have htotal :
        (R.splitAt i).symm
            (a, ((R.splitAtSet i HH) q).2) ≠
          (R.splitAt i).symm
            (a', ((R.splitAtSet i HH) q').2) := by
      intro h
      apply haa'
      have := congrArg (fun z => ((R.splitAt i) z).1) h
      simpa using this
    by_cases ha :
        ((R.splitAt i).symm
            (a, ((R.splitAtSet i HH) q).2)) .alice =
          ((R.splitAt i).symm
            (a', ((R.splitAtSet i HH) q').2)) .alice
    · exact Or.inr (by
        intro hb
        apply htotal
        funext j
        cases j with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  by_cases hlocal :
      ((R.splitAtSet i HH) q).1 ≠ ((R.splitAtSet i HH) q').1
  · exact hI o sigma hsigma _ _ hlocal
  · have hlocalEq :
        ((R.splitAtSet i HH) q).1 = ((R.splitAtSet i HH) q').1 :=
      not_ne_iff.mp hlocal
    have hqne : q ≠ q' := by
      intro h
      subst h
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    have hrest :
        ((R.splitAtSet i HH) q).2 ≠ ((R.splitAtSet i HH) q').2 := by
      intro h
      apply hqne
      apply (R.splitAtSet i HH).injective
      exact Prod.ext hlocalEq h
    have hsigmaZero : sigma = 0 := by
      ext a a'
      apply hrho
      have htotal :
          (R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2) ≠
            (R.splitAt i).symm
              (a', ((R.splitAtSet i HH) q').2) := by
        intro h
        apply hrest
        have := congrArg (fun z => ((R.splitAt i) z).2) h
        simpa using this
      by_cases ha :
          ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2)) .alice =
            ((R.splitAt i).symm
              (a', ((R.splitAtSet i HH) q').2)) .alice
      · exact Or.inr (by
          intro hb
          apply htotal
          funext j
          cases j with
          | alice => exact ha
          | bob => exact hb)
      · exact Or.inl ha
    change (I.operation o sigma) _ _ = 0
    rw [hsigmaZero]
    simp

end PrivateAction

namespace AnnouncedAction

/-- Every raw outcome of an announced action preserves the diagonal predicate at its announced
multipartite system. -/
def PreservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y) : Prop :=
  ∀ o rho, R.HonestRegistersDiagonal rho →
    (A.out (A.announce o)).HonestRegistersDiagonal (A.liftedOperation o rho)

/-- An announced party-local instrument preserving its local diagonal preserves the two-party
predicate on every raw branch.

This is the announced `K ⊗ 1` lifting step in the finite LOCC model of Chitambar et al.,
arXiv:1210.4583, Section 2. -/
theorem ofInstrument_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (i : TwoParty.Party)
    {HH : Type} [Fintype HH] [DecidableEq HH]
    {O : Type} [Fintype O] {Y : Type} [Fintype Y] [DecidableEq Y]
    (I : Instrument (R.reg i) HH O) (announce : O → Y)
    (hI : I.PreservesDiagonalBranches) :
    (AnnouncedAction.ofInstrument i I announce).PreservesHonestRegistersDiagonal := by
  intro o rho hrho
  exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal i I hI o rho hrho

end AnnouncedAction

namespace Program

/-- Recursive certificate that every raw action branch preserves honest classical storage before
its continuation. -/
inductive IsHonestClassical {End : MultipartiteSystem TwoParty.Party → Type 1} :
    {R : MultipartiteSystem TwoParty.Party} → Program R End → Prop where
  /-- Termination is an honest-classical program. -/
  | done {R : MultipartiteSystem TwoParty.Party} (value : End R) :
      IsHonestClassical (Program.done value)
  /-- An announced node is certified by its raw-action law and every continuation. -/
  | announced {R : MultipartiteSystem TwoParty.Party} {Y : Type} [Fintype Y] [DecidableEq Y]
      (A : AnnouncedAction R Y)
      (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End)
      (hA : A.PreservesHonestRegistersDiagonal)
      (hk : ∀ y, IsHonestClassical (k y)) :
      IsHonestClassical (Program.announced A k)
  /-- A private node is certified by its raw-action law and its continuation. -/
  | priv {R : MultipartiteSystem TwoParty.Party}
      (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End)
      (hA : A.PreservesHonestRegistersDiagonal) (hk : IsHonestClassical k) :
      IsHonestClassical (Program.priv A k)

variable {End : MultipartiteSystem TwoParty.Party → Type 1}

/-- A private program is honest-classical exactly when its action and continuation are certified. -/
@[simp] theorem isHonestClassical_priv_iff
    {R : MultipartiteSystem TwoParty.Party}
    (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End) :
    (Program.priv A k).IsHonestClassical ↔
      A.PreservesHonestRegistersDiagonal ∧ k.IsHonestClassical := by
  constructor
  · intro h
    cases h with
    | priv _ _ hA hk => exact ⟨hA, hk⟩
  · rintro ⟨hA, hk⟩
    exact .priv A k hA hk

/-- A recursively certified program maps an honest-register diagonal input to an output diagonal
within every fixed public exit. Cross-exit blocks are handled separately by
`Program.denote_isExitBlockDiagonal`. -/
theorem IsHonestClassical.denote
    {R : MultipartiteSystem TwoParty.Party} {p : Program R End}
    (hp : p.IsHonestClassical) (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    p.boundary.HonestRegistersDiagonal (p.denote rho) := by
  induction hp with
  | done value =>
      intro e q q' hqq'
      rcases e with ⟨⟩
      rw [Program.denote_done]
      exact hrho q q' hqq'
  | @announced R Y _ _ A next hA hnext ih =>
      let Bs : Y → Boundary TwoParty.Party := fun y => (next y).boundary
      intro e q q' hqq'
      rcases e with ⟨y, e⟩
      change ((Bs y).system e).total at q q'
      rw [Program.denote_announced_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro o _
      let normal := (Equiv.cast (congrArg MultipartiteSystem.total
        (SystemPresentation.update_eq_set R A.actor (A.Output (A.announce o))))).symm
      let sigma := (Matrix.reindexLinearEquiv ℂ ℂ normal normal).toLinearMap (A.liftedOperation o
        rho)
      let M := (next (A.announce o)).denote sigma
      by_cases ho : A.announce o = y
      · subst y
        let E : Matrix (Σ z, (Bs z).space) (Bs (A.announce o)).space ℂ :=
          sigmaInclKraus (fun z => (Bs z).space) (A.announce o)
        have hentry : Matrix.conjLinearMap E M ⟨A.announce o, ⟨e, q⟩⟩
            ⟨A.announce o, ⟨e, q'⟩⟩ = M ⟨e, q⟩ ⟨e, q'⟩ := by
          simp [Matrix.conjLinearMap, E, sigmaInclKraus, Matrix.mul_apply,
            Matrix.conjTranspose_apply]
        exact hentry.trans
          (ih (A.announce o) sigma ((hA o rho hrho).reindex normal) e q q' hqq')
      · exact Matrix.conjLinearMap_apply_eq_zero_of_row_left
          (Boundary.publicInclKraus Bs (A.announce o)) M
          (funext fun t => Boundary.publicInclKraus_apply_eq_zero_of_fst_ne Bs
            (p := ⟨⟨y, e⟩, q⟩) (Ne.symm ho) t) ⟨⟨y, e⟩, q'⟩
  | priv A next hA hnext ih =>
      intro e q q' hqq'
      rw [Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro o _
      exact ih _ ((hA o rho hrho).reindex _) e q q' hqq'

end Program

end LOCC
