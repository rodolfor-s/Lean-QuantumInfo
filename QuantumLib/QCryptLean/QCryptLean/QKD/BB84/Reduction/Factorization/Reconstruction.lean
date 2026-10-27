import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondAlgebra
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Reconstruction -/


open Quantum.Operators (Op)

open Quantum.Channels Quantum.Metrics
open Quantum.Symmetry (pairFunctions)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.FiniteKey

/-- Group selected party strings into rounds, retaining the actual comparison control. -/
def comparisonPreToRetainedControlEquiv (N n : ℕ) :
    ComparisonPreOutput N n ≃ Signals n × ComparisonControl N n :=
  (pairFunctions Bit Bit n).symm.prodCongr (Equiv.refl _)

/-- Apply the retained map to every control block after structural round grouping. -/
noncomputable def retainedControlLift (N n : ℕ) (Y : Type*)
    (Φ : Operation (Signals n) Y) :
    Operation (ComparisonPreOutput N n) (Y × ComparisonControl N n) :=
  (mapTensorId Φ (ComparisonControl N n)).comp
    (Matrix.reindexLinearEquiv ℂ ℂ (comparisonPreToRetainedControlEquiv N n)
      (comparisonPreToRetainedControlEquiv N n)).toLinearMap

/-- Positive support of one total selected-control fibre. -/
abbrev SelectedControlSupport
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX))) :=
  {omega : RawControl N //
    0 < totalSelectedControlKernel N nK mZ mX pA pB
      (Math.FiniteEmbedding.joinSubsetPerm S pi) omega}

/-- Positive support of one total shortage-control fibre. -/
abbrev FailureControlSupport
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) :=
  {omega : RawControl N //
    0 < totalFailureControlKernel N nK mZ mX pA pB j omega}

/-- Positive selected-kernel support supplies the actual quota witness. -/
theorem selectedControlSupport_hasQuotas
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S
      pi) :
    HasQuotas nK mZ mX omega.1 := by
  have hselect := totalSelectedControlKernel_select
    N nK mZ mX pA pB (Math.FiniteEmbedding.joinSubsetPerm
      S pi)
      omega.1 omega.2
  apply (select_isSome_iff nK mZ mX omega.1).mp
  rw [hselect]
  rfl

/-- The supported selected embedding is the literal subset-permutation embedding. -/
theorem selectedControlSupport_selectedEmbedding
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S
      pi) :
    selectedEmbedding omega.1
        (selectedControlSupport_hasQuotas N nK mZ mX pA pB
          S pi omega) =
      Math.FiniteEmbedding.joinSubsetPerm S pi := by
  have hselect := totalSelectedControlKernel_select
    N nK mZ mX pA pB (Math.FiniteEmbedding.joinSubsetPerm
      S pi)
      omega.1 omega.2
  unfold select at hselect
  split at hselect
  · simpa only [Option.some.injEq] using hselect
  · simp at hselect

/-- Positive failure-kernel support supplies the actual shortage witness. -/
theorem failureControlSupport_not_hasQuotas
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    ¬ HasQuotas nK mZ mX omega.1 :=
  totalFailureControlKernel_not_hasQuotas
    N nK mZ mX pA pB j omega.1 omega.2

/-- Input type of the complete-control reconstruction instrument. -/
abbrev ReconstructionInput
    (N nK mZ mX ell ellEV leakEC : ℕ) :=
  RetainedAnalysisOutput nK mZ mX ell ellEV leakEC ×
    ComparisonControl N (nK + mZ + mX)

/-- Output type of the complete-control reconstruction instrument. -/
abbrev ReconstructionOutput
    (N nK mZ mX ell ellEV leakEC : ℕ) :=
  (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space

/-- Hidden reconstruction Kraus index. -/
abbrev ReconstructionKrausIndex
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :=
  (Σ S : Set.powersetCard (Fin N) (nK + mZ + mX),
    Σ pi : Equiv.Perm (Fin (nK + mZ + mX)),
      SelectedControlSupport N nK mZ mX pA pB S pi) ⊕
  (Σ j : Fin (nK + mZ + mX),
    RetainedAnalysisOutput nK mZ mX ell ellEV leakEC ×
      FailureControlSupport N nK mZ mX pA pB j)

/-- One supported success Kraus matrix, retaining the complete raw-tail coordinate coherently. -/
def reconstructionSuccessKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S
      pi) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  fun y x =>
    let q := (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm x.1
    let data := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    if x.2 = Sum.inl S ∧ data.1 = pi ∧
        y = successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB
            S pi omega) data.2 then
      Instrument.weightedChoiceScale
        (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi))
            omega.1
    else 0

/-- One supported shortage Kraus matrix, tracing the retained output and preserving metadata. -/
def reconstructionShortageKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 •
    Matrix.single
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
      (r, Sum.inr j) 1

/-- Complete explicit reconstruction Kraus family. -/
def reconstructionKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  match r with
  | Sum.inl ⟨S, pi, omega⟩ =>
      reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
        S pi omega
  | Sum.inr ⟨j, r, omega⟩ =>
      reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega

/-- A success Kraus matrix vanishes on every input column outside its own control block. -/
private theorem reconstructionSuccessKraus_apply_of_control_ne
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
    (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) (hx : x.2 ≠ Sum.inl
      S) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
      S pi omega y x = 0 :=
  ite_eq_right fun h => hx h.1

/-- The ambient reconstruction Kraus family resolves the identity on every control sector. -/
theorem reconstructionKraus_complete
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    ∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
      (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r)ᴴ *
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r = 1 := by
  classical
  have hprob {R : Type} [Fintype R] (p : PMF R) :
      ∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ) = 1 := by
    calc
      ∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ) =
          (∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ)) +
            ∑ a : {x : R // ¬ 0 < p x}, ((p a.1).toReal : ℂ) := by
        suffices (∑ a : {x : R // ¬ 0 < p x}, ((p a.1).toReal : ℂ)) = 0 by
          rw [this, add_zero]
        apply Finset.sum_eq_zero
        intro a _
        have ha : p a.1 = 0 := bot_unique (le_of_not_gt a.2)
        simp [ha]
      _ = ∑ a : R, ((p a).toReal : ℂ) :=
        Fintype.sum_subtype_add_sum_subtype (fun x : R => 0 < p x)
          (fun x => ((p x).toReal : ℂ))
      _ = 1 := LOCC.Instrument.weightedChoiceProbability_sum p
  have hfailure_col_zero
      (l : Fin (nK + mZ + mX))
      (t : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (omega : FailureControlSupport N nK mZ mX pA pB l)
      (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (hcol : ((t, Sum.inr l) : ReconstructionInput
        N nK mZ mX ell ellEV leakEC) ≠ x) :
      reconstructionShortageKraus
          N nK mZ mX ell ellEV leakEC pA pB l t omega y x = 0 := by
    unfold reconstructionShortageKraus
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
      (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
    exact smul_zero _
  have hfailure_sum_zero_on_success
      (a : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      (∑ l, ∑ t, ∑ omega, ∑ y,
        star (reconstructionShortageKraus
          N nK mZ mX ell ellEV leakEC pA pB l t omega y (a, Sum.inl
            S)) *
          reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y x) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro omega _
    apply Finset.sum_eq_zero
    intro y _
    have hcol : ((t, Sum.inr l) : ReconstructionInput
        N nK mZ mX ell ellEV leakEC) ≠ (a, Sum.inl S) :=
          by
      intro h
      cases congrArg Prod.snd h
    rw [hfailure_col_zero l t omega y (a, Sum.inl S) hcol]
    simp
  -- Expand the `(x, z)` entry into the success branches and the shortage branches.
  ext x z
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma,
    Fintype.sum_prod_type (α₁ := RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, reconstructionKraus]
  rcases x with ⟨r, c⟩
  rcases z with ⟨s, d⟩
  cases c with
  | inl S =>
    cases d with
    | inl T =>
      let E := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
      let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
      obtain ⟨u, rfl⟩ := E.surjective r
      obtain ⟨⟨pi, q⟩, rfl⟩ := D.symm.surjective u
      obtain ⟨v, rfl⟩ := E.surjective s
      obtain ⟨⟨pj, t⟩, rfl⟩ := D.symm.surjective v
      by_cases heq : S = T ∧ pi = pj ∧ q = t
      · rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hfailure_sum_zero_on_success (E (D.symm (pi, q)))
          S
          (E (D.symm (pi, q)), Sum.inl S)]
        simp only [add_zero, Matrix.one_apply]
        rw [Fintype.sum_eq_single S]
        · rw [Fintype.sum_eq_single pi]
          · have hout (omega : SelectedControlSupport N nK mZ mX pA pB
            S pi) :
                ∑ y,
                    star (reconstructionSuccessKraus
                      N nK mZ mX ell ellEV leakEC pA pB S
                        pi omega y
                        (E (D.symm (pi, q)), Sum.inl S)) *
                      reconstructionSuccessKraus
                        N nK mZ mX ell ellEV leakEC pA pB
                          S pi omega y
                          (E (D.symm (pi, q)), Sum.inl S)
                            =
                  ((totalSelectedControlKernel N nK mZ mX pA pB
                    (Math.FiniteEmbedding.joinSubsetPerm
                      S pi) omega.1).toReal : ℂ) := by
              let y0 := successCompleteOutputEmbedding
                N nK mZ mX ell ellEV leakEC omega.1
                  (selectedControlSupport_hasQuotas N nK mZ mX pA pB
                    S pi omega) q
              rw [Fintype.sum_eq_single y0]
              · have hd : D (E.symm (E (D.symm (pi, q)))) = (pi, q) :=
                  (congrArg D (E.symm_apply_apply (D.symm (pi, q)))).trans
                    (D.apply_symm_apply (pi, q))
                have hk : reconstructionSuccessKraus
                    N nK mZ mX ell ellEV leakEC pA pB S
                      pi omega y0
                      (E (D.symm (pi, q)), Sum.inl S) =
                    Instrument.weightedChoiceScale
                      (totalSelectedControlKernel N nK mZ mX pA pB
                        (Math.FiniteEmbedding.joinSubsetPerm
                          S pi)) omega.1 :=
                  ite_eq_left ⟨rfl, congrArg Prod.fst hd,
                    congrArg (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
                      omega.1 (selectedControlSupport_hasQuotas N nK mZ mX pA pB
                        S pi omega))
                      (congrArg Prod.snd hd).symm⟩
                exact (congrArg (fun z : ℂ => star z * z) hk).trans
                  (Instrument.weightedChoiceScale_star_mul
                    (totalSelectedControlKernel N nK mZ mX pA pB
                      (Math.FiniteEmbedding.joinSubsetPerm
                        S pi)) omega.1)
              · intro y hy
                simp [reconstructionSuccessKraus, E, D, y0, hy]
            calc
              (∑ omega : SelectedControlSupport N nK mZ mX pA pB
                S pi,
                  ∑ y,
                    star (reconstructionSuccessKraus
                      N nK mZ mX ell ellEV leakEC pA pB S
                        pi omega y
                        (E (D.symm (pi, q)), Sum.inl S)) *
                      reconstructionSuccessKraus
                        N nK mZ mX ell ellEV leakEC pA pB
                          S pi omega y
                          (E (D.symm (pi, q)), Sum.inl
                            S)) =
                    ∑ omega : SelectedControlSupport N nK mZ mX pA pB
                      S pi,
                      ((totalSelectedControlKernel N nK mZ mX pA pB
                        (Math.FiniteEmbedding.joinSubsetPerm
                          S pi)
                          omega.1).toReal : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro omega _
                    exact hout omega
              _ = 1 := hprob (totalSelectedControlKernel N nK mZ mX pA pB
                (Math.FiniteEmbedding.joinSubsetPerm S
                  pi))
          · intro pj hpj
            have hpij : pi ≠ pj := Ne.symm hpj
            simp [reconstructionSuccessKraus, E, D, hpij]
        · -- Kraus operators of another control block `T ≠
        -- S` vanish on the column.
          intro T hTS
          refine Finset.sum_eq_zero fun pi' _ => Finset.sum_eq_zero fun omega _ =>
            Finset.sum_eq_zero fun y _ => ?_
          rw [reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            T pi' omega y _ fun h => hTS (Sum.inl.inj h).symm, star_zero, zero_mul]
      · have hKzero (omega : SelectedControlSupport N nK mZ mX pA pB
        S pi) :
            reconstructionSuccessKraus
                N nK mZ mX ell ellEV leakEC pA pB S pi
                  omega
                  (successCompleteOutputEmbedding
                    N nK mZ mX ell ellEV leakEC omega.1
                      (selectedControlSupport_hasQuotas N nK mZ mX pA pB
                        S pi omega) q)
                  (E (D.symm (pj, t)), Sum.inl T) = 0 := by
          unfold reconstructionSuccessKraus
          simp only [E, D, Equiv.apply_symm_apply]
          split
          · rename_i hcond
            exfalso
            rcases hcond with ⟨hTS, hpj, hout⟩
            apply heq
            refine ⟨(Sum.inl.inj hTS).symm, hpj.symm, ?_⟩
            exact (successCompleteOutputEmbedding
              N nK mZ mX ell ellEV leakEC omega.1
                (selectedControlSupport_hasQuotas N nK mZ mX pA pB
                  S pi omega)).injective hout
          · rfl
        have hinput :
            ((E (D.symm (pi, q)), Sum.inl S) :
              ReconstructionInput N nK mZ mX ell ellEV leakEC) ≠
              ((E (D.symm (pj, t)), Sum.inl T) :
                ReconstructionInput N nK mZ mX ell ellEV leakEC) := by
          intro h
          apply heq
          have hcontrol := congrArg Prod.snd h
          have hcoordinate := congrArg Prod.fst h
          have hdata : (pi, q) = (pj, t) :=
            D.symm.injective (E.injective hcoordinate)
          exact ⟨Sum.inl.inj hcontrol, congrArg Prod.fst hdata,
            congrArg Prod.snd hdata⟩
        rw [hfailure_sum_zero_on_success (E (D.symm (pi, q)))
          S
          (E (D.symm (pj, t)), Sum.inl T)]
        simp only [add_zero, Matrix.one_apply, ite_eq_right hinput]
        rw [Fintype.sum_eq_single S]
        · rw [Fintype.sum_eq_single pi]
          · apply Finset.sum_eq_zero
            intro omega _
            let y0 := successCompleteOutputEmbedding
              N nK mZ mX ell ellEV leakEC omega.1
                (selectedControlSupport_hasQuotas N nK mZ mX pA pB
                  S pi omega) q
            rw [Fintype.sum_eq_single y0]
            · rw [hKzero omega]
              simp
            · intro y hy
              simp [reconstructionSuccessKraus, E, D, y0, hy]
          · intro pk hpk
            have hpik : pi ≠ pk := Ne.symm hpk
            simp [reconstructionSuccessKraus, E, D, hpik]
        · -- Kraus operators of another control block `U ≠
        -- S` vanish on the column.
          intro U hUS
          refine Finset.sum_eq_zero fun pi' _ => Finset.sum_eq_zero fun omega _ =>
            Finset.sum_eq_zero fun y _ => ?_
          rw [reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi' omega y _ fun h => hUS (Sum.inl.inj h).symm, star_zero, zero_mul]
    | inr j =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inl
              S)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr j)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz, mul_zero]
      ]
      rw [show (∑ l, ∑ t, ∑ omega, ∑ y,
          star (reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inl
              S)) *
            reconstructionShortageKraus
              N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inr j)) = 0 by
        apply Finset.sum_eq_zero
        intro l _
        apply Finset.sum_eq_zero
        intro t _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hcol : ((t, Sum.inr l) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inl S)
              := by
          intro h
          cases congrArg Prod.snd h
        have hz : reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inl
              S) = 0 := by
          unfold reconstructionShortageKraus
          refine (Matrix.smul_apply _ _ _ _).trans ?_
          refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
            (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
          exact smul_zero _
        rw [hz]
        simp
      ]
      simp only [zero_add]
      exact (Matrix.one_apply_ne fun h => Sum.inl_ne_inr (congrArg Prod.snd h)).symm
  | inr j =>
    cases d with
    | inl S =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inl
                S)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz]
        simp
      ]
      rw [show (∑ l, ∑ t, ∑ omega, ∑ y,
          star (reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inr j)) *
            reconstructionShortageKraus
              N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inl
                S)) = 0 by
        apply Finset.sum_eq_zero
        intro l _
        apply Finset.sum_eq_zero
        intro t _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hcol : ((t, Sum.inr l) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) ≠ (s, Sum.inl S)
              := by
          intro h
          cases congrArg Prod.snd h
        have hz : reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inl
              S) = 0 := by
          unfold reconstructionShortageKraus
          refine (Matrix.smul_apply _ _ _ _).trans ?_
          refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
            (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
          exact smul_zero _
        rw [hz, mul_zero]
      ]
      simp only [zero_add]
      exact (Matrix.one_apply_ne fun h => Sum.inr_ne_inl (congrArg Prod.snd h)).symm
    | inr k =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr k)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz]
        simp
      ]
      by_cases hinput :
          ((r, Sum.inr j) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) = (s, Sum.inr k)
      · have hrs : r = s := congrArg Prod.fst hinput
        have hjk : j = k := Sum.inr.inj (congrArg Prod.snd hinput)
        subst s
        subst k
        simp only [zero_add, Matrix.one_apply]
        rw [Fintype.sum_eq_single j]
        · rw [Fintype.sum_eq_single r]
          · have hout (omega : FailureControlSupport N nK mZ mX pA pB j) :
                ∑ y,
                    star (reconstructionShortageKraus
                      N nK mZ mX ell ellEV leakEC pA pB j r omega y
                        (r, Sum.inr j)) *
                      reconstructionShortageKraus
                        N nK mZ mX ell ellEV leakEC pA pB j r omega y
                          (r, Sum.inr j) =
                  ((totalFailureControlKernel N nK mZ mX pA pB j
                    omega.1).toReal : ℂ) := by
              let y0 := shortageCompleteOutput
                N nK mZ mX ell ellEV leakEC omega.1
                  (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega)
              rw [Fintype.sum_eq_single y0]
              · dsimp only [reconstructionShortageKraus]
                change star ((_ : ℂ) * _) * ((_ : ℂ) * _) = _
                refine (congrArg (fun z : ℂ => star ((_ : ℂ) * z) * ((_ : ℂ) * z))
                  (Matrix.single_apply_same y0 (r, (Sum.inr j : ComparisonControl N _))
                    (1 : ℂ))).trans ?_
                simpa only [mul_one] using
                  Instrument.weightedChoiceScale_star_mul
                    (totalFailureControlKernel N nK mZ mX pA pB j) omega.1
              · intro y hy
                have hrow : y0 ≠ y := Ne.symm hy
                have hz : reconstructionShortageKraus
                    N nK mZ mX ell ellEV leakEC pA pB j r omega y
                      (r, Sum.inr j) = 0 := by
                  unfold reconstructionShortageKraus
                  refine (Matrix.smul_apply _ _ _ _).trans ?_
                  exact (congrArg (fun z : ℂ => _ • z)
                    (Matrix.single_apply_of_row_ne hrow
                      ((r, Sum.inr j) : ReconstructionInput N nK mZ mX ell ellEV leakEC)
                      (r, Sum.inr j) (1 : ℂ))).trans (smul_zero _)
                rw [hz]
                simp
            calc
              (∑ omega : FailureControlSupport N nK mZ mX pA pB j,
                  ∑ y,
                    star (reconstructionShortageKraus
                      N nK mZ mX ell ellEV leakEC pA pB j r omega y
                        (r, Sum.inr j)) *
                      reconstructionShortageKraus
                        N nK mZ mX ell ellEV leakEC pA pB j r omega y
                          (r, Sum.inr j)) =
                    ∑ omega : FailureControlSupport N nK mZ mX pA pB j,
                      ((totalFailureControlKernel N nK mZ mX pA pB j
                        omega.1).toReal : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro omega _
                    exact hout omega
              _ = 1 := hprob (totalFailureControlKernel N nK mZ mX pA pB j)
          · intro t htr
            apply Finset.sum_eq_zero
            intro omega _
            apply Finset.sum_eq_zero
            intro y _
            have hcol : ((t, Sum.inr j) : ReconstructionInput
                N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
              intro h
              exact htr (congrArg Prod.fst h)
            rw [hfailure_col_zero j t omega y (r, Sum.inr j) hcol]
            simp
        · intro l hlj
          apply Finset.sum_eq_zero
          intro t _
          apply Finset.sum_eq_zero
          intro omega _
          apply Finset.sum_eq_zero
          intro y _
          have hcol : ((t, Sum.inr l) : ReconstructionInput
              N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
            intro h
            exact hlj (Sum.inr.inj (congrArg Prod.snd h))
          rw [hfailure_col_zero l t omega y (r, Sum.inr j) hcol]
          simp
      · simp only [zero_add, Matrix.one_apply]
        refine Eq.trans ?_ (ite_eq_right hinput).symm
        rw [Fintype.sum_eq_single j]
        · rw [Fintype.sum_eq_single r]
          · apply Finset.sum_eq_zero
            intro omega _
            let y0 := shortageCompleteOutput
              N nK mZ mX ell ellEV leakEC omega.1
                (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega)
            rw [Fintype.sum_eq_single y0]
            · rw [hfailure_col_zero j r omega y0 (s, Sum.inr k) hinput]
              simp
            · intro y hy
              have hrow : y0 ≠ y := Ne.symm hy
              have hz : reconstructionShortageKraus
                  N nK mZ mX ell ellEV leakEC pA pB j r omega y
                    (r, Sum.inr j) = 0 := by
                unfold reconstructionShortageKraus
                refine (Matrix.smul_apply _ _ _ _).trans ?_
                exact (congrArg (fun z : ℂ => _ • z)
                  (Matrix.single_apply_of_row_ne hrow
                    ((r, Sum.inr j) : ReconstructionInput N nK mZ mX ell ellEV leakEC)
                    (r, Sum.inr j) (1 : ℂ))).trans (smul_zero _)
              rw [hz]
              simp
          · intro t htr
            apply Finset.sum_eq_zero
            intro omega _
            apply Finset.sum_eq_zero
            intro y _
            have hcol : ((t, Sum.inr j) : ReconstructionInput
                N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
              intro h
              exact htr (congrArg Prod.fst h)
            rw [hfailure_col_zero j t omega y (r, Sum.inr j) hcol]
            simp
        · intro l hlj
          apply Finset.sum_eq_zero
          intro t _
          apply Finset.sum_eq_zero
          intro omega _
          apply Finset.sum_eq_zero
          intro y _
          have hcol : ((t, Sum.inr l) : ReconstructionInput
              N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
            intro h
            exact hlj (Sum.inr.inj (congrArg Prod.snd h))
          rw [hfailure_col_zero l t omega y (r, Sum.inr j) hcol]
          simp

/-- Certified one-outcome reconstruction instrument on the complete ambient control. -/
def reconstructionInstrument
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    Instrument (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionOutput N nK mZ mX ell ellEV leakEC) Unit where
  krausIndex _ := ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB
  kraus _ r := reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r
  complete := by
    simpa only [Fintype.sum_unique] using
      reconstructionKraus_complete N nK mZ mX ell ellEV leakEC pA pB


/-- The reconstruction input coordinate of one retained subset
-- `S`, announced permutation `pi`
and retained-tail output `u`. -/
def reconstructionSuccessInput (N nK mZ mX ell ellEV leakEC : ℕ)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    ReconstructionInput N nK mZ mX ell ellEV leakEC :=
  (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
    ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, u)), Sum.inl
      S)

/-- Along the successful output embedding of its control, a success Kraus matrix is the scaled
identity along the success input coordinates. -/
theorem reconstructionSuccessKraus_row
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
      S pi omega
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB
            S pi omega) u) =
      Pi.single (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC
        S pi u)
        (Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi))
            omega.1) := by
  funext x
  rw [Pi.single_apply]
  simp only [reconstructionSuccessKraus, reconstructionSuccessInput]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 := (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
      (selectedControlSupport_hasQuotas N nK mZ mX pA pB
        S pi omega)).injective h3
    have h5 : retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
        ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm x.1) = (pi, u) :=
      Prod.ext h2 h4.symm
    refine Prod.ext ?_ h1
    rw [← h5, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · rintro rfl
    refine ⟨rfl, ?_, ?_⟩ <;> rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- A success Kraus matrix vanishes on every output row outside the successful embedding of its
control. -/
theorem reconstructionSuccessKraus_row_eq_zero
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    {y : ReconstructionOutput N nK mZ mX ell ellEV leakEC}
    (hy : y ∉ Set.range (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
      (selectedControlSupport_hasQuotas N nK mZ mX pA pB
        S pi omega))) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
      S pi omega y = 0 := by
  funext x
  simp only [reconstructionSuccessKraus]
  rw [ite_eq_right]
  · rfl
  rintro ⟨-, -, h⟩
  exact hy ⟨_, h.symm⟩

/-- A shortage Kraus matrix is the scaled matrix unit from its retained input coordinate to the
metadata-bearing abort output of its control. -/
theorem reconstructionShortageKraus_eq_single
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (r : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega =
      Matrix.single
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
          (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
        (r, Sum.inr j)
        (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j)
          omega.1) := by
  unfold reconstructionShortageKraus
  refine (Matrix.smul_single _ _ _ _).trans ?_
  rw [smul_eq_mul, mul_one]

/-- The reconstruction channel is the sum of its supported success and shortage branches. -/
theorem reconstructionInstrument_channel_apply
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel rho =
      (∑ a : Σ S : Set.powersetCard (Fin N) (nK + mZ +
        mX),
          Σ pi : Equiv.Perm (Fin (nK + mZ + mX)),
            SelectedControlSupport N nK mZ mX pA pB S pi,
        Matrix.conjLinearMap (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
          a.1 a.2.1 a.2.2) rho) +
      ∑ j : Fin (nK + mZ + mX), ∑ omega : FailureControlSupport N nK mZ mX pA pB j,
        ∑ r, Matrix.conjLinearMap
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) rho := by
  have h0 : (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel =
      ∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
        Matrix.conjLinearMap (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) := by
    rw [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation,
      Quantum.Channels.krausMap_eq_sum_conjLinearMap]
    rfl
  rw [h0, LinearMap.sum_apply,
    Fintype.sum_sum_type (fun r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB =>
      Matrix.conjLinearMap (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) rho)]
  congr 1
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The reconstruction instrument's channel on its natural input and output registers. -/
noncomputable def reconstruction
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    Operation (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionOutput N nK mZ mX ell ellEV leakEC) :=
  (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel

/-- Reconstruction preserves trace and complete positivity. -/
theorem isChannel_reconstruction
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    IsChannel (reconstruction N nK mZ mX ell ellEV leakEC pA pB) :=
  (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).isChannel_channel

/-- The actual control lift is a channel whenever its retained operation is. -/
theorem isChannel_retainedControlLift (N n : ℕ) (Y : Type*) [Fintype Y]
    (Φ : Operation (Signals n) Y) (hΦ : IsChannel Φ) :
    IsChannel (retainedControlLift N n Y Φ) :=
  hΦ.mapTensorId.comp (isChannel_reindex _)

/-- Control lifting respects composition on the retained factor. -/
theorem retainedControlLift_comp (N n : ℕ) (Y Z : Type*)
    (Φ : Operation (Signals n) Y) (Ψ : Operation Y Z) :
    (mapTensorId Ψ (ComparisonControl N n)).comp (retainedControlLift N n Y Φ) =
      retainedControlLift N n Z (Ψ.comp Φ) := rfl

/-- Control lifting respects subtraction on the retained factor. -/
theorem retainedControlLift_sub (N n : ℕ) (Y : Type*) (Φ Ψ : Operation (Signals n) Y) :
    retainedControlLift N n Y (Φ - Ψ) =
      retainedControlLift N n Y Φ - retainedControlLift N n Y Ψ := rfl

/-- The actual control lift preserves adjoints whenever its retained operation does. -/
theorem retainedControlLift_preserves_conjTranspose (N n : ℕ) (Y : Type*)
    (Φ : Operation (Signals n) Y) (hΦ : ∀ M, Φ Mᴴ = (Φ M)ᴴ)
    (M : Op (ComparisonPreOutput N n)) :
    retainedControlLift N n Y Φ Mᴴ = (retainedControlLift N n Y Φ M)ᴴ := by
  change mapTensorId Φ _ (Matrix.reindex _ _ Mᴴ) = _
  rw [← Matrix.conjTranspose_reindex]
  exact mapTensorId_conjTranspose Φ hΦ _

/-- The complete control lift has coefficient one in the diamond bound. -/
theorem retainedControlLift_diamondNorm_le (N n : ℕ) (Y : Type*) [Fintype Y]
    (Φ : Operation (Signals n) Y) (hΦ : ∀ M, Φ Mᴴ = (Φ M)ᴴ) :
    diamondNorm (retainedControlLift N n Y Φ) ≤ diamondNorm Φ := by
  have he := diamondNorm_reindex (comparisonPreToRetainedControlEquiv N n).symm
    (Equiv.refl (Y × ComparisonControl N n)) (mapTensorId Φ (ComparisonControl N n))
  have hnorm : diamondNorm (retainedControlLift N n Y Φ) =
      diamondNorm (mapTensorId Φ (ComparisonControl N n)) := by
    simpa only [Equiv.symm_symm, Matrix.reindexLinearEquiv_refl_refl,
      LinearEquiv.refl_toLinearMap, LinearMap.id_comp, retainedControlLift] using he
  exact hnorm.le.trans (diamondNorm_mapTensorId_le Φ hΦ)

/-- The composite of `comparisonPre`, the retained real experiment in every control block and the
reconstruction channel. -/
noncomputable def retainedFactorizedReal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  let e := constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  ((Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
    (reconstruction N nK mZ mX ell ellEV leakEC pA pB)).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

/-- The composite of `comparisonPre`, the retained ideal experiment in every control block and the
reconstruction channel. -/
noncomputable def retainedFactorizedIdeal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  let e := constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  ((Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
    (reconstruction N nK mZ mX ell ellEV leakEC pA pB)).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

/-- The composite of `comparisonPre`, the retained real-minus-ideal difference in every control
block and the reconstruction channel. -/
noncomputable def retainedFactorizedDifference
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  let e := constructionSpaceEquiv pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  ((Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
    (reconstruction N nK mZ mX ell ellEV leakEC pA pB)).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
      (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

end QKD.BB84.Reduction
