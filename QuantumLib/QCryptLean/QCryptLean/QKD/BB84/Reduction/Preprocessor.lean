import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedBornRule
import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Preprocessor -/


open Quantum.Operators (Op)

open Quantum.Channels (
  IsChannel
  isChannel_reindex
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction
open LOCC

open Measurement Sampling

/-- Ambient classical control for a retained subset or a shortage label. -/
@[implicit_reducible] def ComparisonControl (N n : ℕ) : Type :=
  Set.powersetCard (Fin N) n ⊕ Fin n

deriving instance Fintype, DecidableEq for ComparisonControl

/-- The initial retained subset, used only to exhibit that the success control sector is
inhabited. -/
def comparisonInitialSubset {N n : ℕ} (hN : n ≤ N) :
    Set.powersetCard (Fin N) n :=
  Set.powersetCard.ofFinEmb n (Fin N) (Fin.castLEEmb hN)

/-- The ambient comparison control is inhabited for every `N,n`: use the empty retained subset
when `n = 0`, and the first shortage label when `n` is positive. -/
theorem nonempty_comparisonControl (N n : ℕ) :
    Nonempty (ComparisonControl N n) :=
  match n with
  | 0 => ⟨Sum.inl (comparisonInitialSubset (N := N) (n := 0) (Nat.zero_le N))⟩
  | k + 1 => ⟨Sum.inr (0 : Fin (k + 1))⟩

attribute [local instance] nonempty_comparisonControl

/-- Physical two-party bit-string input on `N` measured signal pairs. -/
abbrev ComparisonPreInput (N : ℕ) :=
  (Fin N → Bit) × (Fin N → Bit)

/-- Selected Alice/Bob strings together with the full ambient comparison control. -/
abbrev ComparisonPreOutput (N n : ℕ) :=
  (Bits n × Bits n) × ComparisonControl N n

/-- The all-zero selected input written on the shortage branch. -/
def comparisonZeroNativeInput (n : ℕ) : Bits n × Bits n := (0, 0)

/-- The actual physical schedule input expressed in its two bit-string coordinates. -/
def comparisonPreInputEquiv (N : ℕ) :
    ComparisonPreInput N ≃ (Measurement.weightedStreamSystem Unit N).total :=
  (weightedScheduleUnitInputEquiv N).symm

/-- Hidden success branch: a retained subset and one hidden representative of its actual
selected-input marginal instrument. -/
abbrev ComparisonPreSuccessIndex (N n : ℕ) :=
  Σ S : Set.powersetCard (Fin N) n,
    (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).krausIndex ()

/-- Hidden preprocessor branch.  The failure summand is empty when `n = 0`; for positive `n`,
only its label-zero slice has nonzero Kraus matrices. -/
abbrev ComparisonPreKrausIndex (N n : ℕ) :=
  ComparisonPreSuccessIndex N n ⊕ (Fin n × ComparisonPreInput N)

/-- Square-root amplitude for a successful retained-subset branch. -/
def comparisonPreSuccessScale
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  Instrument.weightedChoiceScale
      (selectionStatusLaw N nK mZ mX pA pB) true *
    Instrument.uniformChoiceScale
      (R := Set.powersetCard (Fin N) (nK + mZ + mX))

/-- Kraus matrix for one success subset and one hidden selected-marginal representative. -/
def comparisonPreSuccessKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (t : (selectedInputMarginalInstrument
      (increasingSubsetEmbedding S)).krausIndex ()) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  fun q a =>
    if q.2 = Sum.inl S then
      comparisonPreSuccessScale N nK mZ mX pA pB *
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).kraus () t
            q.1 a
    else 0

/-- Square-root amplitude of the shortage branch. -/
def comparisonPreFailureScale
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  Instrument.weightedChoiceScale
    (selectionStatusLaw N nK mZ mX pA pB) false

/-- Kraus matrix for one shortage label and one physical input basis coordinate.

Only label zero is active.  Since the label type is `Fin (nK + mZ + mX)`, the entire family is
empty at zero total quota. -/
def comparisonPreFailureKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (a : ComparisonPreInput N) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  if j.val = 0 then
    comparisonPreFailureScale N nK mZ mX pA pB •
      Matrix.single
        (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) a 1
  else 0

/-- Complete success-or-shortage Kraus family on the full ambient comparison output. -/
def comparisonPreKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (r : ComparisonPreKrausIndex N (nK + mZ + mX)) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  match r with
  | Sum.inl ⟨S, t⟩ => comparisonPreSuccessKraus N nK mZ mX pA pB S t
  | Sum.inr ⟨j, a⟩ => comparisonPreFailureKraus N nK mZ mX pA pB j a

/-- The ambient success and shortage Kraus blocks resolve the physical input identity.

The hypothesis supplies the finite success-sector inhabitant; no positivity, support, or
normalization premise on an input operator is used. -/
theorem comparisonPreKraus_complete
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    ∑ r : ComparisonPreKrausIndex N (nK + mZ + mX),
        (comparisonPreKraus N nK mZ mX pA pB r)ᴴ *
          comparisonPreKraus N nK mZ mX pA pB r = 1 := by
  classical
  let : Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
    ⟨comparisonInitialSubset hN⟩
  have hsuccessS
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (a b : ComparisonPreInput N) :
      ∑ t : (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).krausIndex (),
        ((comparisonPreSuccessKraus N nK mZ mX pA pB S t)ᴴ *
          comparisonPreSuccessKraus N nK mZ mX pA pB S t) a b =
        (star (comparisonPreSuccessScale N nK mZ mX pA pB) *
          comparisonPreSuccessScale N nK mZ mX pA pB) *
            (if a = b then 1 else 0) := by
    let I := selectedInputMarginalInstrument (increasingSubsetEmbedding S)
    let s := comparisonPreSuccessScale N nK mZ mX pA pB
    let e := Equiv.refl (Bits (nK + mZ + mX) × Bits (nK + mZ + mX))
    let control : ComparisonControl N (nK + mZ + mX) := Sum.inl S
    change (∑ t : I.krausIndex (), ∑ q : ComparisonPreOutput N (nK + mZ + mX),
      star (if q.2 = control then s * I.kraus () t (e q.1) a else 0) *
        (if q.2 = control then s * I.kraus () t (e q.1) b else 0)) = _
    simp only [Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, mul_one]
    have hcomplete := congrFun (congrFun I.complete a) b
    simp only [Fintype.sum_unique, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply] at hcomplete
    have hcomplete' :
        (∑ t : I.krausIndex (), ∑ x,
          star (I.kraus () t (e x) a) * I.kraus () t (e x) b) =
            if a = b then 1 else 0 := by
      calc
        _ = ∑ t : I.krausIndex (), ∑ x,
            star (I.kraus () t x a) * I.kraus () t x b := by
          apply Finset.sum_congr rfl
          intro t _
          exact e.sum_comp (fun x =>
            star (I.kraus () t x a) * I.kraus () t x b)
        _ = _ := hcomplete
    simp_rw [show ∀ (t : I.krausIndex ()) (x),
        star (s * I.kraus () t (e x) a) *
            (s * I.kraus () t (e x) b) =
          (star s * s) *
            (star (I.kraus () t (e x) a) * I.kraus () t (e x) b) by
            intros
            rw [star_mul']
            ac_rfl]
    calc
      _ = (star s * s) *
          (∑ t : I.krausIndex (), ∑ x,
            star (I.kraus () t (e x) a) * I.kraus () t (e x) b) := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum, Fintype.sum_prod_type]
      _ = _ := by
        rw [hcomplete', mul_ite, mul_one, mul_zero]
  have hfailure (a b : ComparisonPreInput N) :
      ∑ x : Fin (nK + mZ + mX) × ComparisonPreInput N,
        ((comparisonPreFailureKraus N nK mZ mX pA pB x.1 x.2)ᴴ *
          comparisonPreFailureKraus N nK mZ mX pA pB x.1 x.2) a b =
        (star (comparisonPreFailureScale N nK mZ mX pA pB) *
          comparisonPreFailureScale N nK mZ mX pA pB) *
            (if a = b then 1 else 0) := by
    let s := comparisonPreFailureScale N nK mZ mX pA pB
    have hactive (j : Fin (nK + mZ + mX)) (x : ComparisonPreInput N) :
        (comparisonPreFailureKraus N nK mZ mX pA pB j x)ᴴ *
            comparisonPreFailureKraus N nK mZ mX pA pB j x =
          if j.val = 0 then
            (star s * s) • Matrix.single x x (1 : ℂ)
          else 0 := by
      by_cases hj : j.val = 0
      · simp only [comparisonPreFailureKraus, hj, ite_eq_left]
        let z : ComparisonPreOutput N (nK + mZ + mX) :=
          (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j)
        change (s • Matrix.single z x (1 : ℂ))ᴴ * (s • Matrix.single z x 1) = _
        rw [Matrix.conjTranspose_smul]
        conv_lhs => tactic => exact Matrix.smul_mul _ _ _
        conv_lhs => arg 2; tactic => exact Matrix.mul_smul _ _ _
        rw [smul_smul, Matrix.conjTranspose_single, star_one,
          Matrix.single_mul_single_same, one_mul]
      · simp [comparisonPreFailureKraus, hj]
    simp_rw [hactive]
    rw [Fintype.sum_prod_type]
    by_cases hn : nK + mZ + mX = 0
    · have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      simp [s, comparisonPreFailureScale,
        Instrument.weightedChoiceScale,
        selectionStatusLaw_apply, selectionStatusWeight,
        selectionFailureMass_zero_quotas]
    · let j : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
      rw [Fintype.sum_eq_single j]
      · by_cases hab : a = b
        · subst b
          simp [j, s, Matrix.single_apply]
        · have hj : j.val = 0 := rfl
          rw [ite_eq_right hab]
          simp only [hj, ite_true, smul_single, smul_eq_mul, mul_one]
          simp only [mul_zero]
          apply Finset.sum_eq_zero
          intro x _
          simp only [Matrix.single_apply]
          split
          · rename_i hx
            exact (hab (hx.1.symm.trans hx.2)).elim
          · rfl
      · intro k hk
        have hkval : k.val ≠ 0 := by
          intro hzero
          apply hk
          apply Fin.ext
          simpa [j] using hzero
        simp [hkval]
  rw [Fintype.sum_sum_type]
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply]
  rw [Fintype.sum_sigma]
  simp only [comparisonPreKraus]
  simp_rw [hsuccessS]
  rw [hfailure]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [comparisonPreSuccessScale, comparisonPreFailureScale]
    rw [show
        star (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true *
            Instrument.uniformChoiceScale) *
            (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true *
            Instrument.uniformChoiceScale) =
          (star (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true) *
            Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true) *
          (star (Instrument.uniformChoiceScale
              (R := Set.powersetCard (Fin N) (nK + mZ + mX))) *
            Instrument.uniformChoiceScale) by
              rw [star_mul']
              ring]
    rw [Instrument.weightedChoiceScale_star_mul,
      Instrument.uniformChoiceScale_star_mul,
      Instrument.weightedChoiceScale_star_mul]
    rw [show (Fintype.card
          (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ) *
          (((selectionStatusLaw N nK mZ mX pA pB true).toReal : ℂ) *
            (Fintype.card
              (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ)⁻¹) =
          ((selectionStatusLaw N nK mZ mX pA pB true).toReal : ℂ) by
            rw [mul_left_comm, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
              mul_one]]
    have hprob := Instrument.weightedChoiceProbability_sum
      (selectionStatusLaw N nK mZ mX pA pB)
    rw [Fintype.sum_bool] at hprob
    simpa only [add_comm] using hprob
  · simp [hab]

/-- Certified one-outcome preprocessor instrument on the complete ambient output space. -/
def comparisonPreInstrument
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    Instrument (ComparisonPreInput N)
      (ComparisonPreOutput N (nK + mZ + mX)) Unit where
  krausIndex _ := ComparisonPreKrausIndex N (nK + mZ + mX)
  kraus _ r := comparisonPreKraus N nK mZ mX pA pB r
  complete := by
    simpa only [Fintype.sum_unique] using
      comparisonPreKraus_complete N nK mZ mX pA pB hN

/-- Complex success coefficient, including the uniform retained-subset probability. -/
def comparisonPreSuccessCoefficient
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  ((selectionSuccessMass N nK mZ mX pA pB).toReal : ℂ) *
    (Fintype.card
      (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ)⁻¹

/-- Complex shortage coefficient. -/
def comparisonPreFailureCoefficient
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  ((selectionFailureMass N nK mZ mX pA pB).toReal : ℂ)

/-- The squared modulus of the success amplitude is the success coefficient: the selection-status
weight of success times the uniform retained-subset probability. -/
private lemma comparisonPreSuccessScale_mul_star
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) [Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX))] :
    comparisonPreSuccessScale N nK mZ mX pA pB *
        star (comparisonPreSuccessScale N nK mZ mX pA pB) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB := by
  calc comparisonPreSuccessScale N nK mZ mX pA pB *
          star (comparisonPreSuccessScale N nK mZ mX pA pB)
      = (star (Instrument.weightedChoiceScale (selectionStatusLaw N nK mZ mX pA pB) true) *
            Instrument.weightedChoiceScale (selectionStatusLaw N nK mZ mX pA pB) true) *
          (star (Instrument.uniformChoiceScale (R := Set.powersetCard (Fin N) (nK + mZ + mX))) *
            Instrument.uniformChoiceScale) := by
        rw [comparisonPreSuccessScale, star_mul']; ring
    _ = _ := by
        rw [Instrument.weightedChoiceScale_star_mul, Instrument.uniformChoiceScale_star_mul,
          selectionStatusLaw_apply]
        rfl

/-- Exact ambient entry formula for the comparison preprocessor.

Success keeps the subset-dependent selected marginal.  Shortage writes only the zero native input
and label zero.  Distinct success subsets, distinct shortage labels, and success/shortage cross
blocks are zero. -/
def comparisonPreEntry
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (rho : Op (ComparisonPreInput N))
    (q q' : ComparisonPreOutput N (nK + mZ + mX)) : ℂ :=
  match q.2, q'.2 with
  | Sum.inl S, Sum.inl S' =>
      if S = S' then
        comparisonPreSuccessCoefficient N nK mZ mX pA pB *
          (selectedInputMarginalInstrument
            (increasingSubsetEmbedding S)).channel rho
              q.1
              q'.1
      else 0
  | Sum.inr j, Sum.inr j' =>
      if j.val = 0 ∧ j'.val = 0 ∧
          q.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧
          q'.1 = comparisonZeroNativeInput (nK + mZ + mX) then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- Exact evaluation of the certified preprocessor on every complex operator and every pair of
ambient output coordinates. -/
theorem comparisonPreInstrument_channel_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N)
    (rho : Op (ComparisonPreInput N))
    (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
    (comparisonPreInstrument N nK mZ mX pA pB hN).channel rho q q' =
      comparisonPreEntry N nK mZ mX pA pB rho q q' := by
  classical
  let : Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
    ⟨comparisonInitialSubset hN⟩
  have hsuccess
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
      ∑ t : (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).krausIndex (),
        (comparisonPreSuccessKraus N nK mZ mX pA pB S t * rho *
          (comparisonPreSuccessKraus N nK mZ mX pA pB S t)ᴴ) q q' =
        if q.2 = Sum.inl S ∧ q'.2 = Sum.inl S then
          comparisonPreSuccessCoefficient N nK mZ mX pA pB *
            (selectedInputMarginalInstrument
              (increasingSubsetEmbedding S)).channel rho
                q.1
                q'.1
        else 0 := by
    rcases q with ⟨x, c⟩
    rcases q' with ⟨x', c'⟩
    by_cases hc : c = Sum.inl S
    · subst c
      by_cases hc' : c' = Sum.inl S
      · subst c'
        let I := selectedInputMarginalInstrument (increasingSubsetEmbedding S)
        let s := comparisonPreSuccessScale N nK mZ mX pA pB
        let e := Equiv.refl (Bits (nK + mZ + mX) × Bits (nK + mZ + mX))
        have hentry (t : I.krausIndex ()) (y) (a : ComparisonPreInput N) :
            comparisonPreSuccessKraus N nK mZ mX pA pB S t (y, Sum.inl S) a =
              s * I.kraus () t (e y) a := ite_eq_left rfl
        refine Eq.trans ?_ (ite_eq_left ⟨rfl, rfl⟩).symm
        change (∑ t : I.krausIndex (), ∑ b : ComparisonPreInput N,
          (∑ a : ComparisonPreInput N,
            comparisonPreSuccessKraus N nK mZ mX pA pB S t (x, Sum.inl S) a * rho a b) *
            star (comparisonPreSuccessKraus N nK mZ mX pA pB S t (x', Sum.inl S) b)) = _
        simp_rw [hentry]
        refine Eq.trans ?_ (congrArg (fun z : ℂ => z * I.channel rho (e x) (e x'))
          (comparisonPreSuccessScale_mul_star N nK mZ mX pA pB))
        simp only [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation,
          krausMap_eq_sum_conjLinearMap,
          LinearMap.sum_apply, Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
        change (∑ t : I.krausIndex (), ∑ b : ComparisonPreInput N,
          (∑ a : ComparisonPreInput N, s * I.kraus () t (e x) a * rho a b) *
            star (s * I.kraus () t (e x') b)) =
          (s * star s) * (∑ t : I.krausIndex (), ∑ b : ComparisonPreInput N,
            (∑ a : ComparisonPreInput N, I.kraus () t (e x) a * rho a b) *
              star (I.kraus () t (e x') b))
        simp only [star_mul', Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => by ring
      · simp only [mul_apply, comparisonPreSuccessKraus, ↓reduceIte, conjTranspose_apply, hc',
          star_zero, mul_zero, Finset.sum_const_zero, and_false]
    · simp only [mul_apply, comparisonPreSuccessKraus, hc, ↓reduceIte, zero_mul,
        Finset.sum_const_zero, false_and]
  have hfailure
      (j : Fin (nK + mZ + mX)) (a : ComparisonPreInput N)
      (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
      (comparisonPreFailureKraus N nK mZ mX pA pB j a * rho *
        (comparisonPreFailureKraus N nK mZ mX pA pB j a)ᴴ) q q' =
        if j.val = 0 ∧
            (q.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q.2 = Sum.inr j) ∧
            (q'.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q'.2 = Sum.inr j) then
          comparisonPreFailureCoefficient N nK mZ mX pA pB * rho a a
        else 0 := by
    have hscale :
        comparisonPreFailureScale N nK mZ mX pA pB *
            star (comparisonPreFailureScale N nK mZ mX pA pB) =
          comparisonPreFailureCoefficient N nK mZ mX pA pB := by
      rw [comparisonPreFailureScale]
      rw [mul_comm, Instrument.weightedChoiceScale_star_mul,
        selectionStatusLaw_apply]
      rfl
    by_cases hj : j.val = 0
    · -- `(c E_{ia}) ρ (c E_{ia})ᴴ = E_{ii} (c ρ_aa c̄)` with `i = (0, inr j)`
      rw [comparisonPreFailureKraus, ite_eq_left hj]
      have hsingle := Matrix.smul_single (comparisonPreFailureScale N nK mZ mX pA pB)
        (comparisonZeroNativeInput (nK + mZ + mX), (Sum.inr j : ComparisonControl N _)) a (1 : ℂ)
      simp only [smul_eq_mul, mul_one] at hsingle
      refine (congrArg (fun K : Matrix (ComparisonPreOutput N (nK + mZ + mX))
          (ComparisonPreInput N) ℂ => (K * rho * Kᴴ) q q') hsingle).trans ?_
      refine (congrArg (fun M : Matrix (ComparisonPreInput N)
          (ComparisonPreOutput N (nK + mZ + mX)) ℂ =>
          (Matrix.single (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) a
            (comparisonPreFailureScale N nK mZ mX pA pB) * rho * M) q q')
          (Matrix.conjTranspose_single _ _ _)).trans ?_
      refine (congrFun (congrFun (Matrix.single_mul_mul_single _ _ _ _ _ rho _) q) q').trans ?_
      refine (Matrix.single_apply
        ((comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) :
          ComparisonPreOutput N (nK + mZ + mX)) _ _ q q').trans ?_
      let z : ComparisonPreOutput N (nK + mZ + mX) :=
        (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j)
      by_cases hq : z = q ∧ z = q'
      · have hcoords := And.intro hj
          (And.intro (Prod.mk.inj hq.1.symm) (Prod.mk.inj hq.2.symm))
        exact (ite_eq_left hq).trans ((mul_right_comm _ _ _).trans
          ((congrArg (fun s : ℂ => s * rho a a) hscale).trans (ite_eq_left hcoords).symm))
      · have hcoords : ¬(j.val = 0 ∧
            (q.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q.2 = Sum.inr j) ∧
            (q'.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q'.2 = Sum.inr j)) := by
          rintro ⟨_, hx, hx'⟩
          exact hq ⟨(Prod.ext hx.1 hx.2).symm, (Prod.ext hx'.1 hx'.2).symm⟩
        exact (ite_eq_right hq).trans (ite_eq_right hcoords).symm
    · simp only [comparisonPreFailureKraus, hj, ↓reduceIte, Matrix.zero_mul, conjTranspose_zero,
        Matrix.mul_zero, Matrix.zero_apply, false_and]
  rw [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation]
  simp only [Quantum.Channels.krausMap, LinearMap.coe_mk, AddHom.coe_mk]
  change
    (∑ r : ComparisonPreKrausIndex N (nK + mZ + mX),
      comparisonPreKraus N nK mZ mX pA pB r * rho *
        (comparisonPreKraus N nK mZ mX pA pB r)ᴴ) q q' = _
  rw [Matrix.sum_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [comparisonPreKraus]
  simp_rw [hsuccess]
  rw [Fintype.sum_prod_type]
  simp_rw [hfailure]
  rcases q with ⟨x, c⟩
  rcases q' with ⟨x', c'⟩
  cases c <;> cases c'
  all_goals simp only [comparisonPreEntry]
  case inl.inl S S' =>
    simp only [reduceCtorEq, and_false, and_self, ↓reduceIte,
      Finset.sum_const_zero, add_zero]
    by_cases hSS : S = S'
    · subst S'
      rw [ite_eq_left rfl]
      rw [Fintype.sum_eq_single S]
      · exact ite_eq_left ⟨rfl, rfl⟩
      · intro S hS
        simp only [ite_eq_right_iff]
        intro h
        exfalso
        exact hS (Sum.inl.inj h.1).symm
    · rw [ite_eq_right hSS]
      apply Finset.sum_eq_zero
      intro S _
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hSS
      exact (Sum.inl.inj h.1).trans (Sum.inl.inj h.2).symm
  case inl.inr => simp
  case inr.inl => simp
  case inr.inr j j' =>
    simp only [reduceCtorEq, and_self, ↓reduceIte, Finset.sum_const_zero,
      Finset.sum_ite_irrel, zero_add]
    by_cases hcond :
        j.val = 0 ∧ j'.val = 0 ∧
          x = comparisonZeroNativeInput (nK + mZ + mX) ∧
          x' = comparisonZeroNativeInput (nK + mZ + mX)
    · rw [ite_eq_left hcond]
      have hj : j = j' := by
        apply Fin.ext
        exact hcond.1.trans hcond.2.1.symm
      subst j'
      rw [Fintype.sum_eq_single j]
      · have hbranch :
            j.val = 0 ∧
              (x = comparisonZeroNativeInput (nK + mZ + mX) ∧
                (Sum.inr j : ComparisonControl N (nK + mZ + mX)) = Sum.inr j) ∧
              x' = comparisonZeroNativeInput (nK + mZ + mX) ∧
                (Sum.inr j : ComparisonControl N (nK + mZ + mX)) = Sum.inr j :=
          ⟨hcond.1, ⟨hcond.2.2.1, rfl⟩, hcond.2.2.2, rfl⟩
        refine (ite_eq_left hbranch).trans ?_
        rw [Finset.mul_sum]
      · intro k hne
        simp only [ite_eq_right_iff]
        intro h
        exact (hne (Sum.inr.inj h.2.1.2).symm).elim
    · rw [ite_eq_right hcond]
      apply Finset.sum_eq_zero
      intro k _
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hcond
      refine ⟨?_, ?_, h.2.1.1, h.2.2.1⟩
      · rw [Sum.inr.inj h.2.1.2]
        exact h.1
      · rw [Sum.inr.inj h.2.2.2]
        exact h.1

/-- Success-block evaluation, with the selected marginal depending on the retained subset. -/
theorem comparisonPreInstrument_success_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N)
    (rho : Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (x x' : Bits (nK + mZ + mX) × Bits (nK + mZ + mX)) :
    (comparisonPreInstrument N nK mZ mX pA pB hN).channel rho
        (x, Sum.inl S) (x', Sum.inl S) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB *
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            x
            x' := by
  rw [comparisonPreInstrument_channel_apply]
  simp [comparisonPreEntry]

/-- The ambient comparison preprocessor on the physical input register. -/
def comparisonPre
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    Op (Measurement.weightedStreamSystem Unit N).total →ₗ[ℂ]
      Op (ComparisonPreOutput N (nK + mZ + mX)) :=
  (comparisonPreInstrument N nK mZ mX pA pB hN).channel.comp
    (Matrix.reindexLinearEquiv ℂ ℂ
      (weightedScheduleUnitInputEquiv N) (weightedScheduleUnitInputEquiv N)).toLinearMap

/-- The ambient comparison preprocessor is a channel. -/
theorem isChannel_comparisonPre
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    IsChannel (comparisonPre N nK mZ mX pA pB hN) :=
  (comparisonPreInstrument N nK mZ mX pA pB hN).isChannel_channel.comp
    (isChannel_reindex (weightedScheduleUnitInputEquiv N))

end QKD.BB84.Reduction
