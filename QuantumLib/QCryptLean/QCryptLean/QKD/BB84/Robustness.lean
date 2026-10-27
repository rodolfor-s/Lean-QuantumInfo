import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.Acceptance
import QCryptLean.QKD.BB84.Acceptance
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.Completeness
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Measurement.HonestSource
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.Measurement.ProductInput
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Model.ClassicalSemantics
import QCryptLean.QKD.BB84.Model.RealChannelEntrywise
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.OutputLayout
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-!
# Robustness of the measure-first BB84 experiment on the honest channel

`protocol_acceptProbability_productSource` gives the shared algebraic identity from trace one
and the matched Born tables. Its canonical honest-source specialization holds for every real
`q`; that particular source is positive on `0 ≤ q ≤ 1/2`. The selected classical weights and
source tail estimates are valid on `0 ≤ q ≤ 1`.

`Parameters.HonestBand` records the margin, the shrunk acceptance window, and decoding guarantee.
For the broader physical class `Measurement.HonestOperation`, positivity derives `q ∈ [0,1]`.
The acceptance and abort transfer lemmas identify its probabilities with the canonical source
expressions, so the same bound applies without separate rate hypotheses.

The honest run of the configured experiment `Parameters.protocol` sends `rounds` honest pairs at
QBER `q` (`Measurement.honestSource`), prepared before any basis choice.  Its probability of
aborting is what Portmann--Renner call the robustness of the protocol ("For every `q`, the protocol
has a probability of aborting, `δ`, which is called the robustness", arXiv:2102.00021,
`qkd.tex:845`--`:850`).  This module computes it exactly and bounds it.

## The conditioning identity

`Parameters.acceptProbability_honestSource` states, with no hypothesis at all,

`acceptance(honestSource q) = selectionSuccessMass · honestTailAcceptance q`.

The first factor is the mass of the public controls meeting the quotas; it depends only on the two
basis laws and the quotas.  The second is the probability that the real retained classical tail
accepts the honest selected law `honestRawInput` — `sifted` independent rounds whose two bits agree
with probability `1 - q` — and depends only on the tail and on `q`.  The identity holds because the
program draws its public controls without looking at the prepared input, and at every
quota-feasible control the selected rounds are matched and carry that same law, whatever their role
and whatever the control
(`Measurement.selectionProgram_honestSource_success`).  Per control, the
run announces `ω` and accepts with probability `rawControlLaw ω` times the tail's honest acceptance
(`completeContinuation_acceptWeight_honestSource`), while controls failing a quota end in the
key-free abort leaf.  Nothing is normalized: controls of zero mass contribute zero, and if no
control meets the quotas the experiment aborts with probability one.

Since every run either accepts or aborts (`QKD.Protocol.acceptProbability_add_abortProbability`),

`abort(honestSource q) = selectionFailureMass + selectionSuccessMass · (1 - honestTailAcceptance q)`

(`Parameters.abortProbability_honestSource`), with the quota-failure mass of
`Sampling.selectionFailureMass` explicit.

## The honest-abort bound

Let the honest QBER `q` lie within `tolerance - η` of the accept centre `errorRate`, for a margin
`η > 0`, and let the error-correction scheme decode the honest key-error model at `q` with failure
mass `εEC`.  Then the completeness analysis `one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band` —
two Hoeffding tails at
margin `η` plus `εEC` — bounds the tail's rejection
(`Parameters.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance`), so

`abort(honestSource q) ≤ selectionFailureMass + hoeffdingTestAbortBound zTests xTests η εEC`

(`Parameters.abortProbability_honestSource_le_of_mem_band`).  At the accept centre itself,
`q = errorRate` and `η = tolerance`, this is `Parameters.abortProbability_honestSource_le_self`.  No
nonemptiness hypothesis on the test blocks is needed: an experiment with an empty test block never
accepts (`Parameters.acceptProbability_eq_zero_of_testBlock_empty`), and its budget is then at least
`2` (`two_le_hoeffdingTestAbortBound_of_empty`), so the bound holds and is vacuous there.  The
relative-entropy counterpart
`Parameters.one_sub_testAbortBound_le_honestTailAcceptance` prices the two
PE-band failures at the Bernoulli KL Chernoff rate (Cover--Thomas, *Elements of Information Theory*,
§11.1) and therefore needs no margin — only the strict window `Q - δ < q < Q + δ`.  A
quantitative bound on the quota-failure mass is a separate classical statement about the two basis
laws; combined with it, this bounds the robustness of the physical experiment.

## What is not claimed

The abort probability is neither the composable robustness distance `eq:robustness` of
Portmann--Renner (`qkd.tex:854`) nor a key-rate statement: an accepting run may still hold a short
or useless key, and nothing here compares the real system with an ideal resource.  Their
`lem:robustness` (`qkd.tex:861`--`:868`) bounds that distance by the soundness distance when the
ideal resource aborts with exactly the protocol's honest abort probability; this module computes
that probability, but the lemma itself is not formalized here.  The two published security bounds
about the same `Parameters.protocol` are in `QCryptLean.QKD.BB84.Security`; this module
neither uses nor changes them.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal

noncomputable section

namespace QKD.BB84
open LOCC
open QKD.BB84
open QKD.BB84.Reduction

open LOCC.TwoParty
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.FiniteKey
open QKD.BB84.Model

/-! ## The honest selected law -/

/-- Product weights on `n` retained rounds, with each pair weighted by `honestPairWeight q`.
They sum to one for every `q` and are nonnegative on `0 ≤ q ≤ 1`. -/
def honestRawWeight (n : ℕ) (q : ℝ) (x : (FinalStage.rawSystem n).total) : ℝ :=
  ∏ k, honestPairWeight q (x .alice k) (x .bob k)

/-- Diagonal operator of the honest selected weights; a classical state on `0 ≤ q ≤ 1`. -/
def honestRawInput (n : ℕ) (q : ℝ) : Op (FinalStage.rawSystem n).total :=
  Matrix.diagonal fun x => (honestRawWeight n q x : ℂ)

/-- Raw registers are pairs of bit strings. -/
def rawBitStringsEquiv (n : ℕ) :
    (Fin n → Bit) × (Fin n → Bit) ≃ (FinalStage.rawSystem n).total :=
  (TwoParty.pairEquiv _ _).symm

/-- In bit-string coordinates the honest selected law is the round product of the honest
matched-round law. -/
theorem honestRawWeight_rawBitStringsEquiv (n : ℕ) (q : ℝ) (u : (Fin n → Bit) × (Fin n → Bit)) :
    honestRawWeight n q (rawBitStringsEquiv n u) = ∏ k, honestPairWeight q (u.1 k) (u.2 k) := by
  rfl

/-- The honest selected law is normalized, for every `q`. -/
theorem sum_honestRawWeight (n : ℕ) (q : ℝ) : ∑ x, honestRawWeight n q x = 1 := by
  rw [← (rawBitStringsEquiv n).sum_comp]
  simp_rw [honestRawWeight_rawBitStringsEquiv]
  rw [sum_pairStrings_prod (fun _ c => honestPairWeight q c.1 c.2)]
  simp only [Fintype.sum_prod_type, sum_honestPairWeight, Finset.prod_const_one]

/-- The honest selected law is nonnegative on `0 ≤ q ≤ 1`. -/
theorem honestRawWeight_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (x : (FinalStage.rawSystem n).total) : 0 ≤ honestRawWeight n q x :=
  Finset.prod_nonneg fun _ _ => honestPairWeight_nonneg hq0 hq1 _ _

/-! ## The real tail on the honest selected law -/

/-- Acceptance weight of the real retained tail on `honestRawInput n q`. -/
def honestTailAcceptance (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q q : ℝ) : ℝ :=
  (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.acceptWeight
    ((Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)).toLinearMap
      ((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote (honestRawInput n q)))

/-- The honest acceptance is the honest average of the tail's seed-averaged acceptance. -/
theorem honestTailAcceptance_eq (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q q : ℝ) :
    honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q =
      ∑ x, rawClassicalTailAcceptFraction n m ℓ ℓEV peSel xSel leakEC ec δ Q x *
        honestRawWeight n q x := by
  rw [honestTailAcceptance, rawClassicalTail_acceptWeight_apply]
  simp [honestRawInput]

/-- The honest acceptance is nonnegative on `0 ≤ q ≤ 1`. -/
theorem honestTailAcceptance_nonneg (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q := by
  rw [honestTailAcceptance_eq]
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (rawClassicalTailAcceptFraction_nonneg _ _ _ _ _ _ _ _ _ _ x)
      (honestRawWeight_nonneg hq0 hq1 x)

/-- The honest acceptance is at most one on `0 ≤ q ≤ 1`. -/
theorem honestTailAcceptance_le_one (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q ≤ 1 := by
  rw [honestTailAcceptance_eq, ← sum_honestRawWeight n q]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_of_le_one_left (honestRawWeight_nonneg hq0 hq1 x)
      (rawClassicalTailAcceptFraction_le_one _ _ _ _ _ _ _ _ _ _ x)

/-- Raw registers of `n` retained rounds as round-outcome strings: round `k` carries Alice's bit
high and Bob's bit low, the convention of `QKD.BB84.Model.jointOutcome`. -/
def rawJointOutcomeEquiv (n : ℕ) : (FinalStage.rawSystem n).total ≃ Signals n :=
  (rawBitStringsEquiv n).symm.trans (Quantum.Symmetry.pairFunctions Bit Bit n).symm

/-- `rawJointOutcomeEquiv` is `QKD.BB84.Model.jointOutcome` of the two raw registers. -/
theorem rawJointOutcomeEquiv_apply (n : ℕ) (x : (FinalStage.rawSystem n).total) :
    rawJointOutcomeEquiv n x = QKD.BB84.Model.jointOutcome n
      (x .alice) (x .bob) := by
  funext k
  simp [rawJointOutcomeEquiv, Quantum.Symmetry.pairFunctions, rawBitStringsEquiv,
    QKD.BB84.Model.jointOutcome,
    TwoParty.pairEquiv]

/-- The honest selected law is the honest outcome weight of the completeness analysis. -/
theorem honestRawWeight_eq_honestOutcomeWeight (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool)
    (x : (FinalStage.rawSystem n).total) :
    honestRawWeight n q x = honestOutcomeWeight n q peSel xSel (rawJointOutcomeEquiv n x) := by
  rw [honestOutcomeWeight_eq_prod, rawJointOutcomeEquiv_apply, honestRawWeight]
  rfl

/-- The real tail's flag, with Alice's verification tag and syndrome written out. -/
theorem rawClassicalTailFlag_eq (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
    rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st =
      (Equiv.boolNot.trans finTwoEquiv.symm)
        (QKD.BB84.acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
        (fun j => x .alice (peRoundIdx (m := m) peSel j))
        (fun j => x .bob (peRoundIdx (m := m) peSel j))
        st.2 (verificationTag n ℓEV peSel st.2 (QKD.BB84.aliceRawKey n peSel (x .alice)))
        (ec.syndrome (QKD.BB84.aliceRawKey n peSel (x .alice))) (x .bob)) := by
  simp [rawClassicalTailFlag, rawClassicalTailDataOf, QKD.BB84.tagAndSyndrome]

/-- The nonempty-block case of the honest-tail-acceptance bound: any lower bound `hcompl` on the
accepted honest outcome mass, as supplied by either completeness statement
(`one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band` at the Hoeffding rate or
`one_sub_testAbortBound_le_sum_of_strict_band`
at the relative-entropy rate), transfers to the real tail. -/
private theorem one_sub_le_honestTailAcceptance_of_nonempty
    (n m ℓ ℓEV leakEC : ℕ) (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (q Q δ c : ℝ) (hcount : KeyCount n m peSel)
    (hZ : 0 < siftedZTestSampleSize peSel xSel)
    (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hcompl : ∀ st : KeyHashSeedPairEV n ℓ ℓEV peSel,
      1 - c ≤ ∑ ω : Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
         then honestOutcomeWeight n q peSel xSel ω else 0)) :
    1 - c ≤ honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q := by
  -- The Z-sample size is the cardinality of a subset of `Fin n`, so `hZ` gives `0 < n`.
  have hn0 : 0 < n := by
    have hle : (Finset.univ.filter (fun i : Fin n => peSel i = true ∧ xSel i = false)).card ≤ n :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
    exact lt_of_lt_of_le hZ hle
  have : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  have hq1 : q ≤ 1 := hq
  have hflag (x : (FinalStage.rawSystem n).total) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
      rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st = 0 ↔
        siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 (rawJointOutcomeEquiv n x) =
          true := by
    rw [rawClassicalTailFlag_eq]
    have hvalue := QKD.BB84.Model.acceptFlag_eq n m ℓEV peSel xSel leakEC ec δ Q hcount
      st.2 (x .alice) (x .bob)
    rw [hvalue, ← rawJointOutcomeEquiv_apply]
    split_ifs with hp <;> simp [hp, finTwoEquiv]
  have hper (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
      1 - c ≤
        ∑ x, if rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st = 0 then
          honestRawWeight n q x else 0 := by
    refine (hcompl st).trans ?_
    rw [← (rawJointOutcomeEquiv n).sum_comp]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← honestRawWeight_eq_honestOutcomeWeight n q peSel xSel x]
    by_cases hp : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (rawJointOutcomeEquiv n x) = true
    · rw [ite_eq_left ((hflag x st).mpr hp)]
      split_ifs
      · exact le_rfl
      · exact honestRawWeight_nonneg hq0 hq1 x
    · rw [ite_eq_right (fun h => hp h.1), ite_eq_right (fun h => hp ((hflag x st).mp h))]
  have hsplit : honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹ *
        ∑ st, ∑ x, if rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st = 0 then
          honestRawWeight n q x else 0 := by
    rw [honestTailAcceptance_eq, Finset.sum_comm, Finset.mul_sum]
    simp only [rawClassicalTailAcceptFraction, Finset.mul_sum, Finset.sum_mul, mul_assoc,
      boole_mul]
  have hC : (0 : ℝ) < Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) := by
    exact_mod_cast Fintype.card_pos
  rw [hsplit, inv_mul_eq_div, le_div_iff₀ hC]
  calc
    _ = ∑ _st : KeyHashSeedPairEV n ℓ ℓEV peSel, (1 - c) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum fun st _ => hper st

/-- **The honest acceptance of the real tail is at least `1 - ε_c`, at every honest QBER inside the
accept window.**

The accept test has centre `Q` and half-width `δ`; the honest QBER `q` lies in the window shrunk by
a margin `η > 0`; and the error-correction scheme decodes the honest key-error model at QBER `q`
with failure mass `εEC`.  When both test blocks are nonempty, at every announced seed pair the real
tail's flag is the accept test of the round-outcome string (`QKD.BB84.Model.acceptFlag_eq`,
which needs the key-count hypothesis `hcount`), the honest selected law is the honest outcome
weight, and `one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band` bounds the accepted mass.  When a
test block is empty
the tail never accepts, but the budget is then at least `2`
(`two_le_hoeffdingTestAbortBound_of_empty`), so no nonemptiness hypothesis is needed. -/
theorem one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance
    (n m ℓ ℓEV leakEC : ℕ) (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (q Q δ η εEC : ℝ) (hcount : KeyCount n m peSel)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) (hη : 0 < η) (hband : |q - Q| ≤ δ - η)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n q peSel xSel) εEC) :
    1 - hoeffdingTestAbortBound (siftedZTestSampleSize peSel xSel)
        (siftedXTestSampleSize peSel xSel) η εEC ≤
      honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q := by
  by_cases hblocks : 0 < siftedZTestSampleSize peSel xSel ∧
      0 < siftedXTestSampleSize peSel xSel
  · exact one_sub_le_honestTailAcceptance_of_nonempty n m ℓ ℓEV leakEC peSel xSel ec q Q δ
      (hoeffdingTestAbortBound (siftedZTestSampleSize peSel xSel)
        (siftedXTestSampleSize peSel xSel) η εEC) hcount hblocks.1 hq0 hq
      fun st => one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band n ℓEV leakEC peSel xSel ec st.2
        q Q δ η εEC
        hblocks.1 hblocks.2 hq0 hq hη hband hDecode
  · have hq1 : q ≤ 1 := hq
    have hε := nonneg_of_decodesWhp_honestKeyErrWeight hq0 hq1 hDecode
    have h2 := two_le_hoeffdingTestAbortBound_of_empty (siftedZTestSampleSize peSel xSel)
      (siftedXTestSampleSize peSel xSel) η εEC hε (by omega)
    have hT := honestTailAcceptance_nonneg n m ℓ ℓEV peSel xSel leakEC ec δ Q hq0 hq1
    linarith

/-- **The honest acceptance of the real tail is at least `1 - ε_c^KL`** at every honest QBER
strictly inside the accept window (`Q - δ < q < Q + δ`), the relative-entropy counterpart of
`QKD.BB84.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance`: the two
PE-band failures are priced by the Bernoulli KL divergence
(`one_sub_testAbortBound_le_sum_of_strict_band`;
Chernoff bound, Cover--Thomas, *Elements of Information Theory*, §11.1), so no margin inside the
window is needed.  An empty test block again costs
nothing: the budget is then at least two (`two_le_testAbortBound_of_empty`). -/
theorem one_sub_testAbortBound_le_honestTailAcceptance
    (n m ℓ ℓEV leakEC : ℕ) (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (q Q δ εEC : ℝ) (hcount : KeyCount n m peSel)
    (hq0 : 0 < q) (hq1 : q < 1) (hlo : Q - δ < q) (hhi : q < Q + δ)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n q peSel xSel) εEC) :
    1 - testAbortBound (siftedZTestSampleSize peSel xSel)
        (siftedXTestSampleSize peSel xSel) Q δ q εEC ≤
      honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q q := by
  by_cases hblocks : 0 < siftedZTestSampleSize peSel xSel ∧
      0 < siftedXTestSampleSize peSel xSel
  · have : NeZero n := ⟨by
      rintro rfl
      simp [siftedZTestSampleSize] at hblocks⟩
    exact one_sub_le_honestTailAcceptance_of_nonempty n m ℓ ℓEV leakEC peSel xSel ec q Q δ
      (testAbortBound (siftedZTestSampleSize peSel xSel)
        (siftedXTestSampleSize peSel xSel) Q δ q εEC) hcount hblocks.1 hq0.le
      hq1.le fun st =>
      one_sub_testAbortBound_le_sum_of_strict_band n ℓEV leakEC peSel xSel ec st.2 q Q δ εEC
        hblocks.1
        hblocks.2 hq0 hq1 hlo hhi hDecode
  · have hε := nonneg_of_decodesWhp_honestKeyErrWeight hq0.le hq1.le hDecode
    have h2 := two_le_testAbortBound_of_empty
      (siftedZTestSampleSize peSel xSel) (siftedXTestSampleSize peSel xSel) Q δ q εEC hε
      (by omega)
    have hT := honestTailAcceptance_nonneg n m ℓ ℓEV peSel xSel leakEC ec δ Q hq0.le hq1.le
    linarith

/-- **The honest acceptance of the real tail is at least `1 - ε_c`**, when the accept test is
centred at the honest QBER: the case `q = Q`, `η = δ` of
`QKD.BB84.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance`. -/
theorem one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance_self (n m ℓ ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (Q δ εEC : ℝ)
    (hcount : KeyCount n m peSel)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 1) (hδ : 0 < δ)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n Q peSel xSel) εEC) :
    1 - hoeffdingTestAbortBound (siftedZTestSampleSize peSel xSel)
        (siftedXTestSampleSize peSel xSel) δ εEC ≤
      honestTailAcceptance n m ℓ ℓEV peSel xSel leakEC ec δ Q Q :=
  QKD.BB84.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance
    n m ℓ ℓEV leakEC peSel xSel
    ec Q Q δ δ εEC hcount hQ0 hQ hδ (by simp) hDecode

/-! ## The complete experiment on the honest source -/

/-- Summing over selected records whose basis strings must equal the announced ones. -/
private theorem sum_selectedRecords_mul_ite_eq {N n : ℕ} (a b : Fin N → Basis)
    (F : SelectedLocalRecord N n × SelectedLocalRecord N n → ℝ)
    (G : (Fin n → Bit) → (Fin n → Bit) → ℝ) :
    (∑ r : SelectedLocalRecord N n × SelectedLocalRecord N n,
        F r * (if r.1.1 = a ∧ r.2.1 = b then G r.1.2 r.2.2 else 0)) =
      ∑ uA, ∑ uB, F ((a, uA), (b, uB)) * G uA uB := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun uA _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [hb]
    · simp
  · intro a' _ ha
    simp [ha]
  · simp

/-- The selected product-source acceptance depends only on its trace and matched Born table. -/
private theorem selectedAcceptance_productSource (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (σ : Op (Bit × Bit)) (htr : σ.trace = 1)
    (hborn : ∀ θ x y, pairBornWeight σ θ θ x y = (honestPairWeight q x y : ℂ))
    (ω : RawControl N) (h : HasQuotas nK mZ mX ω) :
    (∑ r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX),
        rawClassicalTailAcceptFraction (nK + mZ + mX) (mZ + mX) ℓ ℓEV
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q
            ((TwoParty.pairEquiv _ _).symm (r.1.2, r.2.2)) *
          (selectedControlState pA pB N nK mZ mX ω h (productSource N σ)
          ((TwoParty.pairEquiv _ _).symm r) ((TwoParty.pairEquiv _ _).symm r)).re) =
      (rawControlLaw N pA pB ω).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  -- The per-record entry of the product source, reduced to the honest-source entry by
  -- Unit trace removes the unselected pairs; the matched table fixes the selected law.
  have hentry (r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
      (selectedControlState pA pB N nK mZ mX ω h (productSource N σ)
          ((TwoParty.pairEquiv _ _).symm r) ((TwoParty.pairEquiv _ _).symm r)).re =
        if r.1.1 = ω.a ∧ r.2.1 = ω.b then
          (rawControlLaw N pA pB ω).toReal * ∏ k, honestPairWeight q (r.1.2 k) (r.2.2 k)
        else 0 := by
    refine (congrArg Complex.re
      (selectionProgram_productSource_success pA pB N nK mZ mX σ ω h r r)).trans ?_
    simp only [true_and]
    split_ifs
    · simp only [hborn]
      rw [htr, one_pow, mul_one, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    · rfl
  -- Sum the selected bits against their honest product law.
  simp_rw [hentry]
  rw [sum_selectedRecords_mul_ite_eq ω.a ω.b
      (fun r => rawClassicalTailAcceptFraction (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q
        ((TwoParty.pairEquiv _ _).symm (r.1.2, r.2.2)))
      (fun uA uB => (rawControlLaw N pA pB ω).toReal * ∏ k, honestPairWeight q (uA k) (uB k)),
    honestTailAcceptance_eq, Finset.mul_sum,
    ← (rawBitStringsEquiv _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun uA _ => Finset.sum_congr rfl fun uB _ => ?_
  rw [honestRawWeight_rawBitStringsEquiv]
  simp only [rawBitStringsEquiv]
  ring

/-- Product-source acceptance at a quota-feasible control factors through the matched Born law. -/
theorem completeContinuation_acceptWeight_productSource (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (σ : Op (Bit × Bit)) (htr : σ.trace = 1)
    (hborn : ∀ θ x y, pairBornWeight σ θ θ x y = (honestPairWeight q x y : ℂ))
    (ω : RawControl N) (h : HasQuotas nK mZ mX ω) :
    (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      packedPESel leakEC).toBoundaryKeyLayout.acceptWeight
        ((Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
            mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q)).toLinearMap
          ((classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV packedPESel packedXSel
            leakEC ec δ Q).denote
            ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
              ((forgetAliceBases N (nK + mZ + mX)).successorOperation ()
                (selectedControlState pA pB N nK mZ mX ω h (productSource N σ)))))) =
      (rawControlLaw N pA pB ω).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  rw [completeContinuation_acceptWeight_success]
  exact selectedAcceptance_productSource pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q q σ htr hborn ω h

/-- Total product-source acceptance is quota-success mass times the honest retained-tail mass. -/
theorem protocol_acceptProbability_productSource (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (σ : Op (Bit × Bit)) (htr : σ.trace = 1)
    (hborn : ∀ θ x y, pairBornWeight σ θ θ x y = (honestPairWeight q x y : ℂ)) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability
        (productSource N σ) =
      (selectionSuccessMass N nK mZ mX pA pB).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  rw [protocol_acceptProbability, selectionSuccessMass_toReal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with h
  · exact selectedAcceptance_productSource pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q q σ htr hborn ω h
  · simp
/-- **The honest run through one quota-feasible public control.**  The probability that the honest
run announces the control `ω` and then accepts is the raw-control mass of `ω` times the honest
acceptance of the real tail.  This holds at every control meeting the quotas, including controls of
zero mass; so, conditioned on any such control of positive mass, the run accepts with probability
`honestTailAcceptance`, whichever control it is. -/
theorem completeContinuation_acceptWeight_honestSource (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (ω : RawControl N) (h : HasQuotas nK mZ mX ω) :
    (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      packedPESel leakEC).toBoundaryKeyLayout.acceptWeight
        ((Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
            mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q)).toLinearMap
          ((classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV packedPESel packedXSel
            leakEC ec δ Q).denote
            ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
              ((forgetAliceBases N (nK + mZ + mX)).successorOperation ()
                (selectedControlState pA pB N nK mZ mX ω h (honestSource N q)))))) =
      (rawControlLaw N pA pB ω).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  rw [honestSource_eq_productSource]
  exact completeContinuation_acceptWeight_productSource pA pB N nK mZ mX ℓ ℓEV leakEC
    ec δ Q q (honestSourceSingle q) (trace_honestSourceSingle q)
    (fun θ x y => by rw [pairBornWeight_honestPair, honestRoundLaw_self]) ω h

/-- **The physical conditioning identity.**  On the honest source, the acceptance probability of
the complete measure-first experiment is the quota-success mass times the acceptance of the real
retained tail on the honest selected law.  No hypothesis is needed. -/
theorem protocol_acceptProbability_honestSource (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability
        (honestSource N q) =
      (selectionSuccessMass N nK mZ mX pA pB).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  rw [honestSource_eq_productSource]
  exact protocol_acceptProbability_productSource pA pB N nK mZ mX ℓ ℓEV leakEC
    ec δ Q q (honestSourceSingle q) (trace_honestSourceSingle q)
    (fun θ x y => by rw [pairBornWeight_honestPair, honestRoundLaw_self])

/-- A physical honest operation has the same control-wise acceptance as its matched product law. -/
theorem completeContinuation_acceptWeight_of_honestOperation (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (ρ : Op (weightedStreamSystem Unit N).total) (h : HonestOperation N q ρ)
    (ω : RawControl N) (hω : HasQuotas nK mZ mX ω) :
    (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      packedPESel leakEC).toBoundaryKeyLayout.acceptWeight
        ((Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q) (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ +
            mX) ℓ ℓEV
          packedPESel packedXSel leakEC ec δ Q)).toLinearMap
          ((classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV packedPESel packedXSel
            leakEC ec δ Q).denote
            ((forgetBobBases N (nK + mZ + mX)).successorOperation ()
              ((forgetAliceBases N (nK + mZ + mX)).successorOperation ()
                (selectedControlState pA pB N nK mZ mX ω hω ρ))))) =
      (rawControlLaw N pA pB ω).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact completeContinuation_acceptWeight_productSource pA pB N nK mZ mX ℓ ℓEV leakEC
    ec δ Q q σ hσ.trace_eq_one hσ.pairBornWeight_self ω hω

/-- Physical honest acceptance factors into quota success and retained-tail acceptance. -/
theorem protocol_acceptProbability_of_honestOperation (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (ρ : Op (weightedStreamSystem Unit N).total) (h : HonestOperation N q ρ) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability ρ =
      (selectionSuccessMass N nK mZ mX pA pB).toReal *
        honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact protocol_acceptProbability_productSource pA pB N nK mZ mX ℓ ℓEV leakEC
    ec δ Q q σ hσ.trace_eq_one hσ.pairBornWeight_self

/-- Physical honest abort probability splits into quota failure and retained-tail rejection. -/
theorem protocol_abortProbability_of_honestOperation (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q q : ℝ)
    (ρ : Op (weightedStreamSystem Unit N).total) (h : HonestOperation N q ρ) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).abortProbability ρ =
      (selectionFailureMass N nK mZ mX pA pB).toReal +
        (selectionSuccessMass N nK mZ mX pA pB).toReal *
          (1 - honestTailAcceptance (nK + mZ + mX) (mZ + mX) ℓ ℓEV
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q q) := by
  rw [(protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).abortProbability_eq_one_sub ρ
      h.trace_eq_one,
    protocol_acceptProbability_of_honestOperation pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q q ρ h]
  have hmass := selectionMass_toReal_add N nK mZ mX pA pB
  linear_combination -hmass

namespace Parameters

/-- An honest error rate lies inside the acceptance window by a positive margin, and the
configured reconciliation scheme decodes its honest key law with the stated failure budget. -/
structure HonestBand (p : Parameters) (q η εEC : ℝ) : Prop where
  /-- The margin inside the acceptance window is positive. -/
  margin_pos : 0 < η
  /-- The rate is in the window shrunk by the margin. -/
  mem_band : |q - p.errorRate| ≤ p.tolerance - η
  /-- The configured scheme has the required honest decoding guarantee. -/
  decodes : p.ec.DecodesWhp (honestKeyErrWeight p.sifted q p.peSel p.xSel) εEC

variable (p : Parameters)

/-- **The honest acceptance of the configured experiment's tail**: the probability that its real
retained classical tail accepts `sifted` honest matched rounds at QBER `q`. -/
def honestTailAcceptance (q : ℝ) : ℝ :=
  QKD.BB84.honestTailAcceptance p.sifted p.tests p.keyLength p.tagLength p.peSel p.xSel p.leak
    p.ec p.tolerance p.errorRate q

/-- Acceptance factors into quota-success mass and tail acceptance, algebraically for every
real `q`.  On `0 ≤ q ≤ 1/2` this is the physical experiment's acceptance probability. -/
theorem acceptProbability_honestSource (q : ℝ) :
    p.protocol.acceptProbability (honestSource p.rounds q) =
      (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis).toReal * p.honestTailAcceptance q :=
  protocol_acceptProbability_honestSource _ _ _ _ _ _ _ _ _ _ _ _ q

/-- Abort weight splits into quota failure and tail rejection, algebraically for every real `q`.
On `0 ≤ q ≤ 1/2` this is the physical experiment's abort probability. -/
theorem abortProbability_honestSource (q : ℝ) :
    p.protocol.abortProbability (honestSource p.rounds q) =
      (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis).toReal +
        (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis).toReal * (1 - p.honestTailAcceptance q) := by
  -- The honest source is a state, so abort is one minus acceptance; then factor acceptance.
  rw [p.protocol.abortProbability_eq_one_sub (honestSource p.rounds q)
      (honestSource_trace p.rounds q), acceptProbability_honestSource]
  -- The quota-failure and quota-success masses add up to one.
  have h := selectionMass_toReal_add p.rounds p.keyRounds p.zTests p.xTests p.aliceBasis
    p.bobBasis
  linear_combination -h

/-- Honest operations and the canonical source have identical acceptance probabilities. -/
lemma acceptProbability_eq_honestSource_of_honestOperation
    (ρ : Op (weightedStreamSystem Unit p.rounds).total) (q : ℝ)
    (h : HonestOperation p.rounds q ρ) :
    p.protocol.acceptProbability ρ = p.protocol.acceptProbability (honestSource p.rounds q) := by
  rw [p.acceptProbability_honestSource]
  exact protocol_acceptProbability_of_honestOperation p.aliceBasis p.bobBasis p.rounds
    p.keyRounds p.zTests p.xTests p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate q ρ h

/-- Honest operations and the canonical source have identical abort probabilities. -/
lemma abortProbability_eq_honestSource_of_honestOperation
    (ρ : Op (weightedStreamSystem Unit p.rounds).total) (q : ℝ)
    (h : HonestOperation p.rounds q ρ) :
    p.protocol.abortProbability ρ = p.protocol.abortProbability (honestSource p.rounds q) := by
  rw [p.protocol.abortProbability_eq_one_sub ρ h.trace_eq_one,
    p.protocol.abortProbability_eq_one_sub _ (honestSource_trace p.rounds q),
    p.acceptProbability_eq_honestSource_of_honestOperation ρ q h]

/-- **The configured tail accepts the honest channel with probability at least `1 - ε_c`**, at
every honest QBER `q` within `tolerance - η` of the accept centre `errorRate`, when `ec` decodes
the honest key-error model at `q` with failure mass `εEC`. -/
theorem one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance (q εEC η : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) (hB : p.HonestBand q η εEC) :
    1 - hoeffdingTestAbortBound p.zTests p.xTests η εEC ≤ p.honestTailAcceptance q := by
  have h := QKD.BB84.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance
    p.sifted p.tests p.keyLength p.tagLength p.leak p.peSel p.xSel p.ec
    q p.errorRate p.tolerance η εEC
    (packedPESel_keyCount p.keyRounds p.zTests p.xTests) hq0 hq hB.margin_pos hB.mem_band hB.decodes
  rwa [siftedZTestSampleSize_packed, siftedXTestSampleSize_packed] at h

/-- **The configured tail accepts the honest channel with probability at least `1 - ε_c`**, when
the accept test is centred at the honest QBER and `ec` decodes the honest key-error model with
failure mass `εEC`. -/
theorem one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance_self (εEC : ℝ) (hQ0 : 0 ≤
    p.errorRate)
    (hQ : p.errorRate ≤ 1) (hB : p.HonestBand p.errorRate p.tolerance εEC) :
    1 - hoeffdingTestAbortBound p.zTests p.xTests p.tolerance εEC ≤
      p.honestTailAcceptance p.errorRate :=
  p.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance p.errorRate εEC p.tolerance
    hQ0 hQ hB

/-- **The honest-abort bound of the configured experiment.**  On the honest channel at any QBER `q`
within `tolerance - η` of the accept centre, the experiment aborts with probability at most the
quota-failure mass plus the completeness budget
`2·exp(−2·zTests·η²) + 2·exp(−2·xTests·η²) + εEC`. -/
theorem abortProbability_honestSource_le_of_mem_band (q εEC η : ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ 1) (hB : p.HonestBand q η εEC) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis).toReal +
        hoeffdingTestAbortBound p.zTests p.xTests η εEC := by
  rw [abortProbability_honestSource]
  have htail := p.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance
    q εEC η hq0 hq hB
  have hle := honestTailAcceptance_le_one p.sifted p.tests p.keyLength p.tagLength p.peSel p.xSel
    p.leak p.ec p.tolerance p.errorRate hq0 (by linarith)
  have hmass := selectionMass_toReal_add p.rounds p.keyRounds p.zTests p.xTests p.aliceBasis
    p.bobBasis
  have hS0 : 0 ≤ (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
      p.aliceBasis p.bobBasis).toReal := ENNReal.toReal_nonneg
  have hF0 : 0 ≤ (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
      p.aliceBasis p.bobBasis).toReal := ENNReal.toReal_nonneg
  have hT : 0 ≤ 1 - p.honestTailAcceptance q := by
    unfold honestTailAcceptance
    linarith
  nlinarith

/-- **The honest-abort bound of the configured experiment**, at the accept test's own QBER: the
experiment aborts with probability at most the quota-failure mass plus the completeness budget
`2·exp(−2·zTests·δ²) + 2·exp(−2·xTests·δ²) + εEC`. -/
theorem abortProbability_honestSource_le_self (εEC : ℝ) (hQ0 : 0 ≤ p.errorRate)
    (hQ : p.errorRate ≤ 1) (hB : p.HonestBand p.errorRate p.tolerance εEC) :
    p.protocol.abortProbability (honestSource p.rounds p.errorRate) ≤
      (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis).toReal +
        hoeffdingTestAbortBound p.zTests p.xTests p.tolerance εEC :=
  p.abortProbability_honestSource_le_of_mem_band p.errorRate εEC p.tolerance hQ0 hQ hB

/-- **The honest-acceptance bound of the configured experiment**, the complementary form of
`abortProbability_honestSource_le_of_mem_band`: acceptance is at least
`selectionSuccessMass · (1 - ε_c)`. -/
theorem mul_one_sub_hoeffdingTestAbortBound_le_acceptProbability (q εEC η : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) (hB : p.HonestBand q η εEC) :
    (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
        p.aliceBasis p.bobBasis).toReal *
        (1 - hoeffdingTestAbortBound p.zTests p.xTests η εEC) ≤
      p.protocol.acceptProbability (honestSource p.rounds q) := by
  rw [acceptProbability_honestSource]
  exact mul_le_mul_of_nonneg_left
    (p.one_sub_hoeffdingTestAbortBound_le_honestTailAcceptance q εEC η hq0 hq hB)
    ENNReal.toReal_nonneg

/-- A physical honest operation inside the acceptance band aborts with probability at most
quota failure plus the completeness budget. Its physical law supplies both error-rate bounds. -/
theorem abortProbability_le_of_mem_band_of_honestOperation
    (ρ : Op (weightedStreamSystem Unit p.rounds).total) (q εEC η : ℝ)
    (hB : p.HonestBand q η εEC) (h : HonestOperation p.rounds q ρ) :
    p.protocol.abortProbability ρ ≤
      (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
        p.aliceBasis p.bobBasis).toReal + hoeffdingTestAbortBound p.zTests p.xTests η εEC := by
  rw [p.abortProbability_eq_honestSource_of_honestOperation ρ q h]
  exact p.abortProbability_honestSource_le_of_mem_band q εEC η h.rate_nonneg h.rate_le_one hB

end Parameters

end QKD.BB84
