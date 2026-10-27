import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Analysis.LogChoose
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.Comparison.TupkaryTanLutkenhaus
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Security.BellRenyi
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.Protocol

/-!
# The Bell–Rényi BB84 theorem certifies a longer key than the lifted literature length

For the configured physical protocol `QKD.BB84.Parameters`, this module compares the key length
the Bell–Rényi finite-key theorem (`QCryptLean.QKD.BB84.Security.BellRenyi`) certifies with the
key length of Tupkary, Tan and Lütkenhaus, arXiv:2311.01600, `adaptivepaper.tex:294`–`:299`
(`\label{eq:l_ivalue}`), lifted to coherent attacks through arXiv:2403.11851
(`QCryptLean.QKD.BB84.Comparison.TupkaryTanLutkenhaus`).

## Which lift is matched, and why

The Bell–Rényi theorem pays the Bell-symmetric postselection prefactor `C(n + 3, 3)` (lift dimension
`x = 4`, arXiv:2403.11851 `main.tex:354`
`\label{lem:groupPurification}`), and it may do so
because it assumes the error-correction scheme to be translation equivariant
(`BellRenyiConditions.ecTranslationEquivariant`).  The same symmetric lift is available to the
comparator on the same protocol under the same assumption, so the matched comparator is the
literature length lifted at `x = 4`, not at the generic `x = 16` of `main.tex:498`
(`\label{cor:liftToCoherent}`).  Every comparison statement here reads the `x = 4` lift; since a
larger prefactor only shortens the lifted length
(`Comparison.liftedLiteratureKeyLength_anti_prefactor`), the `x = 16` comparison follows.

## What the comparator is given

The comparator is evaluated at the Bell–Rényi theorem's own `keyRounds`, `tagLength`, `leak`, accept
test centre `errorRate` and half-width `tolerance`, with its entropy term at the same phase-error
bracket `errorRate + tolerance + dev` (the feasible set of the paper's own `ℓ₁` acceptance test,
`adaptivepaper.tex:549`–`:556`, is not modelled), and its lift taken over the `sifted` rounds
rather than the physical `rounds`.  It pays neither the Bell–Rényi theorem's `2·log₂ C(n + 3, 3)`
key-length charge nor its privacy-amplification cost, and the key-length half `−2·log₂ g` of
`cor:liftToCoherent` is not charged to it.  The unlifted length — prefactor `1`,
`Comparison.liftedLiteratureKeyLength 1` — is a security claim against IID-collective attacks
only, and it can exceed what the Bell–Rényi theorem certifies
(`Comparison.MillionSifted.keyLength_lt_liftedLiteratureKeyLength_one`);
the comparison is
against what the literature proves for coherent attacks.

## Main definitions

* `Parameters.BellRenyiAdvantageRegion`: the Bell–Rényi comparison region, with the free
  `ε_PA`, Rényi offset `β` and phase-error deviation `dev` of
  `Parameters.BellRenyiConditions` free and the comparator evaluated at the phase-error
  deviation `(tolerance + dev)/2`, i.e. the entropy bracket `errorRate + tolerance + dev`.

## Main statements

* `Comparison.exists_keyLength_gt_liftedLiteratureKeyLength`: the
  arithmetic core —
  a penalty gap of at least one bit yields an integer key length above the comparator at which
  the Bell–Rényi key-rate condition `BellRenyiKeyRate` holds at the soundness edge
  `Q + δ + dev`; the comparator is at the phase-error deviation `(δ + dev)/2`, i.e. the entropy
  bracket `Q + δ + dev`.
* `FiniteKey.bellRenyiBudget_mono`: monotonicity in the acceptance-test tail.
* `Parameters.exists_keyLength_gt_liftedLiteratureKeyLength`: the Bell–Rényi comparison
  theorem, against `BellRenyiConditions` and `bellRenyiBudget` at the bracket.

A closed instance at `10⁶` sifted rounds is
`QCryptLean.QKD.BB84.Comparison.MillionSiftedRounds`.
-/

open Math.Combinatorics

open InfoTheory.Renyi

open Math.ClassicalEntropy Quantum.DeFinetti

noncomputable section

namespace QKD.BB84

open QKD.BB84.FiniteKey

namespace Comparison

/-- **The arithmetic core of the Bell–Rényi comparison.**

The key-rate condition is the
free-parameter `BellRenyiKeyRate`, charged at the soundness edge `Q + δ + dev` and
funding the free `ε_PA` with `2·log(1/ε_PA) − 2·log 2` nats, and the comparator is evaluated at the
matching phase-error deviation `(δ + dev)/2`, i.e. the entropy bracket
`Q + 2·((δ + dev)/2) = Q + δ + dev`.  The
penalty gap is in bits: the free-offset Cor IV.2 penalty `P_β`, the postselection charge
`2·log₂ C(n + 3, 3)` and the privacy-amplification funding `2·log₂(1/ε_PA) − 2` must leave one
bit. The
doubled-window arithmetic condition `BellRenyiWindowKeyRate` is the
special case `dev = δ` of this theorem, via `bellRenyiKeyRate_self`. -/
theorem exists_keyLength_gt_liftedLiteratureKeyLength
    {x n m nK ℓEV leak : ℕ} {Q δ dev ε_AEP εPA β ε_tot : ℝ}
    (hK : QKD.BB84.FiniteKey.keyRounds n m = nK)
    (hnonneg : 0 ≤ liftedLiteratureKeyLength x n nK ℓEV leak Q ((δ + dev) / 2) ε_tot)
    (hgap : renyiPenalty binaryVarianceBound nK ε_AEP β
        + 2 * Real.log (Nat.choose (n + 3) 3 : ℝ) / Real.log 2
        + 2 * Real.log (1 / εPA) / Real.log 2 - 1
      ≤ literatureFiniteSizePenalty nK (liftedPrivacyAmplificationError x n ε_tot)) :
    ∃ ℓ : ℕ, liftedLiteratureKeyLength x n nK ℓEV leak Q ((δ + dev) / 2) ε_tot < ℓ ∧
      BellRenyiKeyRate n m ℓ ℓEV leak Q δ dev ε_AEP εPA β := by
  subst hK
  set c : ℝ := liftedLiteratureKeyLength x n (QKD.BB84.FiniteKey.keyRounds n m) ℓEV leak Q
      ((δ + dev) / 2) ε_tot with hc
  refine ⟨⌊c⌋₊ + 1, ?_, ?_⟩
  · push_cast
    exact Nat.lt_floor_add_one c
  · have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hfl : (⌊c⌋₊ : ℝ) * Real.log 2 ≤ c * Real.log 2 :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hnonneg) hL.le
    set S : ℝ := renyiPenalty binaryVarianceBound
        (QKD.BB84.FiniteKey.keyRounds n m) ε_AEP β
    set P : ℝ := literatureFiniteSizePenalty (QKD.BB84.FiniteKey.keyRounds n m)
      (liftedPrivacyAmplificationError x n ε_tot)
    set G : ℝ := Real.log (Nat.choose (n + 3) 3 : ℝ)
    -- the comparator's entropy argument `Q + 2·((δ + dev)/2)` is the soundness edge `Q + δ + dev`
    have hhalf : (Q : ℝ) + 2 * ((δ + dev) / 2) = Q + δ + dev := by ring
    have hrate : (QKD.BB84.FiniteKey.keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + δ + dev))
        = Real.log 2 * (c + (leak : ℝ) + (ℓEV : ℝ) + P) := by
      rw [hc, liftedLiteratureKeyLength, literatureKeyLength, hhalf]
      field_simp
      ring
    have hgap' : Real.log 2 * S + 2 * G + 2 * Real.log (1 / εPA) - Real.log 2
        ≤ Real.log 2 * P := by
      have h := mul_le_mul_of_nonneg_left hgap hL.le
      have hid : Real.log 2 * (S + 2 * G / Real.log 2 + 2 * Real.log (1 / εPA) / Real.log 2 - 1)
          = Real.log 2 * S + 2 * G + 2 * Real.log (1 / εPA) - Real.log 2 := by
        field_simp
      linarith
    rw [bellRenyiKeyRate_iff, hrate]
    push_cast
    linarith

end Comparison

namespace Parameters

variable (p : Parameters)

/-- The lifted literature comparator at a configured experiment's sifted count and costs. -/
def liftedLiteratureWindowKeyLength (p : Parameters) (x : ℕ) (ε_tot : ℝ) : ℝ :=
  Comparison.liftedLiteratureKeyLength x p.sifted p.keyRounds p.tagLength p.leak
    p.errorRate p.tolerance ε_tot

/-- The lifted literature comparator at a configured experiment's sifted count and costs, with
its entropy term at the Bell–Rényi theorem's phase-error bracket `(tolerance + dev) / 2` : the
bracket
`Q + 2·((δ + dev)/2) = Q + δ + dev` at which the Bell–Rényi theorem's key-rate condition
`BellRenyiKeyRate` is charged. -/
def liftedLiteratureKeyLength (p : Parameters) (x : ℕ) (ε_tot dev : ℝ) : ℝ :=
  Comparison.liftedLiteratureKeyLength x p.sifted p.keyRounds p.tagLength p.leak
    p.errorRate ((p.tolerance + dev) / 2) ε_tot

/-- The Bell–Rényi budget is bounded by replacing its KL tail with the quadratic tail. -/
theorem bellRenyiBudget_le_quadraticTail (hQ : 0 < p.errorRate) (hδ : 0 < p.tolerance)
    {dev : ℝ} (hdev : 0 < dev)
    (hbelow : p.errorRate + p.tolerance + dev < errorThreshold) (epsilonAEP εPA : ℝ) :
    p.bellRenyiBudget epsilonAEP εPA dev ≤
      QKD.BB84.FiniteKey.bellRenyiBudget (Real.exp (-4 * (p.xTests : ℝ) * dev ^ 2))
        p.sifted p.tagLength epsilonAEP εPA := by
  have htail := phaseTail_le_exp_neg_mul_sq (peSel := p.peSel) (xSel := p.xSel)
    hQ hδ hdev hbelow
  rw [Reduction.siftedXTestSampleSize_packed] at htail
  exact bellRenyiBudget_mono _ _ _ _ htail

/-- **The explicit comparison region for the Bell–Rényi theorem** against the Bell-symmetric (`x =
4`)
lift of the literature key length evaluated at the phase-error deviation `(tolerance + dev)/2`,
i.e. the entropy bracket `errorRate + tolerance + dev`.

The PA error and Rényi offset are free: the
elementary regime is carried as the key-length-independent fields of `BellRenyiConditions`
and the penalty gap charges the free-offset Cor IV.2 penalty `P_β` and the free
privacy-amplification funding `2·log₂(1/ε_PA) − 2` instead of `sifted·δ²/log 2 − 2` for
`ε_PA = exp(−sifted·δ²/2)` .
The acceptance and soundness edges lie in `(0, 1/2]`, so both KL logarithms have positive
arguments. The budget and penalty gap force a positive key count;
together with `liftedPrivacyAmplificationError_lt_one`, this keeps the comparator's Rényi offset
positive.
Positivity of its PA error follows from the positive Bell budget and
`QKD.BB84.Parameters.BellRenyiAdvantageRegion.bellRenyiBudget_le`.

None of the fields mentions `keyLength`. -/
structure BellRenyiAdvantageRegion (epsilonAEP εPA β dev epsilonTotal : ℝ) : Prop where
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The privacy-amplification error is positive. -/
  epsPA_pos : 0 < εPA
  /-- The Rényi offset is positive. -/
  beta_pos : 0 < β
  /-- The Rényi offset is less than `1`. -/
  beta_lt_one : β < 1
  /-- The phase-error deviation is nonnegative. -/
  dev_nonneg : 0 ≤ dev
  /-- The acceptance edge is strictly positive, as required by both KL logarithms. -/
  acceptanceEdge_pos : 0 < p.errorRate + p.tolerance
  /-- The soundness edge is at most the midpoint of binary entropy. -/
  soundnessEdge_le_half : p.errorRate + p.tolerance + dev ≤ 1 / 2
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant
  /-- The `bellRenyiBudget` is within the shared total. -/
  bellRenyiBudget_le : p.bellRenyiBudget epsilonAEP εPA dev ≤ epsilonTotal
  /-- The comparator's privacy-amplification error lies below one. -/
  liftedPrivacyAmplificationError_lt_one : Comparison.liftedPrivacyAmplificationError 4 p.sifted
    epsilonTotal < 1
  /-- The `x = 4` lifted literature key length at the bracket is nonnegative. -/
  liftedLiteratureKeyLength_nonneg : 0 ≤ p.liftedLiteratureKeyLength 4 epsilonTotal dev
  /-- The lifted literature penalty exceeds the Bell–Rényi theorem's extra charges by one bit. -/
  penalty_le_literatureFiniteSizePenalty :
    renyiPenalty binaryVarianceBound p.keyRounds epsilonAEP β
        + 2 * Real.log (Nat.choose (p.sifted + 3) 3 : ℝ) / Real.log 2
        + 2 * Real.log (1 / εPA) / Real.log 2 - 1
      ≤ Comparison.literatureFiniteSizePenalty p.keyRounds
          (Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal)

/-- The general comparator's entropy bracket is nonnegative. -/
theorem BellRenyiAdvantageRegion.entropyBracket_nonneg {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    0 ≤ p.errorRate + p.tolerance + dev := by
  linarith [h.acceptanceEdge_pos, h.dev_nonneg]

/-- The general region's shared total and literature PA error are positive. -/
theorem BellRenyiAdvantageRegion.liftedPrivacyAmplificationError_pos {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    0 < Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal := by
  apply Comparison.liftedPrivacyAmplificationError_pos
  apply lt_of_lt_of_le _ h.bellRenyiBudget_le
  simp only [Parameters.bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four,
    QKD.BB84.FiniteKey.bellRenyiBudget, bellRenyiSecrecyBudget,
      InfoTheory.Security.smoothingError, InfoTheory.Security.acceptanceError]
  have := h.smoothing_pos
  have := h.epsPA_pos
  positivity

/-- The general region's smoothing parameter is below one. -/
theorem BellRenyiAdvantageRegion.smoothing_lt_one {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    epsilonAEP < 1 := by
  have hg : 0 < (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ p.sifted + 3)
  have htotal := h.liftedPrivacyAmplificationError_lt_one
  rw [Comparison.liftedPrivacyAmplificationError, deFinettiPrefactor_four,
    div_lt_one (by positivity)] at htotal
  have hbudget := h.bellRenyiBudget_le
  simp only [Parameters.bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four,
    QKD.BB84.FiniteKey.bellRenyiBudget, bellRenyiSecrecyBudget,
      InfoTheory.Security.smoothingError, InfoTheory.Security.acceptanceError] at hbudget
  have hcorrect : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
  have hsqrt := Real.sqrt_nonneg
    (2 * phaseTail p.peSel p.xSel p.errorRate p.tolerance dev)
  nlinarith [h.epsPA_pos]

/-- Both Bernoulli parameters in the general region lie strictly between zero and one. -/
theorem BellRenyiAdvantageRegion.klParameters_mem_Ioo {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    p.errorRate + p.tolerance ∈ Set.Ioo (0 : ℝ) 1 ∧
      p.errorRate + p.tolerance + dev ∈ Set.Ioo (0 : ℝ) 1 := by
  have := h.acceptanceEdge_pos
  have := h.dev_nonneg
  have := h.soundnessEdge_le_half
  constructor <;> constructor <;> linarith

/-- The budget and penalty gap force a positive key count in the general comparison region. -/
theorem BellRenyiAdvantageRegion.keyRounds_pos {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    0 < p.keyRounds := by
  have hg : 0 < (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ p.sifted + 3)
  have htotal : epsilonTotal < 2 * (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    have hlt := h.liftedPrivacyAmplificationError_lt_one
    rwa [Comparison.liftedPrivacyAmplificationError, deFinettiPrefactor_four,
      div_lt_one (by positivity)] at hlt
  have hinner : εPA + 2 * (epsilonAEP + Real.sqrt
      (2 * phaseTail p.peSel p.xSel p.errorRate p.tolerance dev)) < 2 := by
    have hbudget := h.bellRenyiBudget_le
    simp only [Parameters.bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four,
    QKD.BB84.FiniteKey.bellRenyiBudget, bellRenyiSecrecyBudget,
      InfoTheory.Security.smoothingError, InfoTheory.Security.acceptanceError] at hbudget
    have hcorrect : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
    nlinarith
  have hsqrt := Real.sqrt_nonneg
    (2 * phaseTail p.peSel p.xSel p.errorRate p.tolerance dev)
  have hAEP : epsilonAEP < 1 := h.smoothing_lt_one
  have hPA : εPA < 2 := by linarith [h.smoothing_pos]
  have hB : 1 < Real.logb 2 (2 / epsilonAEP ^ 2) :=
    one_lt_logb_two_div_sq epsilonAEP h.smoothing_pos hAEP
  have hpen : 1 < Real.logb 2 (2 / epsilonAEP ^ 2) / β := by
    rw [lt_div_iff₀ h.beta_pos]
    linarith [h.beta_lt_one]
  have hn : 0 < p.sifted := by
    by_contra hn
    have hn0 : p.sifted = 0 := Nat.eq_zero_of_not_pos hn
    have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn0; omega
    have hs : 1 ≤ Real.sqrt 2 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    simp only [phaseTail, Reduction.siftedXTestSampleSize_packed, hx,
      Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] at hinner
    linarith [h.smoothing_pos, h.epsPA_pos]
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcharge : -2 < 2 * Real.log (1 / εPA) / Real.log 2 := by
    rw [one_div, Real.log_inv, lt_div_iff₀ hL]
    linarith [Real.log_lt_log h.epsPA_pos hPA]
  have hpost := Real.four_le_two_mul_log_choose_add_three_div_log_two hn
  by_contra hn
  have hzero : p.keyRounds = 0 := Nat.eq_zero_of_not_pos hn
  have hgap := h.penalty_le_literatureFiniteSizePenalty
  simp only [hzero, renyiPenalty,
    InfoTheory.Renyi.renyiVariancePenalty,
    InfoTheory.Renyi.renyiRemainderPenalty,
    InfoTheory.Renyi.renyiSmoothingPenalty,
    InfoTheory.Renyi.smoothingLog, Nat.cast_zero, mul_zero, zero_mul,
    zero_add, Comparison.literatureFiniteSizePenalty_zero] at hgap
  linarith

/-- **The general Bell–Rényi theorem certifies a key strictly longer than the literature length
lifted
at the matched Bell-symmetric prefactor `C(n + 3, 3)`, evaluated at the phase-error deviation
`(tolerance + dev)/2`, i.e. the entropy bracket `errorRate + tolerance + dev`.**

On `BellRenyiAdvantageRegion` there is a key length `ℓ` strictly above
`liftedLiteratureKeyLength 4 ε_tot dev` at which the configured protocol with key length `ℓ`
satisfies `BellRenyiConditions`, has `bellRenyiBudget` at most the shared total, and
is fully interface-secure at that total (`realIdealDistance_le_bellRenyiBudget`,
`isSecure_of_bellRenyiConditions`).

The witness is `⌊literature length⌋₊ + 1`
(`Comparison.exists_keyLength_gt_liftedLiteratureKeyLength`). -/
theorem exists_keyLength_gt_liftedLiteratureKeyLength
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.BellRenyiAdvantageRegion epsilonAEP εPA β dev epsilonTotal) :
    ∃ ℓ : ℕ,
      p.liftedLiteratureKeyLength 4 epsilonTotal dev < ℓ ∧
        ({ p with keyLength := ℓ }).BellRenyiConditions epsilonAEP εPA β dev ∧
        ({ p with keyLength := ℓ }).bellRenyiBudget epsilonAEP εPA dev ≤ epsilonTotal ∧
        ({ p with keyLength := ℓ }).protocol.IsSecure epsilonTotal := by
  have hK : QKD.BB84.FiniteKey.keyRounds p.sifted p.tests = p.keyRounds := by
    simp only [QKD.BB84.FiniteKey.keyRounds, Parameters.sifted, Parameters.tests]
    omega
  obtain ⟨ℓ, hlt, hkey⟩ :=
    Comparison.exists_keyLength_gt_liftedLiteratureKeyLength hK
      h.liftedLiteratureKeyLength_nonneg h.penalty_le_literatureFiniteSizePenalty
  have hcond : ({ p with keyLength := ℓ }).BellRenyiConditions epsilonAEP εPA β dev :=
    { smoothing_pos := h.smoothing_pos
      keyRate := hkey
      ecTranslationEquivariant := h.ecTranslationEquivariant
      epsPA_pos := h.epsPA_pos
      beta_pos := h.beta_pos
      beta_lt_one := h.beta_lt_one
      dev_nonneg := h.dev_nonneg
      soundnessEdge_le_half := h.soundnessEdge_le_half }
  exact ⟨ℓ, hlt, hcond, h.bellRenyiBudget_le,
    (({ p with keyLength := ℓ }).isSecure_of_bellRenyiConditions hcond).mono
      h.bellRenyiBudget_le⟩

end Parameters

end QKD.BB84

end -- noncomputable section
