import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor

/-!
# The literature BB84 finite-size key length, lifted to coherent attacks

This module transcribes, as explicit definitions, the finite-size key length of
Tupkary, Tan and Lütkenhaus, arXiv:2311.01600 (`adaptivepaper.tex`),
and its lift to coherent attacks through the postselection technique of Nahar, Tupkary, Zhao,
Lütkenhaus and Tan, arXiv:2403.11851 (`main.tex`).  It is the
comparator of the key-length comparison in
`QCryptLean.QKD.BB84.Comparison.KeyLengthGap`.

The total security error uses the distinguishing advantage `½‖R − I‖_diamond`, as do both
library security theorems. The factor two in `ε_tot/(2g)` below is the paper's error allocation.

## The transcribed key length

`adaptivepaper.tex:294`–`:299` (`\label{eq:l_ivalue}`) gives, for `n` key-generation signals,

`l = ⌊ n·min H(Z|CE) − leakEC − ℓEV − n(α−1)·log₂²(d_Z+1) − (α/(α−1))·(log₂(1/(4ε_PA)) + 2/α) ⌋`,

with the Rényi order fixed at `:300` (and again at `:567`, `:581`) to `α = 1 + κ/√n`,
`κ = √(log₂(1/ε_PA))/log₂(d_Z+1)`.  At `d_Z = 2` the continuity constant is
`log₂²3` (`literatureContinuityConstant`).

The BB84 display `adaptivepaper.tex:561`–`:567` (`\label{eq:bb84keyrate}`) writes the same term
with `log²(2d_Z+1) = log₂²5` instead; their cited continuity lemma `:1106`
(`\label{lemma:contrenyi}`, Dupuis–Fawzi–Renner) is the source of `log₂²5`.  We transcribe the
smaller constant `log₂²3` of `eq:l_ivalue`, which gives the comparator the *longer* key.

`literatureKeyLength` evaluates `eq:l_ivalue` with the entropy term at `1 − h₂(Q + 2δ)` bits per
key round: the phase-error bracket `Q + 2δ` of the Bell–Rényi theorem's own acceptance test, so that
both key lengths are compared at the same entropy bracket.  The feasible set the paper derives
from its own `ℓ₁` acceptance test (`adaptivepaper.tex:549`–`:556`, `\label{eq:bb84Sset}`) is not
modelled.  The outer floor is omitted and the paper's validity condition
`α ≤ 1 + 1/log₂(2d_Z + 1)` (`:300`) is not imposed; both omissions can only lengthen the
comparator or add points at which it makes a claim.  The closed form of the penalty is
`literatureFiniteSizePenalty_eq_closedForm`: `2√(n·log₂²3·log₂(1/ε_PA)) + log₂(1/ε_PA) − 2`.

## The lift to coherent attacks

`eq:l_ivalue` is a security statement against IID-collective attacks only
(`adaptivepaper.tex:167`, `:186`, `:264`); the lift to coherent attacks is deferred at `:1049` to
arXiv:2403.11851.  There, `main.tex:498` (`\label{cor:liftToCoherent}`) turns an IID-collective
`(ε_PA + 2ε̄ + 2√(2ε_AT))`-secret protocol into a `g_{n,x}·(ε_PA + 2ε̄ + 2√(2ε_AT))`-secret one,
with the postselection prefactor `g_{n,x} = C(n + x − 1, x − 1)` (`main.tex:234`, `:846`;
`Math.Combinatorics.deFinettiPrefactor`), **and** shortens the key to `l − 2·log₂ g_{n,x}`.

On the ledger `ε_sec = ε_EV + max{ε_AT, ε_PA}` (`adaptivepaper.tex:283`) with the paper's split
`ε_AT = ε_PA = ε_EV = ε_sec/2` (`:584`), a coherent-attack total `ε_tot` therefore forces
`ε_PA = ε_tot/(2·g_{n,x})` (`liftedPrivacyAmplificationError`).  `liftedLiteratureKeyLength`
charges only this security-parameter half of the lift and **not** the key-length half
`−2·log₂ g_{n,x}`; the omission is in the comparator's favour.

The lift dimension `x` is an explicit parameter:

* `x = 16 = d_A²·d_B²` is the generic lift of `cor:liftToCoherent`, `g = C(n + 15, 15)`;
* `x = 4` is the Bell-symmetric lift, `g = C(n + 3, 3)`, from `main.tex:354`
  (`\label{lem:groupPurification}`) at the four one-dimensional irreducible representations of
  the bilateral Bell-Pauli group on `ℂ⁴`.  It needs the protocol map to be invariant under that
  group; for the BB84 program of this library that invariance is derived from the translation
  equivariance of the error-correction scheme (`QKD.BB84.ECScheme.IsTranslationEquivariant`).

A larger prefactor lowers the lifted length (`liftedLiteratureKeyLength_anti_prefactor`), so
the `x = 4` comparator is the harder of the two.

## Main definitions

* `literatureContinuityConstant`: `log₂²3`.
* `literatureRenyiOffset`: `α − 1 = κ/√n`.
* `literatureFiniteSizePenalty`: the finite-size charge of `eq:l_ivalue`.
* `literatureKeyLength`: the key length of `eq:l_ivalue` at a given `ε_PA`.
* `liftedPrivacyAmplificationError`: `ε_tot/(2·g_{n,x})`.
* `liftedLiteratureKeyLength`: the key length at the lifted `ε_PA`.

## Main statements

* `literatureFiniteSizePenalty_eq_closedForm`.
* `logb_inv_liftedPrivacyAmplificationError`: `log₂(1/ε_PA) = 1 + log₂(1/ε_tot) + log₂ g_{n,x}`.
* `liftedLiteratureKeyLength_anti_prefactor`.
-/

open Math.Combinatorics

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.Comparison

/-! ## The finite-size penalty of `eq:l_ivalue` -/

/-- **The continuity constant** `log₂²(d_Z + 1)` of `adaptivepaper.tex:294`–`:299`
(`\label{eq:l_ivalue}`) at `d_Z = 2`, i.e. `log₂²3`. -/
def literatureContinuityConstant : ℝ := Real.logb 2 3 ^ 2

/-- The square root of the literature continuity constant is `log₂ 3`. -/
lemma sqrt_literatureContinuityConstant :
    Real.sqrt literatureContinuityConstant = Real.logb 2 3 := by
  exact Real.sqrt_sq (Real.logb_nonneg (by norm_num) (by norm_num))

/-- **The Rényi offset** `α − 1 = κ/√n` with `κ = √(log₂(1/ε_PA))/log₂(d_Z + 1)`
(`adaptivepaper.tex:300`), written as `√(log₂(1/ε_PA)/(log₂²3·n))`. -/
def literatureRenyiOffset (nK : ℕ) (εPA : ℝ) : ℝ :=
  Real.sqrt (Real.logb 2 εPA⁻¹ / (literatureContinuityConstant * (nK : ℝ)))

/-- Rényi-to-smooth-entropy logarithmic cost in the TTL comparison, in bits. -/
def literatureSmoothingCost (β εPA : ℝ) : ℝ :=
  (1 + β) / β * (Real.logb 2 (1 / (4 * εPA)) + 2 / (1 + β))

/-- **The finite-size penalty of `adaptivepaper.tex:294`–`:299`** (`\label{eq:l_ivalue}`), in
bits, at `nK` key-generation signals:
`nK·(α−1)·log₂²3 + (α/(α−1))·(log₂(1/(4ε_PA)) + 2/α)` with `α = 1 + literatureRenyiOffset`. -/
def literatureFiniteSizePenalty (nK : ℕ) (εPA : ℝ) : ℝ :=
  (nK : ℝ) * literatureRenyiOffset nK εPA * literatureContinuityConstant +
    literatureSmoothingCost (literatureRenyiOffset nK εPA) εPA

/-- `log₂²3 > 0`. -/
theorem literatureContinuityConstant_pos : 0 < literatureContinuityConstant := by
  have h3 : (0 : ℝ) < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  rw [literatureContinuityConstant]
  positivity

/-- Positive key count and a PA error in `(0, 1)` give a positive Rényi offset. -/
theorem literatureRenyiOffset_pos {nK : ℕ} {εPA : ℝ}
    (hn : 0 < nK) (h0 : 0 < εPA) (h1 : εPA < 1) :
    0 < literatureRenyiOffset nK εPA := by
  have hinv : (1 : ℝ) < εPA⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) h0]
    simpa using h1
  have hlog : 0 < Real.logb 2 εPA⁻¹ := Real.logb_pos one_lt_two hinv
  have hnR : (0 : ℝ) < nK := by exact_mod_cast hn
  rw [literatureRenyiOffset, Real.sqrt_pos]
  exact div_pos hlog (mul_pos literatureContinuityConstant_pos hnR)

/-- The literature penalty vanishes at zero key rounds under totalized division. -/
@[simp] theorem literatureFiniteSizePenalty_zero (εPA : ℝ) :
    literatureFiniteSizePenalty 0 εPA = 0 := by
  simp [literatureFiniteSizePenalty,
    QKD.BB84.Comparison.literatureSmoothingCost, literatureRenyiOffset]

/-- A privacy-amplification error at least one collapses the literature offset and penalty. -/
theorem literatureFiniteSizePenalty_eq_zero_of_one_le (nK : ℕ) {εPA : ℝ}
    (hε : 1 ≤ εPA) : literatureFiniteSizePenalty nK εPA = 0 := by
  have hlog : Real.logb 2 εPA⁻¹ ≤ 0 := by
    rw [Real.logb_inv]
    exact neg_nonpos.mpr (Real.logb_nonneg one_lt_two hε)
  have hoffset : literatureRenyiOffset nK εPA = 0 := by
    exact Real.sqrt_eq_zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hlog
        (mul_nonneg literatureContinuityConstant_pos.le (Nat.cast_nonneg _)))
  simp [literatureFiniteSizePenalty,
    QKD.BB84.Comparison.literatureSmoothingCost, hoffset]

/-- A positive TTL finite-size penalty requires a privacy-amplification error below one. -/
theorem lt_one_of_literatureFiniteSizePenalty_pos {nK : ℕ} {εPA : ℝ}
    (h : 0 < literatureFiniteSizePenalty nK εPA) : εPA < 1 := by
  by_contra hlt
  rw [literatureFiniteSizePenalty_eq_zero_of_one_le nK (le_of_not_gt hlt)] at h
  exact (lt_irrefl 0) h


/-- **The closed form of the literature penalty**, an exact identity:
`2√(nK·log₂²3·log₂(1/ε_PA)) + log₂(1/ε_PA) − 2`.

`0 < nK` and `0 < ε_PA < 1` are load-bearing: otherwise the offset is `0` and the division
degenerates. -/
theorem literatureFiniteSizePenalty_eq_closedForm (nK : ℕ) (εPA : ℝ)
    (hn : 0 < nK) (h0 : 0 < εPA) (h1 : εPA < 1) :
    literatureFiniteSizePenalty nK εPA
      = 2 * Real.sqrt ((nK : ℝ) * literatureContinuityConstant * Real.logb 2 εPA⁻¹)
        + Real.logb 2 εPA⁻¹ - 2 := by
  have hC : 0 < literatureContinuityConstant := literatureContinuityConstant_pos
  have hnR : (0 : ℝ) < (nK : ℝ) := by exact_mod_cast hn
  have hinv : (1 : ℝ) < εPA⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) h0]; simpa using h1
  set W : ℝ := Real.logb 2 εPA⁻¹ with hWdef
  have hW : 0 < W := Real.logb_pos (by norm_num) hinv
  set b : ℝ := literatureRenyiOffset nK εPA with hbdef
  have hbsq : b ^ 2 = W / (literatureContinuityConstant * (nK : ℝ)) := by
    rw [hbdef, literatureRenyiOffset, ← hWdef]
    exact Real.sq_sqrt (by positivity)
  have hbpos : 0 < b := by
    rw [hbdef, literatureRenyiOffset, ← hWdef]
    exact Real.sqrt_pos.mpr (by positivity)
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hb1 : (1 : ℝ) + b ≠ 0 := by positivity
  have hquarter : Real.logb 2 ((1 : ℝ) / 4) = -2 := by
    rw [Real.logb, show (1 : ℝ) / 4 = ((2 : ℝ) ^ (2 : ℕ))⁻¹ from by norm_num,
      Real.log_inv, Real.log_pow]
    field_simp
    norm_num
  have hshift : Real.logb 2 (1 / (4 * εPA)) = W - 2 := by
    rw [show (1 : ℝ) / (4 * εPA) = (1 / 4) * εPA⁻¹ from by field_simp,
      Real.logb_mul (by norm_num) (by positivity), hquarter, ← hWdef]
    ring
  have hWb : W / b = Real.sqrt ((nK : ℝ) * literatureContinuityConstant * W) := by
    have hid : (nK : ℝ) * literatureContinuityConstant * W = (W / b) ^ 2 := by
      rw [div_pow, hbsq]
      field_simp
    rw [hid, Real.sqrt_sq (by positivity)]
  have hnC : (nK : ℝ) * literatureContinuityConstant = W / b ^ 2 := by
    rw [hbsq]
    field_simp
  have hfirst : (nK : ℝ) * b * literatureContinuityConstant = W / b := by
    rw [show (nK : ℝ) * b * literatureContinuityConstant
        = ((nK : ℝ) * literatureContinuityConstant) * b from by ring, hnC]
    field_simp
  rw [literatureFiniteSizePenalty,
    QKD.BB84.Comparison.literatureSmoothingCost, ← hbdef, hshift, ← hWb, hfirst]
  field_simp
  ring

/-- The literature finite-size penalty with `log₂ 3` factored out of the square root. -/
lemma literatureFiniteSizePenalty_eq_logb_three_mul_sqrt (m : ℕ) (εPA : ℝ)
    (hm : 0 < m) (h0 : 0 < εPA) (h1 : εPA < 1) :
    literatureFiniteSizePenalty m εPA =
      2 * (Real.logb 2 3 * Real.sqrt ((m : ℝ) * Real.logb 2 εPA⁻¹)) +
        Real.logb 2 εPA⁻¹ - 2 := by
  rw [literatureFiniteSizePenalty_eq_closedForm m εPA hm h0 h1,
    show (m : ℝ) * literatureContinuityConstant * Real.logb 2 εPA⁻¹ =
      literatureContinuityConstant * ((m : ℝ) * Real.logb 2 εPA⁻¹) from by ring,
    Real.sqrt_mul literatureContinuityConstant_pos.le, sqrt_literatureContinuityConstant]

/-- **The literature penalty is monotone in `log₂(1/ε_PA)`.**  At a fixed `nK > 0`, a smaller
`ε_PA ∈ (0, 1)` is charged a larger penalty. -/
theorem literatureFiniteSizePenalty_le_of_le (nK : ℕ) {ε ε' : ℝ} (hn : 0 < nK)
    (hε' : 0 < ε') (hεε' : ε' ≤ ε) (hε1 : ε < 1) :
    literatureFiniteSizePenalty nK ε ≤ literatureFiniteSizePenalty nK ε' := by
  have hε : 0 < ε := hε'.trans_le hεε'
  rw [literatureFiniteSizePenalty_eq_closedForm nK ε hn hε hε1,
    literatureFiniteSizePenalty_eq_closedForm nK ε' hn hε' (hεε'.trans_lt hε1)]
  have hW : Real.logb 2 ε⁻¹ ≤ Real.logb 2 ε'⁻¹ :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity)
      ((inv_le_inv₀ hε hε').mpr hεε')
  have hC : 0 ≤ (nK : ℝ) * literatureContinuityConstant :=
    mul_nonneg (Nat.cast_nonneg _) literatureContinuityConstant_pos.le
  have hs : Real.sqrt ((nK : ℝ) * literatureContinuityConstant * Real.logb 2 ε⁻¹)
      ≤ Real.sqrt ((nK : ℝ) * literatureContinuityConstant * Real.logb 2 ε'⁻¹) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hW hC)
  linarith

/-! ## The key length at a given `ε_PA`, and its lift -/

/-- **The literature key length at a given `ε_PA`**, in bits: `adaptivepaper.tex:294`–`:299`
(`\label{eq:l_ivalue}`) at `nK` key-generation signals, with the entropy term evaluated at the
phase-error bracket `Q + 2δ`, i.e. `1 − h₂(Q + 2δ)` bits per signal (`binaryEntropy` is in nats),
and without the outer floor.

This is a key length against IID-collective attacks only; see `liftedLiteratureKeyLength` for the
coherent-attack version. -/
def literatureKeyLength (nK ℓEV leak : ℕ) (Q δ εPA : ℝ) : ℝ :=
  (nK : ℝ) / Real.log 2 * (Real.log 2 - binaryEntropy (Q + 2 * δ))
    - (leak : ℝ) - (ℓEV : ℝ) - literatureFiniteSizePenalty nK εPA

/-- **The privacy-amplification error forced by the postselection lift**:
`ε_PA = ε_tot/(2·g_{n,x})`, with `g_{n,x} = deFinettiPrefactor x n = C(n + x − 1, x − 1)`
(arXiv:2403.11851 `main.tex:234`, `:498` `\label{cor:liftToCoherent}`) and the split
`ε_AT = ε_PA = ε_EV = ε_sec/2` of `adaptivepaper.tex:584` on the ledger of `:283`.

`x` is the lift dimension: `16` for the generic lift of `cor:liftToCoherent`, `4` for the
Bell-symmetric lift of `main.tex:354` (`\label{lem:groupPurification}`). -/
def liftedPrivacyAmplificationError (x n : ℕ) (ε_tot : ℝ) : ℝ :=
  ε_tot / (2 * (deFinettiPrefactor x n : ℝ))

/-- **The literature key length lifted to coherent attacks** at lift dimension `x` over `n`
postselected signals, for a coherent-attack total `ε_tot`: `literatureKeyLength` at
`liftedPrivacyAmplificationError x n ε_tot`.

Only the security-parameter half of `cor:liftToCoherent` is charged; the key-length half
`−2·log₂ g_{n,x}` is not, in the comparator's favour.
This is the Tupkary–Tan–Lütkenhaus bound, with the security error rescaled by the
postselection factor. It omits the additional `2 * log₂ g` key-length charge of the coherent
attack lift, as well as the outer floor and Rényi-order validity restriction. -/
def liftedLiteratureKeyLength (x n nK ℓEV leak : ℕ) (Q δ ε_tot : ℝ) : ℝ :=
  literatureKeyLength nK ℓEV leak Q δ (liftedPrivacyAmplificationError x n ε_tot)

/-- The lifted `ε_PA` is positive for a positive total. -/
theorem liftedPrivacyAmplificationError_pos (x n : ℕ) {ε_tot : ℝ} (h : 0 < ε_tot) :
    0 < liftedPrivacyAmplificationError x n ε_tot := by
  have hg : (1 : ℝ) ≤ (deFinettiPrefactor x n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (deFinettiPrefactor_pos x n))
  rw [liftedPrivacyAmplificationError]
  positivity

/-- The lifted `ε_PA` is below one for a total at most one. -/
theorem liftedPrivacyAmplificationError_lt_one (x n : ℕ) {ε_tot : ℝ} (h : ε_tot ≤ 1) :
    liftedPrivacyAmplificationError x n ε_tot < 1 := by
  have hg : (1 : ℝ) ≤ (deFinettiPrefactor x n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (deFinettiPrefactor_pos x n))
  rw [liftedPrivacyAmplificationError, div_lt_one (by positivity)]
  linarith

/-- **`log₂(1/ε_PA) = 1 + log₂(1/ε_tot) + log₂ g_{n,x}`** at the lifted `ε_PA`. -/
theorem logb_inv_liftedPrivacyAmplificationError (x n : ℕ) {ε_tot : ℝ} (h : 0 < ε_tot) :
    Real.logb 2 (liftedPrivacyAmplificationError x n ε_tot)⁻¹
      = 1 + Real.logb 2 ε_tot⁻¹ + Real.logb 2 (deFinettiPrefactor x n : ℝ) := by
  have hg : (0 : ℝ) < (deFinettiPrefactor x n : ℝ) := by
    exact_mod_cast deFinettiPrefactor_pos x n
  rw [liftedPrivacyAmplificationError, inv_div,
    show 2 * (deFinettiPrefactor x n : ℝ) / ε_tot
      = 2 * (ε_tot⁻¹ * (deFinettiPrefactor x n : ℝ)) from by field_simp,
    Real.logb_mul (by norm_num) (by positivity),
    Real.logb_mul (by positivity) (ne_of_gt hg), Real.logb_self_eq_one (by norm_num)]
  ring

/-- Inverse powers of two add their exponent to the lifted privacy-amplification logarithm. -/
lemma logb_inv_liftedPrivacyAmplificationError_inv_two_pow (x n k : ℕ) :
    Real.logb 2 (liftedPrivacyAmplificationError x n ((2 : ℝ) ^ k)⁻¹)⁻¹ =
      (k : ℝ) + 1 + Real.logb 2 (deFinettiPrefactor x n : ℝ) := by
  rw [logb_inv_liftedPrivacyAmplificationError x n (by positivity), inv_inv,
    Real.logb_self_pow (by norm_num) (by norm_num)]
  ring

/-- **A larger postselection prefactor gives a shorter lifted key.**  In particular the
Bell-symmetric `x = 4` comparator is at least as long as the generic `x = 16` one. -/
theorem liftedLiteratureKeyLength_anti_prefactor {x y n nK ℓEV leak : ℕ} {Q δ ε_tot : ℝ}
    (hnK : 0 < nK) (h0 : 0 < ε_tot) (h1 : ε_tot ≤ 1)
    (hxy : deFinettiPrefactor x n ≤ deFinettiPrefactor y n) :
    liftedLiteratureKeyLength y n nK ℓEV leak Q δ ε_tot
      ≤ liftedLiteratureKeyLength x n nK ℓEV leak Q δ ε_tot := by
  have hgx : (1 : ℝ) ≤ (deFinettiPrefactor x n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (deFinettiPrefactor_pos x n))
  have hgxy : (deFinettiPrefactor x n : ℝ) ≤ (deFinettiPrefactor y n : ℝ) := by
    exact_mod_cast hxy
  have hle : liftedPrivacyAmplificationError y n ε_tot
      ≤ liftedPrivacyAmplificationError x n ε_tot := by
    rw [liftedPrivacyAmplificationError, liftedPrivacyAmplificationError]
    exact div_le_div_of_nonneg_left h0.le (by positivity) (by linarith)
  have hP := literatureFiniteSizePenalty_le_of_le nK hnK
    (liftedPrivacyAmplificationError_pos y n h0) hle
    (liftedPrivacyAmplificationError_lt_one x n h1)
  rw [liftedLiteratureKeyLength, liftedLiteratureKeyLength, literatureKeyLength,
    literatureKeyLength]
  linarith

/-- The Bell-symmetric prefactor `C(n + 3, 3)` is at most the generic `C(n + 15, 15)`. -/
theorem deFinettiPrefactor_four_le_sixteen (n : ℕ) :
    deFinettiPrefactor 4 n ≤ deFinettiPrefactor 16 n := by
  change Nat.choose (n + 3) 3 ≤ Nat.choose (n + 15) 15
  rw [show n + 3 = 3 + n from by omega, Nat.choose_symm_add,
    show n + 15 = 15 + n from by omega, Nat.choose_symm_add]
  exact Nat.choose_le_choose n (by omega)

end QKD.BB84.Comparison

end -- noncomputable section
