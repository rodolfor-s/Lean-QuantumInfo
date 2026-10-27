import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.QKD.BB84.SelectionData

/-!
# Bell entropy floors with clamped and free Rényi penalties

`bellRenyiClampedFloor` is the entropy floor used with Bell postselection at the
Dupuis–Fawzi Cor IV.2 penalty with the binary variance bound `binaryVarianceBound = log₂²(1+√2)`
(the bound `V(X|B) ≤ log₂²(1+√2)`, `condVariance_le_logb_sq_of_card_eq_two`), at a general
test-set split point `m` (key-round count `keyRounds n m = n − m`). Pure scalar definition;
no quantum content.

## Floor variants

`bellRenyiClampedFloor` uses `clampedRenyiPenalty` at the clamped Rényi offset.
`bellRenyiWindowFloor` uses `renyiPenalty` at a supplied offset, keeping the window edge `Q + 2·δ`.
`bellRenyiFloor` also takes a free phase-error deviation and uses the edge `Q + δ + dev`.
These match the entropy terms in `BellRenyiWindowKeyRate` and `BellRenyiKeyRate`.
The separate Bell postselection charge is added later; none of these floors includes it.

## Magnitude

At `n = 6·10⁶`, `m = 200 000` (so `n_K = 5 800 000`) and `ε_AEP = 2⁻⁴³¹` the naive (Bennett-style)
finite-size penalty is `193 993.66` bits against
`clampedRenyiPenalty binaryVarianceBound ≈ 110 340` bits — a factor `≈ 1.758`.
Read as admissible key length on the Bell–Rényi theorem that is `≈ 83 653` bits of `ℓ` out of
`4 708 755`, i.e. `+1.78 %`.

## Window and deviation

Alongside the free-β axis, `bellRenyiFloor` moves the entropy edge of the
rate factor from the doubled window edge `Q + 2·δ` to the deviation edge `Q + δ + dev`: the window
`δ` keeps only its protocol role (accept-test half-width), the **deviation** `dev` is where the
floor is charged, and `dev = δ` gives the doubled-window level
(`bellRenyiFloor_self`).  This is the separation of Nahar et al. 2024
(arXiv:2403.11851) Lemma 9 Eq. 44 with §V.C.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`), `\label{lem:divergence-variance-general-bounds}` (`:394`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), `\label{lem:groupPurification}`
(`main.tex:354`), §V.C (`main.tex:909` — the general test-set size `m`; `main.tex:913` —
`n_key = n − m`).
-/

open Math.Combinatorics

open InfoTheory.Renyi

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.FiniteKey

/-- **The Bell carried floor level at the Rényi Cor IV.2 penalty and a general test-set
size `m`.**

The rate factor
`(n_K/log 2)·(log 2 − h₂(Q+2δ))` at `n_K = keyRounds n m = n − m`, minus the Cor IV.2
binary-variance-bound finite-size penalty
`clampedRenyiPenalty binaryVarianceBound n_K εTensor`. The reference is
the component’s own quantum marginal.

The later purifying-register extension charges `2·log₂ C(n+3,3)` at the full `n`.
The component floor defined here has no de Finetti charge.

**The penalty's copy count IS the key-round count** `keyRounds n m`: the AEP lift is
taken over the `n_K` key rounds, and that is the same `n_K` the rate factor scopes.  A copy count
larger than the rate scope would fund a penalty the entropy does not pay for.

**No hypothesis relating `m` and `n` appears.**  The split point enters only through the key-round
count, so `m = 0` (no test rounds, `n_K = n`) and `m ≥ n` (`n_K = 0`, the level collapses to
`−clampedRenyiPenalty binaryVarianceBound 0 ε`) are both covered and both degenerate.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`)
`\label{cor:continuity-bound-halpha_new}` (`:784`), `\label{eq_eathmin_halpha}` (`:1053`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), §V.C (`main.tex:909`, `:913`). -/
noncomputable def bellRenyiClampedFloor (n m : ℕ) (Q δ εTensor : ℝ) : ℝ :=
  (keyRounds n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    clampedRenyiPenalty binaryVarianceBound (keyRounds n m) εTensor

/-- A positive Bell floor after postselection, error-correction and verification charges
requires the test-set size to be strictly below the total round count. -/
lemma lt_of_bellRenyiClampedFloor_charged_pos
    {n m ℓEV leakEC : ℕ} {Q δ εTensor : ℝ}
    (hkEVpos : 0 < bellRenyiClampedFloor n m Q δ εTensor -
      2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) :
    m < n := by
  have hpen := clampedRenyiPenalty_nonneg binaryVarianceBound
    binaryVarianceBound_pos.le (keyRounds n m) εTensor
  have hlog : 0 ≤ Real.log (bellSymmetricDim n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (bellSymmetricDim_pos n).ne')
  have hcharge : 0 ≤ 2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 :=
    div_nonneg (by linarith) (Real.log_pos one_lt_two).le
  by_contra hmn
  have hzero : keyRounds n m = 0 := Nat.sub_eq_zero_of_le (by omega)
  rw [bellRenyiClampedFloor, hzero, Nat.cast_zero, zero_div, zero_mul] at hkEVpos
  rw [hzero] at hpen
  have hleak : (0 : ℝ) ≤ leakEC := Nat.cast_nonneg _
  have hEV : (0 : ℝ) ≤ ℓEV := Nat.cast_nonneg _
  linarith

/-- **The Bell carried floor level at the Rényi Cor IV.2 penalty charged at a free
Rényi offset `β`, and a general test-set size `m`.**

Same expression as `bellRenyiClampedFloor` with the Dupuis–Fawzi Cor IV.2 penalty
evaluated at an arbitrary admissible `β ∈ (0, 1)` (`renyiPenalty`)
instead of at the clamped optimiser `clampedRenyiOffset`.  The free-β version lets the Bell–Rényi
BB84 theorem pick any admissible offset.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`)
`\label{cor:continuity-bound-halpha_new}` (`:784`), `\label{eq_eathmin_halpha}` (`:1053`);
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`). -/
noncomputable def bellRenyiWindowFloor (n m : ℕ) (Q δ εTensor β : ℝ) : ℝ :=
  (keyRounds n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    renyiPenalty binaryVarianceBound (keyRounds n m) εTensor β

/-- The fixed-β⋆ floor level is the free-β floor level at `β = clampedRenyiOffset …`. -/
lemma bellRenyiClampedFloor_eq_bellRenyiWindowFloor (n m : ℕ) (Q δ εTensor : ℝ) :
    bellRenyiClampedFloor n m Q δ εTensor
      = bellRenyiWindowFloor n m Q δ εTensor
          (clampedRenyiOffset binaryVarianceBound (keyRounds n m) εTensor) :=
  rfl

/-- **The Bell carried floor level at the Rényi Cor IV.2 penalty charged at a free
Rényi offset `β`, a general test-set size `m`, and a free phase-error deviation.**

The same two terms as `bellRenyiWindowFloor`, with the entropy argument of the
key-scoped phase-error AEP rate moved from the window edge `Q + 2·δ` (where the window half-width
`δ` is charged twice: once as the accept-test window, once as the deviation between the window
edge and the phase-error rate the floor is charged at) to the general deviation edge `Q + δ + dev`.
Here `δ = p.tolerance` keeps only its protocol role — the accept-test window — and `dev` is the
phase-error **deviation**; `dev = δ` gives the doubled-window level up to the arithmetic rewrite
`δ + δ = 2 * δ`.

This is the separation of Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44 with §V.C: the entropy floor is charged at the soundness edge, not at the
completeness window. -/
noncomputable def bellRenyiFloor
    (n m : ℕ) (Q δ dev εTensor β : ℝ) : ℝ :=
  (keyRounds n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + δ + dev)) -
    renyiPenalty binaryVarianceBound (keyRounds n m) εTensor β

/-- The doubled-window free-β level is `bellRenyiFloor` at `dev = δ` (up to `δ + δ = 2 * δ`). -/
lemma bellRenyiFloor_self (n m : ℕ) (Q δ εTensor β : ℝ) :
    bellRenyiFloor n m Q δ δ εTensor β
      = bellRenyiWindowFloor n m Q δ εTensor β := by
  unfold bellRenyiFloor bellRenyiWindowFloor
  rw [add_assoc, two_mul]

end QKD.BB84.FiniteKey

end -- noncomputable section
