import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.HammingBall
import QCryptLean.Quantum.Bases.Basic
import QCryptLean.Quantum.Bases.Support
import QCryptLean.Quantum.Bases.Walsh
import QCryptLean.Quantum.Operators.BraKet

/-!
# Native uncertainty bounds for Walsh support in a Hamming ball

The support remains a finite set of bit strings and outcomes use that same
Boolean function register. The scalar entropy estimate is reused from Math.
-/

open Quantum.Operators Math.ClassicalEntropy
open scoped BigOperators

noncomputable section

namespace Quantum.Bases

variable {n r : ℕ} {p : ℝ}

/-- **Walsh support in a Hamming ball bounds every computational outcome probability.**

If a unit vector of `ℂ^{2ⁿ}` is a combination of Walsh–Hadamard basis kets indexed by bit
strings within Hamming distance `r` of some centre `c`, and `r ≤ p·n` for a relative radius
`p ∈ [0, 1/2]`, then every computational-basis outcome has probability at most
`2^{n·h(p) − n}`.

The centre `c` is arbitrary: only the *size* of the support enters, through the Hamming-ball
volume.  The three inputs are flatness of the Walsh basis (`2ⁿ` equal-modulus coordinates),
Cauchy–Schwarz over the support, and the entropy bound on the ball volume. -/
theorem normSq_stdKet_dag_walshCombination_le (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2)
    (hr : (r : ℝ) ≤ p * (n : ℝ)) (c : Fin n → Bool) (J : Finset (Fin n → Bool))
    (hJ : ∀ e ∈ J, hammingDist c e ≤ r) (α : (Fin n → Bool) → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1) (w : Fin n → Bool) :
    Complex.normSq (((stdKet w).dag * ketCombination J α walshKet : ℂ)) ≤
      (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p - (n : ℝ)) := by
  classical
  -- Flatness of the Walsh basis: the probability is at most `|J| / 2ⁿ`.
  have hflat :=
    (stdKet_walshKet_mutuallyUnbiased n).normSq_combination_le_card_div w J α hnorm
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hflat
  -- The support sits inside a Hamming ball, whose volume obeys the entropy bound.
  have hsub : J ⊆ Finset.univ.filter fun y : Fin n → Bool => hammingDist c y ≤ r := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hJ e he⟩
  have hcard : (J.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p) := by
    have hle : (J.card : ℝ) ≤
        ((Finset.univ.filter fun y : Fin n → Bool => hammingDist c y ≤ r).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hball := card_filter_hammingDist_le_two_pow_of_le (ι := Fin n) c hp0 hp_half
      (by simpa using hr)
    exact hle.trans (by simpa using hball)
  -- Divide the volume bound by the dimension.
  have hdim : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine le_trans hflat ?_
  rw [hdim, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), div_le_div_iff_of_pos_right hpos]
  exact hcard

/-- **Surprisal form.**  Under the hypotheses of `normSq_stdKet_dag_walshCombination_le`, an
outcome of positive probability carries at least `n · (1 − h(p))` bits:

  `n · (1 − h(p)) ≤ −log₂ ‖⟨w|ψ⟩‖²`.

At `p = 0` (an exactly determined Walsh string) this is the full `n` bits; it degrades to `0` as
`p → 1/2`, where `h(p) → 1` and the support may be the whole space. -/
theorem le_neg_logb_normSq_stdKet_dag_walshCombination (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2)
    (hr : (r : ℝ) ≤ p * (n : ℝ)) (c : Fin n → Bool) (J : Finset (Fin n → Bool))
    (hJ : ∀ e ∈ J, hammingDist c e ≤ r) (α : (Fin n → Bool) → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1) (w : Fin n → Bool)
    (hprob : 0 < Complex.normSq (((stdKet w).dag * ketCombination J α walshKet : ℂ))) :
    (n : ℝ) * (1 - binaryEntropyBits p) ≤
      -Real.logb 2
        (Complex.normSq (((stdKet w).dag * ketCombination J α walshKet : ℂ))) := by
  have hbound := normSq_stdKet_dag_walshCombination_le hp0 hp_half hr c J hJ α hnorm w
  have hmono := Real.logb_le_logb_of_le one_lt_two hprob hbound
  have hrw : Real.logb 2 ((2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p - (n : ℝ)))
      = (n : ℝ) * binaryEntropyBits p - (n : ℝ) :=
    Real.logb_rpow (by norm_num) (by norm_num)
  rw [hrw] at hmono
  have hexpand : (n : ℝ) * (1 - binaryEntropyBits p)
      = (n : ℝ) - (n : ℝ) * binaryEntropyBits p := by ring
  rw [hexpand]
  linarith

end Quantum.Bases

end
