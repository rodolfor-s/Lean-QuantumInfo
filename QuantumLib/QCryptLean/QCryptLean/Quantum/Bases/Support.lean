import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.Quantum.Bases.Basic
import QCryptLean.Quantum.Operators.BraKet

/-!
# Native flat-basis support bounds

Cauchy--Schwarz yields probability and surprisal bounds on arbitrary finite
registers. Empty supports and empty registers are admitted by the statements.
-/

namespace Quantum.Bases

open Quantum.Operators

variable {X ι κ : Type*} [Fintype X]

/-- **Support–overlap Cauchy–Schwarz bound.**  If every overlap `⟨φ | b_e⟩` with `e ∈ J` has
squared modulus at most `c`, then

  `‖⟨φ | ∑_{e ∈ J} α_e b_e⟩‖² ≤ (∑_{e ∈ J} ‖α_e‖²) · (|J| · c)`.

No normalization, orthogonality or sign hypothesis is needed: `J = ∅` gives `0 ≤ 0`, and
nonnegativity of `c` (when `J ≠ ∅`) is already implied by the overlap bound. -/
theorem normSq_bra_mul_ketCombination_le (φ : Bra X) (J : Finset ι) (α : ι → ℂ) (b : ι → Ket X)
    {c : ℝ} (hb : ∀ e ∈ J, Complex.normSq ((φ * b e : ℂ)) ≤ c) :
    Complex.normSq ((φ * ketCombination J α b : ℂ)) ≤
      (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) * c) := by
  rw [bra_mul_ketCombination]
  have htri : ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ≤ ∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖ :=
    (norm_sum_le J _).trans_eq (Finset.sum_congr rfl fun e _ => norm_mul _ _)
  have hsq : ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ^ 2 ≤ (∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hCS : (∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖) ^ 2 ≤
      (∑ e ∈ J, ‖α e‖ ^ 2) * ∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq J (fun e => ‖α e‖) fun e => ‖(φ * b e : ℂ)‖
  have hoverlap : (∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2) ≤ (J.card : ℝ) * c := by
    have h1 : (∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2) ≤ ∑ _e ∈ J, c :=
      Finset.sum_le_sum fun e he => by rw [← Complex.normSq_eq_norm_sq]; exact hb e he
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  have hcoeff : (0 : ℝ) ≤ ∑ e ∈ J, ‖α e‖ ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  calc Complex.normSq (∑ e ∈ J, α e * (φ * b e : ℂ))
      = ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ ≤ (∑ e ∈ J, ‖α e‖ ^ 2) * ∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2 := hsq.trans hCS
    _ ≤ (∑ e ∈ J, ‖α e‖ ^ 2) * ((J.card : ℝ) * c) := mul_le_mul_of_nonneg_left hoverlap hcoeff
    _ = (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) * c) := by
        simp [Complex.normSq_eq_norm_sq]

/-- **The flat-family support bound.**  For families `a`, `b` mutually unbiased in dimension `d`,
a combination of the `b`-kets supported on `J` has every `a`-overlap bounded by

  `‖⟨a_w | ∑_{e ∈ J} α_e b_e⟩‖² ≤ (∑_{e ∈ J} ‖α_e‖²) · (|J| / Fintype.card X)`. -/
theorem IsMutuallyUnbiased.normSq_combination_le {a : κ → Ket X} {b : ι → Ket X}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ) :
    Complex.normSq (((a w).dag * ketCombination J α b : ℂ)) ≤
      (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) / Fintype.card X) := by
  have hbase := normSq_bra_mul_ketCombination_le (a w).dag J α b (c := 1 / (Fintype.card X : ℝ))
    fun e _ => le_of_eq (h w e)
  rwa [show (J.card : ℝ) * (1 / (Fintype.card X : ℝ)) =
    (J.card : ℝ) / Fintype.card X from by rw [mul_one_div]] at hbase

/-- **Bouman–Fehr's flat-basis probability bound.**  A *normalized* combination supported on `J`
in a flat family has every conjugate outcome probability bounded by `|J|/d`. -/
theorem IsMutuallyUnbiased.normSq_combination_le_card_div {a : κ → Ket X} {b : ι → Ket X}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1) :
    Complex.normSq (((a w).dag * ketCombination J α b : ℂ)) ≤ (J.card : ℝ) / Fintype.card X := by
  simpa [hnorm] using h.normSq_combination_le w J α

/-! ## The surprisal form -/

/-- **Surprisal form of the flat-family bound.**  If the outcome `w` of the `a`-measurement has
positive probability on a normalized `b`-combination supported on `J`, then its surprisal is at
least `log₂(d/|J|)`:

  `log₂(d / |J|) ≤ −log₂ ‖⟨a_w | ψ⟩‖²`.

Both `0 < d` and `0 < |J|` are *derived* from positivity of the probability — an empty support or
a zero-dimensional space forces the overlap to vanish — so neither is a hypothesis.  Logarithms
are base two, matching the min-entropy convention; the bound is the per-outcome (unconditional)
surprisal `−log₂ p_w ≥ log₂ d − log₂ |J|`. -/
theorem IsMutuallyUnbiased.logb_card_div_le_neg_logb_normSq {a : κ → Ket X} {b : ι → Ket X}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1)
    (hpos : 0 < Complex.normSq (((a w).dag * ketCombination J α b : ℂ))) :
    Real.logb 2 ((Fintype.card X : ℝ) / (J.card : ℝ)) ≤
      -Real.logb 2 (Complex.normSq (((a w).dag * ketCombination J α b : ℂ))) := by
  have hbound := h.normSq_combination_le_card_div w J α hnorm
  have hmono : Real.logb 2 (Complex.normSq (((a w).dag * ketCombination J α b : ℂ))) ≤
      Real.logb 2 ((J.card : ℝ) / Fintype.card X) :=
    Real.logb_le_logb_of_le one_lt_two hpos hbound
  have hflip : Real.logb 2 ((J.card : ℝ) / Fintype.card X) =
      -Real.logb 2 ((Fintype.card X : ℝ) / (J.card : ℝ)) := by
    rw [← Real.logb_inv, inv_div]
  rw [hflip] at hmono
  linarith

end Quantum.Bases
