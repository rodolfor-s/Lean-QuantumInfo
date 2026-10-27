import QCryptLean.Math.SpectralTheory.ExteriorPowerNorm
import QCryptLean.Math.SpectralTheory.LiebThirringHigher

/-!
# From weak log-majorization to power sums

Abel summation and logarithmic majorization compare power sums of nonnegative antitone
sequences.

## Main declarations

Main results include `prod_le_to_sum_pow_le_of_antitone`.

## References

See the mathematical references in the declaration docstrings.
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory


/-- **Abel summation core** for the weak-log-majorization descent.

If `w` is non-negative and non-increasing on `[0,N)` and every leading partial
sum of `u` is non-negative (`0 ≤ Σ_{i<k} uᵢ` for `k ≤ N`), then the weighted sum
`Σ_{i<N} wᵢ uᵢ` is non-negative.

Proof by summation by parts (`Finset.sum_range_by_parts`): the boundary term
`w_{N-1}·(Σ_{i<N} uᵢ)` is non-negative, and each interior term
`(w_{i+1}-wᵢ)·(Σ_{j≤i} uⱼ)` is `≤ 0` (a non-positive increment times a
non-negative partial sum), so its subtraction adds a non-negative quantity.
Reference: Marshall-Olkin, *Inequalities: Theory of Majorization*, 5.A (Abel
summation in the weak-majorization argument). -/
private lemma sum_mul_nonneg_of_antitone_of_sum_nonneg {N : ℕ} (w u : ℕ → ℝ)
    (hw0 : ∀ i, i < N → 0 ≤ w i) (hwA : ∀ i, i + 1 < N → w (i + 1) ≤ w i)
    (hU : ∀ k, k ≤ N → 0 ≤ ∑ i ∈ Finset.range k, u i) :
    0 ≤ ∑ i ∈ Finset.range N, w i * u i := by
  have key : ∑ i ∈ Finset.range N, w i * u i
      = w (N - 1) * (∑ i ∈ Finset.range N, u i)
        - ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), u j) := by
    simpa [smul_eq_mul] using Finset.sum_range_by_parts (fun i => w i) (fun i => u i) N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  rw [key]
  have hN1 : N - 1 < N := Nat.sub_lt hN (by norm_num)
  have h1 : 0 ≤ w (N - 1) * ∑ i ∈ Finset.range N, u i :=
    mul_nonneg (hw0 _ hN1) (hU N le_rfl)
  have h2 : ∑ i ∈ Finset.range (N - 1),
      (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), u j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    rw [Finset.mem_range] at hi
    have hi' : i + 1 < N := by omega
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [hwA i hi']
    · exact hU (i + 1) (by omega)
  linarith

/-- **Weak log-majorization ⟹ weak majorization, strictly-positive case**
(`p = 1`, range form): for `a, b` strictly positive and `a` non-increasing on
`[0,n)` with dominated leading partial products (`∏_{i<k} aᵢ ≤ ∏_{i<k} bᵢ` for
`k ≤ n`), the linear sums are ordered: `Σ_{i<n} aᵢ ≤ Σ_{i<n} bᵢ`.

Proof: set `uᵢ = log bᵢ - log aᵢ`. The partial sums `Σ_{i<k} uᵢ =
log(∏ b) - log(∏ a) ≥ 0` by `hprod` (logarithm is monotone and the products are
positive). The tangent-line bound `log x ≤ x - 1` (`Real.log_le_sub_one_of_pos`)
gives `aᵢ uᵢ = aᵢ·log(bᵢ/aᵢ) ≤ bᵢ - aᵢ` termwise, so
`Σ (bᵢ - aᵢ) ≥ Σ aᵢ uᵢ ≥ 0` where the last inequality is the Abel core
`sum_mul_nonneg_of_antitone_of_sum_nonneg` with weight `w = a` (non-negative, non-increasing) and
the
non-negative partial sums of `u`. Reference: Marshall-Olkin, *Inequalities*, 5.A;
Bhatia, *Matrix Analysis*, III. -/
private lemma weak_logMaj_sum_le_of_pos {n : ℕ} (a b : ℕ → ℝ)
    (ha0 : ∀ i, i < n → 0 < a i) (hb0 : ∀ i, i < n → 0 < b i)
    (haA : ∀ i j, i ≤ j → a j ≤ a i)
    (hprod : ∀ k, k ≤ n → ∏ i ∈ Finset.range k, a i ≤ ∏ i ∈ Finset.range k, b i) :
    ∑ i ∈ Finset.range n, a i ≤ ∑ i ∈ Finset.range n, b i := by
  set u : ℕ → ℝ := fun i => Real.log (b i) - Real.log (a i) with hu
  have hUpos : ∀ k, k ≤ n → 0 ≤ ∑ i ∈ Finset.range k, u i := by
    intro k hk
    have hlogprod : ∀ (f : ℕ → ℝ), (∀ i, i < n → 0 < f i) →
        ∑ i ∈ Finset.range k, Real.log (f i) = Real.log (∏ i ∈ Finset.range k, f i) := by
      intro f hf
      rw [Real.log_prod]
      intro i hi
      rw [Finset.mem_range] at hi
      exact (hf i (lt_of_lt_of_le hi hk)).ne'
    have hsum : ∑ i ∈ Finset.range k, u i
        = Real.log (∏ i ∈ Finset.range k, b i) - Real.log (∏ i ∈ Finset.range k, a i) := by
      simp only [hu, Finset.sum_sub_distrib]
      rw [hlogprod b hb0, hlogprod a ha0]
    rw [hsum, sub_nonneg]
    apply Real.log_le_log
    · exact Finset.prod_pos (fun i hi => ha0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
    · exact hprod k hk
  have habel : 0 ≤ ∑ i ∈ Finset.range n, a i * u i :=
    sum_mul_nonneg_of_antitone_of_sum_nonneg a u (fun i hi => (ha0 i hi).le) (fun i hi => haA i
      (i+1) (Nat.le_succ i)) hUpos
  have hterm : ∀ i ∈ Finset.range n, a i * u i ≤ b i - a i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hai := ha0 i hi
    have hbi := hb0 i hi
    have hlog : u i = Real.log (b i / a i) := by
      rw [hu]; rw [Real.log_div hbi.ne' hai.ne']
    rw [hlog]
    have hx : Real.log (b i / a i) ≤ b i / a i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hbi hai)
    have hmul := mul_le_mul_of_nonneg_left hx hai.le
    rw [mul_sub, mul_div_cancel₀ _ hai.ne', mul_one] at hmul
    linarith
  have hsum_term : ∑ i ∈ Finset.range n, a i * u i ≤ ∑ i ∈ Finset.range n, (b i - a i) :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum_term
  linarith

/-- **Weak log-majorization ⟹ weak majorization** (`p = 1`, general form): for
non-increasing non-negative `a, b : ℕ → ℝ` with dominated leading partial
products (`∏_{i<k} aᵢ ≤ ∏_{i<k} bᵢ` for every `k`), the linear sums over `Fin N`
are ordered: `Σᵢ aᵢ ≤ Σᵢ bᵢ`.

Reduces the possibly-degenerate general case to the strictly-positive core
`weak_logMaj_sum_le_of_pos`: since `a` is non-increasing and non-negative, its
positive entries form a prefix `[0,j)`; `b` is forced strictly positive on `[0,j)`
by `hprod` (a zero `bᵢ` with `i < j` would make a leading product vanish while the
corresponding `a`-product is positive); the entries on `[j,N)` of `a` vanish, and
the extra `b`-entries are non-negative. Reference: Marshall-Olkin, *Inequalities*,
5.A; Bhatia, *Matrix Analysis*, III. -/
private lemma weak_logMaj_sum_le {N : ℕ} (a b : ℕ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (haA : Antitone a) (_hbA : Antitone b)
    (hprod : ∀ k, ∏ i ∈ Finset.range k, a i ≤ ∏ i ∈ Finset.range k, b i) :
    ∑ i : Fin N, a i ≤ ∑ i : Fin N, b i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => a i) N, Fin.sum_univ_eq_sum_range (fun i => b i) N]
  classical
  obtain ⟨j, hjN, hjpos, hjzero⟩ :
      ∃ j, j ≤ N ∧ (∀ i, i < j → 0 < a i) ∧ (∀ i, j ≤ i → i < N → a i = 0) := by
    by_cases h : ∃ i, i < N ∧ a i = 0
    · have hex : ∃ i, i < N ∧ a i = 0 := h
      have hspec := Nat.find_spec hex
      refine ⟨Nat.find hex, ?_, ?_, ?_⟩
      · exact le_of_lt hspec.1
      · intro i hi
        have hmin := Nat.find_min hex hi
        push Not at hmin
        rcases lt_or_ge i N with hiN | hiN
        · exact lt_of_le_of_ne (ha0 i) (Ne.symm (hmin hiN))
        · exact absurd (lt_of_lt_of_le hi (le_trans (le_of_lt hspec.1) hiN)) (by omega)
      · intro i hji hiN
        have hle : a i ≤ a (Nat.find hex) := haA hji
        rw [hspec.2] at hle
        exact le_antisymm hle (ha0 i)
    · push Not at h
      exact ⟨N, le_rfl, fun i hi => lt_of_le_of_ne (ha0 i) (Ne.symm (h i hi)),
        fun i hji hiN => absurd hiN (by omega)⟩
  have hbpos : ∀ i, i < j → 0 < b i := by
    intro i hi
    by_contra hb
    push Not at hb
    have hbz : b i = 0 := le_antisymm hb (hb0 i)
    have hbprod : ∏ l ∈ Finset.range (i + 1), b l = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self i)) hbz
    have haprod : 0 < ∏ l ∈ Finset.range (i + 1), a l :=
      Finset.prod_pos (fun l hl => hjpos l (lt_of_lt_of_le (Finset.mem_range.mp hl) hi))
    have hcontra := hprod (i + 1)
    rw [hbprod] at hcontra
    linarith
  have hsumA : ∑ i ∈ Finset.range N, a i = ∑ i ∈ Finset.range j, a i := by
    rw [← Finset.sum_range_add_sum_Ico a hjN]
    have hzeroIco : ∑ i ∈ Finset.Ico j N, a i = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [Finset.mem_Ico] at hi; exact hjzero i hi.1 hi.2)
    rw [hzeroIco, add_zero]
  have hsumB : ∑ i ∈ Finset.range j, b i ≤ ∑ i ∈ Finset.range N, b i := by
    rw [← Finset.sum_range_add_sum_Ico b hjN]
    have hnn : 0 ≤ ∑ i ∈ Finset.Ico j N, b i := Finset.sum_nonneg (fun i _ => hb0 i)
    linarith
  have hcore : ∑ i ∈ Finset.range j, a i ≤ ∑ i ∈ Finset.range j, b i :=
    weak_logMaj_sum_le_of_pos a b (fun i hi => hjpos i hi) (fun i hi => hbpos i hi)
      (fun i k hik => haA hik) (fun k _ => hprod k)
  rw [hsumA]
  linarith

/-- **Weak-log-majorization sum bound** (Karamata / Bhatia III): for two
non-increasing nonnegative real families `a, b : ℕ → ℝ` whose leading partial
products are dominated (`∏_{i<k} aᵢ ≤ ∏_{i<k} bᵢ` for every `k`), the sums of
squares are ordered: `Σᵢ aᵢ² ≤ Σᵢ bᵢ²`.

This is the real-analytic core of the singular-value descent: weak
log-majorization of nonneg non-increasing families, composed with the increasing
convex map `t ↦ t²` (equivalently `s ↦ e^{2s}` on logs), yields weak
majorization of the squared families and hence the sum inequality. The carrier
hypotheses (`Antitone a`, `Antitone b`, nonnegativity, and the dominated partial
products `hprod`) are exactly the weak-log-majorization data; no equality at
`k = N` is required because the convex map `e^{2s}` is increasing.

This real-analysis lemma expresses the required weak-log-majorization bound. Reference: Bhatia,
*Matrix
Analysis*, III (majorization); Marshall-Olkin, *Inequalities: Theory of
Majorization*, 3.A / 5.A (weak log majorization ⟹ Schur-convex sum order). -/
lemma prod_le_to_sum_pow_le_of_antitone {N : ℕ} (a b : ℕ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (haA : Antitone a) (hbA : Antitone b)
    (hprod : ∀ k, ∏ i ∈ Finset.range k, a i ≤ ∏ i ∈ Finset.range k, b i) :
    ∑ i : Fin N, (a i) ^ 2 ≤ ∑ i : Fin N, (b i) ^ 2 := by
  -- Apply the `p = 1` linear bound to the squared families: `aᵢ², bᵢ²` are
  -- non-increasing, non-negative, with dominated partial products (squaring is
  -- monotone on `[0,∞)` and the products are non-negative).
  have hsq : ∀ k, ∏ i ∈ Finset.range k, (a i) ^ 2 ≤ ∏ i ∈ Finset.range k, (b i) ^ 2 := by
    intro k
    rw [Finset.prod_pow, Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => ha0 i)) (hprod k) 2
  exact weak_logMaj_sum_le (fun i => (a i) ^ 2) (fun i => (b i) ^ 2)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _)
    (fun i j h => pow_le_pow_left₀ (ha0 j) (haA h) 2)
    (fun i j h => pow_le_pow_left₀ (hb0 j) (hbA h) 2) hsq


end Math.SpectralTheory
