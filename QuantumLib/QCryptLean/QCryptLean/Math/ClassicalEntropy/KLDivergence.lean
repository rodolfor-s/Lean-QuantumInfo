import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Classical KL Divergence — Gibbs inequality, variational principle, entropy product rule

Kullback-Leibler divergence and Shannon entropy structural theorems.

## Main definitions
- `classicalKLDiv`: D(p‖q) = Σᵢ pᵢ log(pᵢ/qᵢ)

## Main statements
- `classicalKLDiv_nonneg`: D(p‖q) ≥ 0 (Gibbs inequality)
- `shannonEntropy_add_sum_mul_le_log_sum_exp`: H(r) + Σ rᵢ αᵢ ≤ log(Σ exp(αᵢ))
- `shannonEntropy_product`: H(p ⊗ q) = H(p) + H(q)
- `shannonEntropy_four_le_add_binaryEntropy`: H(X,Y) ≤ H(X) + H(Y)
-/

noncomputable section

namespace Math.ClassicalEntropy

/-!
## Classical KL Divergence

Kullback-Leibler divergence between probability distributions.
-/

/-- Classical KL divergence between two distributions. -/
def classicalKLDiv {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ := by
  classical
  exact ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- Gibbs inequality: Σᵢ pᵢ log(pᵢ/qᵢ) ≥ 0 for probability distributions.

    This is nonnegativity of the classical KL divergence. -/
theorem classicalKLDiv_nonneg {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hq_support : ∀ i, p i > 0 → q i > 0) :
    0 ≤ classicalKLDiv p q := by
  classical
  change 0 ≤ ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)
  -- Main proof using Jensen's inequality
  -- Let S = {i | p i > 0}
  let S := Finset.univ.filter (fun i => p i ≠ 0)
  -- Helper to extract p i ≠ 0 from i ∈ S
  have hS_mem : ∀ i, i ∈ S ↔ p i ≠ 0 := fun i => by simp [S]
  -- The sum simplifies to Σ_{i ∈ S} p i * log(p i / q i)
  have h_eq : ∑ i, (if p i = 0 then 0 else p i * Real.log (p i / q i)) =
      ∑ i ∈ S, p i * Real.log (p i / q i) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr
    · ext i; simp [S]
    · intro i _; rfl
  rw [h_eq]
  -- p i * log(p i / q i) = -p i * log(q i / p i)
  have h_rewrite : ∑ i ∈ S, p i * Real.log (p i / q i) =
      -∑ i ∈ S, p i * Real.log (q i / p i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
    have hqi : 0 < q i := hq_support i hpi
    have h : Real.log (p i / q i) = -Real.log (q i / p i) := by
      rw [Real.log_div (ne_of_gt hpi) (ne_of_gt hqi)]
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt hpi)]
      ring
    rw [h]
    ring
  rw [h_rewrite]
  -- Now apply Jensen: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * q_i/p_i) = log(Σ q_i) ≤ 0
  rw [neg_nonneg]
  -- Need: Σ_{i ∈ S} p i * log(q i / p i) ≤ 0
  -- By Jensen with concave log: Σ p_i log(x_i) ≤ log(Σ p_i x_i) when Σ p_i = 1
  -- First establish that Σ_{i ∈ S} p_i = 1
  have hS_sum : ∑ i ∈ S, p i = 1 := by
    have h_full : ∑ i, p i = ∑ i ∈ S, p i + ∑ i ∈ (Finset.univ \ S), p i := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [hp_sum] at h_full
    have h_zero : ∑ i ∈ (Finset.univ \ S), p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      have : ¬(p i ≠ 0) := fun h => hi ((hS_mem i).mpr h)
      push Not at this
      exact this
    linarith
  -- Apply Jensen: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * q_i/p_i)
  have hconcave : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  -- All q_i / p_i > 0 for i ∈ S
  have h_in_domain : ∀ i ∈ S, q i / p i ∈ Set.Ioi 0 := by
    intro i hi
    have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
    have hqi : 0 < q i := hq_support i hpi
    exact div_pos hqi hpi
  -- All weights are non-negative
  have h_weights_nonneg : ∀ i ∈ S, 0 ≤ p i := by
    intro i _; exact hp_nonneg i
  -- Jensen gives: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * (q_i/p_i))
  have hJensen := hconcave.le_map_sum h_weights_nonneg hS_sum h_in_domain
  -- Simplify: Σ p_i * (q_i / p_i) = Σ q_i (over S)
  have h_simplify : ∑ i ∈ S, p i * (q i / p i) = ∑ i ∈ S, q i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hpi : p i ≠ 0 := (hS_mem i).mp hi
    field_simp
  -- Weighted average: Σ p_i • (q_i / p_i) = Σ q_i (over S)
  have h_smul_eq : ∑ i ∈ S, p i • (q i / p i) = ∑ i ∈ S, q i := by
    simp only [smul_eq_mul]; exact h_simplify
  -- The sum over S is at most 1
  have h_sum_le : ∑ i ∈ S, q i ≤ 1 := by
    calc ∑ i ∈ S, q i ≤ ∑ i, q i := Finset.sum_le_univ_sum_of_nonneg (fun i => hq_nonneg i)
      _ = 1 := hq_sum
  -- Combine: log(Σ_{S} q_i) ≤ log 1 = 0
  calc ∑ i ∈ S, p i * Real.log (q i / p i)
      = ∑ i ∈ S, p i • Real.log (q i / p i) := by simp only [smul_eq_mul]
    _ ≤ Real.log (∑ i ∈ S, p i • (q i / p i)) := hJensen
    _ = Real.log (∑ i ∈ S, q i) := by rw [h_smul_eq]
    _ ≤ Real.log 1 := Real.log_le_log (by
        have hne : S.Nonempty := by
          by_contra h
          simp only [Finset.not_nonempty_iff_eq_empty] at h
          have : ∑ i ∈ S, p i = 0 := by rw [h]; simp
          rw [hS_sum] at this
          exact one_ne_zero this
        obtain ⟨i, hi⟩ := hne
        apply Finset.sum_pos' (fun j _ => hq_nonneg j)
        have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
        have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
        exact ⟨i, hi, hq_support i hpi⟩
      ) h_sum_le
    _ = 0 := Real.log_one

/-- Characterization: x² = x iff x = 0 or x = 1. -/
lemma _root_.Real.sq_eq_self_iff_zero_or_one (x : ℝ) : x^2 = x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have h' : x * (x - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with hx | hx
    · left; exact hx
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-!
## Product Distributions
-/

/-- Entropy is additive for independent probability distributions. -/
theorem shannonEntropy_product {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (q : J → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    shannonEntropy (fun x : I × J => p x.1 * q x.2) =
      shannonEntropy p + shannonEntropy q := by
  have he (x y : ℝ) : entropyTerm (x * y) = y * entropyTerm x + x * entropyTerm y := by
    simp only [entropyTerm_eq_neg_mul_log]
    simpa only [Real.negMulLog_eq_neg, mul_neg] using Real.negMulLog_mul x y
  simp only [shannonEntropy, Fintype.sum_prod_type, he, Finset.sum_add_distrib]
  congr 1
  · simp only [← Finset.sum_mul, hq, one_mul]
  · rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hp, one_mul]

/-- **Shannon entropy subadditivity for 2×2 joint distribution**

For a joint distribution over X,Y with marginals:
- pX = (px0, px1) where px0 = p00 + p10, px1 = p01 + p11
- pY = (py0, py1) where py0 = p00 + p01, py1 = p10 + p11

We have: H(X,Y) ≤ H(X) + H(Y)

This is equivalent to mutual information I(X;Y) = D_KL(p_XY || p_X ⊗ p_Y) ≥ 0. -/
theorem shannonEntropy_four_le_add_binaryEntropy (p00 p01 p10 p11 : ℝ)
    (h00 : 0 ≤ p00) (h01 : 0 ≤ p01) (h10 : 0 ≤ p10) (h11 : 0 ≤ p11)
    (h_sum : p00 + p01 + p10 + p11 = 1) :
    shannonEntropy ![p00, p01, p10, p11] ≤
      binaryEntropy (p01 + p11) + binaryEntropy (p10 + p11) := by
  -- Gibbs bound for one cell `a` lying below its two marginals `x`, `y`:
  -- `η(a) ≤ -a log x - a log y + (x y - a)`, from `log t ≤ t - 1` at `t = x y / a`.
  have cell : ∀ a x y : ℝ, 0 ≤ a → a ≤ x → a ≤ y →
      Real.negMulLog a ≤ -(a * Real.log x) - a * Real.log y + (x * y - a) := by
    intro a x y ha hax hay
    rcases ha.eq_or_lt with rfl | ha
    · linarith [mul_nonneg hax hay, Real.negMulLog_zero]
    · have hx : 0 < x := ha.trans_le hax
      have hy : 0 < y := ha.trans_le hay
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hx hy) ha)
      rw [Real.log_div (mul_pos hx hy).ne' ha.ne', Real.log_mul hx.ne' hy.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog ha.le
      have hcancel : a * (x * y / a) = x * y := mul_div_cancel₀ (x * y) ha.ne'
      rw [Real.negMulLog]
      linarith
  -- the four cells, against the marginals `P(X = i) = p0i + p1i` and `P(Y = j) = pj0 + pj1`
  have k00 := cell p00 (p00 + p10) (p00 + p01) h00
    (le_add_of_nonneg_right h10) (le_add_of_nonneg_right h01)
  have k01 := cell p01 (p01 + p11) (p00 + p01) h01
    (le_add_of_nonneg_right h11) (le_add_of_nonneg_left h00)
  have k10 := cell p10 (p00 + p10) (p10 + p11) h10
    (le_add_of_nonneg_left h00) (le_add_of_nonneg_right h11)
  have k11 := cell p11 (p01 + p11) (p10 + p11) h11
    (le_add_of_nonneg_left h01) (le_add_of_nonneg_left h10)
  -- the product of the marginals is normalized
  have hprod : (p00 + p10) * (p00 + p01) + (p01 + p11) * (p00 + p01)
      + (p00 + p10) * (p10 + p11) + (p01 + p11) * (p10 + p11) = 1 := by
    linear_combination (p00 + p01 + p10 + p11 + 1) * h_sum
  -- both sides as sums of `η = negMulLog` of nonnegative weights
  have hX0 : 1 - (p01 + p11) = p00 + p10 := by linarith
  have hY0 : 1 - (p10 + p11) = p00 + p01 := by linarith
  simp only [shannonEntropy, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, binaryEntropy,
    hX0, hY0]
  rw [entropyTerm_eq_negMulLog _ h00, entropyTerm_eq_negMulLog _ h01,
    entropyTerm_eq_negMulLog _ h10, entropyTerm_eq_negMulLog _ h11,
    entropyTerm_eq_negMulLog _ (add_nonneg h01 h11),
    entropyTerm_eq_negMulLog _ (add_nonneg h00 h10),
    entropyTerm_eq_negMulLog _ (add_nonneg h10 h11),
    entropyTerm_eq_negMulLog _ (add_nonneg h00 h01)]
  -- sum the four cell bounds: the `log`-weights regroup into the marginal entropies
  simp only [Real.negMulLog] at k00 k01 k10 k11 ⊢
  linarith

/-- **Classical Gibbs variational principle**: For a probability distribution r and reals α,
    H(r) + Σ rᵢ αᵢ ≤ log(Σ exp(αᵢ)).

    Proof: Define qᵢ = exp(αᵢ)/Z. Then D_KL(r‖q) = -H(r) - Σ rᵢ αᵢ + log Z ≥ 0. -/
lemma shannonEntropy_add_sum_mul_le_log_sum_exp {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (α : ι → ℝ)
    (hr_nonneg : ∀ i, 0 ≤ r i) (hr_sum : ∑ i, r i = 1) :
    shannonEntropy r + ∑ i, r i * α i ≤
    Real.log (∑ i, Real.exp (α i)) := by
  -- Define Z = Σ exp(αᵢ) and q = exp(α)/Z (Gibbs distribution)
  set Z := ∑ i, Real.exp (α i) with hZ_def
  have hZ_pos : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  set q := (fun i => Real.exp (α i) / Z) with hq_def
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => div_nonneg (Real.exp_pos _).le hZ_pos.le
  have hq_sum : ∑ i, q i = 1 := by
    simp only [hq_def]; rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ_pos)
  have hq_pos : ∀ i, 0 < q i := fun i => div_pos (Real.exp_pos _) hZ_pos
  -- Apply Gibbs inequality: D_KL(r‖q) ≥ 0
  have hKL := classicalKLDiv_nonneg r q hr_nonneg hq_nonneg hr_sum hq_sum
    (fun i _ => hq_pos i)
  -- Key: rewrite each KL term as rᵢ log rᵢ - rᵢ αᵢ + rᵢ log Z
  have hterm : ∀ i, (if r i = 0 then 0 else r i * Real.log (r i / q i)) =
      (if r i = 0 then (0 : ℝ) else r i * Real.log (r i)) +
      (- r i * α i + r i * Real.log Z) := by
    intro i
    by_cases hri : r i = 0
    · simp [hri]
    · simp only [hri, ↓reduceIte]
      have hri_pos : 0 < r i := lt_of_le_of_ne (hr_nonneg i) (Ne.symm hri)
      rw [hq_def, Real.log_div hri_pos.ne' (ne_of_gt (hq_pos i))]
      rw [Real.log_div (Real.exp_pos _).ne' (ne_of_gt hZ_pos)]
      rw [Real.log_exp]; ring
  -- Sum the expanded terms
  unfold classicalKLDiv at hKL
  simp_rw [hterm, Finset.sum_add_distrib] at hKL
  -- hKL: 0 ≤ Σ(if rᵢ=0 then 0 else rᵢ log rᵢ) + (Σ -rᵢ αᵢ + Σ rᵢ log Z)
  -- Simplify Σ rᵢ log Z = log Z
  have hlogZ : ∑ x, r x * Real.log Z = Real.log Z := by
    rw [← Finset.sum_mul, hr_sum, one_mul]
  rw [hlogZ] at hKL
  -- Simplify Σ -rᵢ αᵢ = -Σ rᵢ αᵢ
  have hneg_sum : ∑ x, -r x * α x = -(∑ x, r x * α x) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext; ring
  rw [hneg_sum] at hKL
  -- Simplify Σ(if rᵢ=0 then 0 else rᵢ log rᵢ) = -shannonEntropy r
  have hH : ∑ x, (if r x = 0 then (0 : ℝ) else r x * Real.log (r x)) =
      -shannonEntropy r := by
    unfold shannonEntropy entropyTerm
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    by_cases hri : r i = 0 <;> simp [hri]
  rw [hH] at hKL
  -- hKL : 0 ≤ -shannonEntropy r + (-Σ rᵢ αᵢ + log Z)
  linarith

/-- Shannon entropy increases under doubly stochastic transformation.

    For any probability distribution p and doubly stochastic matrix D:
      H(p) ≤ H(D·p)

    **Proof sketch**:
    1. entropyTerm = negMulLog is concave on [0, ∞)
    2. For each row i: entropyTerm((D·p)ᵢ) = entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
       (by Jensen's inequality since Dᵢⱼ ≥ 0 and Σⱼ Dᵢⱼ = 1)
    3. Summing over i:
       H(D·p) = Σᵢ entropyTerm((D·p)ᵢ) ≥ Σᵢ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
             = Σⱼ (Σᵢ Dᵢⱼ) entropyTerm(pⱼ) = Σⱼ entropyTerm(pⱼ) = H(p) -/
lemma shannonEntropy_doubly_stochastic_ge {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (D : Matrix ι ι ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_row : ∀ i, ∑ j, D i j = 1)
    (hD_col : ∀ j, ∑ i, D i j = 1) :
    Math.ClassicalEntropy.shannonEntropy p ≤ Math.ClassicalEntropy.shannonEntropy (fun i => ∑ j, D i
        j * p j) := by
  -- The proof uses Jensen's inequality with concave negMulLog
  unfold Math.ClassicalEntropy.shannonEntropy
  -- Goal: Σᵢ entropyTerm(pᵢ) ≤ Σᵢ entropyTerm(Σⱼ Dᵢⱼ pⱼ)
  -- By Jensen, for each i: entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
  have hconcave := Real.concaveOn_negMulLog
  -- First establish bounds on transformed probabilities
  have hDp_nonneg : ∀ i, 0 ≤ ∑ j, D i j * p j := fun i => by
    apply Finset.sum_nonneg; intro j _; exact mul_nonneg (hD_nonneg i j) (hp_nonneg j)
  -- For each i, apply Jensen:
  -- entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)  since entropyTerm = negMulLog is concave
  have hJensen_row : ∀ i,
      Math.ClassicalEntropy.entropyTerm (∑ j, D i j * p j) ≥ ∑ j, D i j *
          Math.ClassicalEntropy.entropyTerm (p j) := by
    intro i
    have hp_in_Ici : ∀ j, j ∈ Finset.univ → p j ∈ Set.Ici (0 : ℝ) := fun j _ => hp_nonneg j
    have hJensen := hconcave.le_map_sum (fun j _ => hD_nonneg i j) (hD_row i) hp_in_Ici
    simp only [smul_eq_mul] at hJensen
    -- Convert from negMulLog to entropyTerm
    have h_lhs : Math.ClassicalEntropy.entropyTerm (∑ j, D i j * p j) =
        Real.negMulLog (∑ j, D i j * p j) := by
      rw [Math.ClassicalEntropy.entropyTerm_eq_negMulLog]; exact hDp_nonneg i
    have h_rhs : ∑ j, D i j * Math.ClassicalEntropy.entropyTerm (p j) =
        ∑ j, D i j * Real.negMulLog (p j) := by
      congr 1; ext j; congr 1; rw [Math.ClassicalEntropy.entropyTerm_eq_negMulLog]; exact hp_nonneg
          j
    rw [h_lhs, h_rhs]
    exact hJensen
  -- Sum over i and exchange order of summation
  calc ∑ i, Math.ClassicalEntropy.entropyTerm (p i)
      = ∑ i, (∑ j, D j i) * Math.ClassicalEntropy.entropyTerm (p i) := by
          congr 1; ext i; rw [hD_col i, one_mul]
    _ = ∑ i, ∑ j, D j i * Math.ClassicalEntropy.entropyTerm (p i) := by
          congr 1; ext i; rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, D j i * Math.ClassicalEntropy.entropyTerm (p i) := Finset.sum_comm
    _ ≤ ∑ j, Math.ClassicalEntropy.entropyTerm (∑ i, D j i * p i) := Finset.sum_le_sum (fun j _ =>
        hJensen_row j)


/-- Any bound on all exponential variational tests also bounds classical relative entropy. -/
lemma classicalKLDiv_le_of_gibbs {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hsupp : ∀ i, 0 < p i → 0 < q i) {D : ℝ}
    (h : ∀ a : ι → ℝ, (∑ i, p i * a i) - Real.log (∑ i, q i * Real.exp (a i)) ≤ D) :
    classicalKLDiv p q ≤ D := by
  classical
  let a (C : ℝ) (i : ι) := if p i = 0 then -C else Real.log (p i / q i)
  let B := ∑ i ∈ Finset.univ.filter (fun i => p i = 0), q i
  have ht (C : ℝ) : (∑ i, p i * a C i) = classicalKLDiv p q := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = 0 <;> simp [a, hi]
  have hz (C : ℝ) : (∑ i, q i * Real.exp (a C i)) = 1 + B * Real.exp (-C) := by
    have he (i : ι) : q i * Real.exp (a C i) =
        (if p i = 0 then q i * Real.exp (-C) else 0) + p i := by
      by_cases hi : p i = 0
      · simp [a, hi]
      · have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
        have hqi := hsupp i hpi
        simp only [a, hi, ↓reduceIte, zero_add, Real.exp_log (div_pos hpi hqi)]
        field_simp
    simp_rw [he]
    rw [Finset.sum_add_distrib, hs]
    simp only [← Finset.sum_filter, B, Finset.sum_mul]
    ring
  have hb (C : ℝ) : classicalKLDiv p q - Real.log (1 + B * Real.exp (-C)) ≤ D := by
    simpa only [ht, hz] using h (a C)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B
  have he' := he.const_add 1
  simp only [mul_zero, add_zero] at he'
  have hl := (Real.continuousAt_log one_ne_zero).tendsto.comp he'
  have hf := hl.const_sub (classicalKLDiv p q)
  simp only [Real.log_one, sub_zero] at hf
  exact le_of_tendsto' hf hb

end Math.ClassicalEntropy

