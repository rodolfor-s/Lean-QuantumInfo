import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import QCryptLean.Math.Analysis.ExpRemainder
import QCryptLean.Math.SpectralTheory.ArakiLiebThirring

/-! # Lie-Trotter products and the Golden-Thompson trace inequality -/
open scoped Matrix ComplexOrder
noncomputable section
namespace Matrix
/-- Non-commutative telescoping: X^m - Y^m = Σ_{j<m} X^j * (X - Y) * Y^{m-1-j}. -/
lemma noncomm_telescope {R : Type*} [Ring R] (X Y : R) (m : ℕ) :
    X ^ m - Y ^ m =
      ∑ j ∈ Finset.range m, X ^ j * (X - Y) * Y ^ (m - 1 - j) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ X n, pow_succ Y n]
    have key : X ^ n * X - Y ^ n * Y =
        X ^ n * (X - Y) + (X ^ n - Y ^ n) * Y := by simp [mul_sub, sub_mul]
    rw [key, ih, Finset.sum_mul]
    rw [Finset.sum_range_succ]
    rw [add_comm (X ^ n * (X - Y))]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [mul_assoc, ← pow_succ Y]
      congr 1
      congr 1
      omega
    · have : n + 1 - 1 - n = 0 := by omega
      rw [this, pow_zero, mul_one]

/-- The Pi topology on matrices equals the topology from the L∞ operator norm.
    This is the key fact enabling metric arguments for matrix convergence. -/
lemma matrix_nhds_eq_linftyOp_nhds {ι : Type*} [Fintype ι] :
    @instTopologicalSpaceMatrix ι ι ℂ _ =
    @UniformSpace.toTopologicalSpace (Matrix ι ι ℂ)
      (@PseudoMetricSpace.toUniformSpace _
        Matrix.linftyOpSeminormedAddCommGroup.toPseudoMetricSpace) := by rfl

/-- The matrix exponential satisfies `‖exp(X)‖ ≤ exp(‖X‖)` in the `L∞` operator norm. -/
lemma norm_exp_le_exp_norm_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    open scoped Matrix.Norms.Operator in
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℂ)
  let := Matrix.linftyOpNormedAlgebra (n := ι) (R := ℂ) (α := ℂ)
  rcases isEmpty_or_nonempty ι with he | hn
  · have hX : X = 0 := Subsingleton.elim X 0
    simp [hX, Subsingleton.elim (1 : Matrix ι ι ℂ) 0]
  · have : NormOneClass (Matrix ι ι ℂ) := Matrix.linfty_opNormOneClass
    have hexp := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) X
    have hns := NormedSpace.norm_expSeries_summable (𝕂 := ℂ) X
    have h1 : ‖NormedSpace.exp X‖ ≤ ∑' n, ‖(NormedSpace.expSeries ℂ _ n) (fun _ => X)‖ :=
      hexp.tsum_eq ▸ norm_tsum_le_tsum_norm hns
    have h_norm_hasSum : HasSum (fun n => ‖(NormedSpace.expSeries ℂ _ n) (fun _ => X)‖)
        (∑' n, ‖(NormedSpace.expSeries ℂ _ n) (fun _ => X)‖) := hns.hasSum
    have hR := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖
    rw [show Real.exp ‖X‖ = NormedSpace.exp ‖X‖ from congrFun Real.exp_eq_exp_ℝ ‖X‖]
    apply le_trans h1
    apply hasSum_le _ h_norm_hasSum hR
    intro n
    rw [NormedSpace.expSeries_apply_eq, norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le X n) (by positivity)

/-- Helper: ‖X^j * D * Y^k‖ ≤ a^j * ‖D‖ * b^k when ‖X‖ ≤ a, ‖Y‖ ≤ b. -/
lemma norm_pow_mul_pow_bound {α : Type*} [NormedRing α] [NormOneClass α]
    (X Y D : α) (j k : ℕ) (a b : ℝ) (ha : ‖X‖ ≤ a) (hb : ‖Y‖ ≤ b) :
    ‖X ^ j * D * Y ^ k‖ ≤ a ^ j * ‖D‖ * b ^ k := by
  have ha' : 0 ≤ a := le_trans (norm_nonneg _) ha
  have hb' : 0 ≤ b := le_trans (norm_nonneg _) hb
  have h1 : ‖X ^ j‖ ≤ a ^ j :=
    (norm_pow_le X j).trans (pow_le_pow_left₀ (norm_nonneg _) ha j)
  have h2 : ‖Y ^ k‖ ≤ b ^ k :=
    (norm_pow_le Y k).trans (pow_le_pow_left₀ (norm_nonneg _) hb k)
  calc ‖X ^ j * D * Y ^ k‖
      ≤ ‖X ^ j‖ * ‖D‖ * ‖Y ^ k‖ := by
        apply le_trans (norm_mul_le _ _)
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ a ^ j * ‖D‖ * b ^ k := by
        have := mul_le_mul (mul_le_mul h1 (le_refl ‖D‖) (norm_nonneg _) (pow_nonneg ha' _)) h2
            (norm_nonneg _) (mul_nonneg (pow_nonneg ha' _) (norm_nonneg _))
        linarith

/-- Helper: a^j * b^(m-1-j) ≤ max(a,b)^(m-1) for j < m, a,b ≥ 0. -/
lemma pow_mul_pow_le_max_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) (j : ℕ)
    (hj : j < m) :
    a ^ j * b ^ (m - 1 - j) ≤ max a b ^ (m - 1) := by
  have h_sum : j + (m - 1 - j) = m - 1 := by omega
  calc a ^ j * b ^ (m - 1 - j)
      ≤ max a b ^ j * max a b ^ (m - 1 - j) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ ha (le_max_left a b) j
        · exact pow_le_pow_left₀ hb (le_max_right a b) (m - 1 - j)
        · exact pow_nonneg hb _
        · exact pow_nonneg (le_max_of_le_left ha) _
    _ = max a b ^ (m - 1) := by rw [← pow_add, h_sum]

/-- exp(c/m)^{m-1} ≤ exp(c) for c ≥ 0 and m > 0. -/
lemma exp_div_pow_le (c : ℝ) (hc : 0 ≤ c) (m : ℕ) (hm : 0 < m) :
    Real.exp (c / m) ^ (m - 1) ≤ Real.exp c := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h_pow : Real.exp (c / m) ^ (m - 1) =
      Real.exp (↑(m - 1) * (c / m)) := by
    induction (m - 1) with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← Real.exp_add]; congr 1; push_cast; ring
  rw [h_pow, Real.exp_le_exp]
  calc ↑(m - 1) * (c / ↑m)
      ≤ ↑m * (c / ↑m) := by
        apply mul_le_mul_of_nonneg_right
        · exact Nat.cast_le.mpr (Nat.sub_le m 1)
        · exact div_nonneg hc hm_pos.le
    _ = c := by field_simp

/-- Helper: exp((A+B)/m)^m = exp(A+B) -/
lemma exp_inv_smul_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (A : Matrix ι ι ℂ) :
    NormedSpace.exp (((n + 1 : ℕ) : ℂ)⁻¹ • A) ^ (n + 1) = NormedSpace.exp A := by
  rw [← Matrix.exp_nsmul (n + 1)]
  congr 1
  have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← smul_assoc, nsmul_eq_mul, mul_inv_cancel₀ h, one_smul]

/-- For `t ≥ 0`, the exponential remainder satisfies `exp(t) - 1 - t ≤ t² * exp(t)`. -/
lemma real_exp_sub_one_sub_le_sq_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t - 1 - t ≤ t ^ 2 * Real.exp t := by
  by_cases h1 : t ≤ 1
  · have hab : |t| ≤ 1 := abs_le.mpr ⟨by linarith, h1⟩
    have h := Real.abs_exp_sub_one_sub_id_le hab
    have h2 : Real.exp t - 1 - t ≤ |Real.exp t - 1 - t| := le_abs_self _
    have h3 : t ^ 2 ≤ t ^ 2 * Real.exp t :=
      le_mul_of_one_le_right (sq_nonneg t) (Real.one_le_exp ht)
    linarith
  · push Not at h1
    have h2 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    have h3 : 1 ≤ t ^ 2 := by nlinarith
    have hexp := Real.exp_pos t
    nlinarith

section LieTrotterEstimates

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The matrix exponential remainder bound: `‖exp(Z) - 1 - Z‖ ≤ exp(‖Z‖) - 1 - ‖Z‖`. -/
lemma norm_exp_sub_one_sub_le
    (Z : Matrix ι ι ℂ) :
    ‖NormedSpace.exp Z - 1 - Z‖ ≤ Real.exp ‖Z‖ - 1 - ‖Z‖ := by
  rcases isEmpty_or_nonempty ι with he | hn
  · have hZ : Z = 0 := Subsingleton.elim Z 0
    simp [hZ]
  · have : NormOneClass (Matrix ι ι ℂ) := Matrix.linfty_opNormOneClass
    -- the exponential series of `Z` (resp. of `‖Z‖`) with its first two terms `1 + Z` removed
    have htailZ :
        HasSum (fun n : ℕ => (NormedSpace.expSeries ℂ _ (n + 2)) (fun _ => Z))
          (NormedSpace.exp Z - 1 - Z) := by
      have h := (hasSum_nat_add_iff' (f := fun n : ℕ =>
          (NormedSpace.expSeries ℂ (Matrix ι ι ℂ) n) (fun _ => Z)) 2).mpr
        (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) Z)
      have hinitZ :
          ∑ i ∈ Finset.range 2, (NormedSpace.expSeries ℂ _ i) (fun _ => Z) = 1 + Z := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        simp [NormedSpace.expSeries_apply_eq]
      rwa [hinitZ, ← sub_sub] at h
    have htailR :
        HasSum (fun n : ℕ => (NormedSpace.expSeries ℝ _ (n + 2)) (fun _ => ‖Z‖))
          (NormedSpace.exp ‖Z‖ - 1 - ‖Z‖) := by
      have h := (hasSum_nat_add_iff' (f := fun n : ℕ =>
          (NormedSpace.expSeries ℝ ℝ n) (fun _ => ‖Z‖)) 2).mpr
        (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ‖Z‖)
      have hinitR :
          ∑ i ∈ Finset.range 2, (NormedSpace.expSeries ℝ _ i) (fun _ => ‖Z‖) = 1 + ‖Z‖ := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]
        simp
      rwa [hinitR, ← sub_sub] at h
    calc
      ‖NormedSpace.exp Z - 1 - Z‖ =
          ‖∑' n : ℕ, (NormedSpace.expSeries ℂ _ (n + 2)) (fun _ => Z)‖ := by
        rw [htailZ.tsum_eq]
      _ ≤ ∑' n : ℕ, ‖(NormedSpace.expSeries ℂ _ (n + 2)) (fun _ => Z)‖ := by
          exact norm_tsum_le_tsum_norm htailZ.summable.norm
      _ ≤ ∑' n : ℕ, (NormedSpace.expSeries ℝ _ (n + 2)) (fun _ => ‖Z‖) := by
          refine Summable.tsum_le_tsum (fun n => ?_) htailZ.summable.norm htailR.summable
          rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, norm_smul,
            norm_inv, Complex.norm_natCast, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (norm_pow_le Z (n + 2)) (by positivity)
      _ = NormedSpace.exp ‖Z‖ - 1 - ‖Z‖ := by rw [← htailR.tsum_eq]
      _ = Real.exp ‖Z‖ - 1 - ‖Z‖ := by rw [← congrFun Real.exp_eq_exp_ℝ ‖Z‖]

/-- Baker-Campbell-Hausdorff error bound:
    `‖exp(X) · exp(Y) - exp(X+Y)‖ ≤ 2(‖X‖+‖Y‖)² exp(‖X‖+‖Y‖)`. -/
lemma norm_exp_mul_exp_sub_exp_add_le
    (X Y : Matrix ι ι ℂ) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - NormedSpace.exp (X + Y)‖ ≤
    2 * (‖X‖ + ‖Y‖) ^ 2 * Real.exp (‖X‖ + ‖Y‖) := by
  set nSum := ‖X‖ + ‖Y‖
  rcases isEmpty_or_nonempty ι with he | hn
  · have hX : X = 0 := Subsingleton.elim X 0
    have hY : Y = 0 := Subsingleton.elim Y 0
    simp only [hX, hY, add_zero, NormedSpace.exp_zero, one_mul, sub_self, norm_zero]
    positivity
  · have : NormOneClass (Matrix ι ι ℂ) := Matrix.linfty_opNormOneClass
    have decomp : NormedSpace.exp X * NormedSpace.exp Y - NormedSpace.exp (X + Y) =
        (NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) +
        (NormedSpace.exp X - 1 - X) + (NormedSpace.exp Y - 1 - Y) -
        (NormedSpace.exp (X + Y) - 1 - (X + Y)) := by
      have h1 : (NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) =
          NormedSpace.exp X * NormedSpace.exp Y - NormedSpace.exp X - NormedSpace.exp Y + 1 := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
        abel
      rw [h1]
      abel
    rw [decomp]
    have term2 : ‖NormedSpace.exp X - 1 - X‖ ≤ Real.exp ‖X‖ - 1 - ‖X‖ := norm_exp_sub_one_sub_le X
    have term3 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ Real.exp ‖Y‖ - 1 - ‖Y‖ := norm_exp_sub_one_sub_le Y
    have term4 : ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ ≤ Real.exp ‖X + Y‖ - 1 - ‖X + Y‖ :=
      norm_exp_sub_one_sub_le (X + Y)
    have aux1 : Real.exp ‖X‖ - 1 - ‖X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ :=
      real_exp_sub_one_sub_le_sq_mul_exp (norm_nonneg X)
    have aux2 : Real.exp ‖Y‖ - 1 - ‖Y‖ ≤ ‖Y‖ ^ 2 * Real.exp ‖Y‖ :=
      real_exp_sub_one_sub_le_sq_mul_exp (norm_nonneg Y)
    have aux3 : Real.exp ‖X + Y‖ - 1 - ‖X + Y‖ ≤ ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ :=
      real_exp_sub_one_sub_le_sq_mul_exp (norm_nonneg (X + Y))
    have hXY : ‖X + Y‖ ≤ nSum := norm_add_le X Y
    have exp_sub_one_bound :
        ∀ Z : Matrix ι ι ℂ,
        ‖NormedSpace.exp Z - 1‖ ≤ Real.exp ‖Z‖ - 1 := by
      intro Z
      have h := norm_exp_sub_one_sub_le Z
      calc ‖NormedSpace.exp Z - 1‖
          = ‖(NormedSpace.exp Z - 1 - Z) + Z‖ := by congr 1; abel
        _ ≤ ‖NormedSpace.exp Z - 1 - Z‖ + ‖Z‖ := norm_add_le _ _
        _ ≤ (Real.exp ‖Z‖ - 1 - ‖Z‖) + ‖Z‖ := by linarith
        _ = Real.exp ‖Z‖ - 1 := by ring
    have hexp_sub : ∀ t : ℝ, 0 ≤ t → Real.exp t - 1 ≤ t * Real.exp t :=
      fun _ ht => Real.exp_sub_one_le_mul_exp ht
    have term1 : ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1)‖ ≤
        ‖X‖ * ‖Y‖ * Real.exp nSum := by
      calc ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1)‖
          ≤ ‖NormedSpace.exp X - 1‖ * ‖NormedSpace.exp Y - 1‖ := norm_mul_le _ _
        _ ≤ (Real.exp ‖X‖ - 1) * (Real.exp ‖Y‖ - 1) := by
            apply mul_le_mul (exp_sub_one_bound X) (exp_sub_one_bound Y)
              (norm_nonneg _)
            linarith [Real.one_le_exp (norm_nonneg X)]
        _ ≤ (‖X‖ * Real.exp ‖X‖) * (‖Y‖ * Real.exp ‖Y‖) := by
            apply mul_le_mul (hexp_sub ‖X‖ (norm_nonneg X)) (hexp_sub ‖Y‖ (norm_nonneg Y))
              (by linarith [Real.one_le_exp (norm_nonneg Y)])
              (mul_nonneg (norm_nonneg X) (Real.exp_pos _).le)
        _ = ‖X‖ * ‖Y‖ * (Real.exp ‖X‖ * Real.exp ‖Y‖) := by ring
        _ = ‖X‖ * ‖Y‖ * Real.exp (‖X‖ + ‖Y‖) := by rw [← Real.exp_add]
        _ = ‖X‖ * ‖Y‖ * Real.exp nSum := rfl
    have h_tri : ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) +
          (NormedSpace.exp X - 1 - X) + (NormedSpace.exp Y - 1 - Y) -
          (NormedSpace.exp (X + Y) - 1 - (X + Y))‖ ≤
        ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1)‖ +
          ‖NormedSpace.exp X - 1 - X‖ + ‖NormedSpace.exp Y - 1 - Y‖ +
          ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ := by
      have tri1 := norm_sub_le ((NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) +
          (NormedSpace.exp X - 1 - X) + (NormedSpace.exp Y - 1 - Y))
          (NormedSpace.exp (X + Y) - 1 - (X + Y))
      have tri2 := norm_add_le ((NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) +
          (NormedSpace.exp X - 1 - X)) (NormedSpace.exp Y - 1 - Y)
      have tri3 := norm_add_le ((NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1))
          (NormedSpace.exp X - 1 - X)
      linarith
    calc ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1) +
          (NormedSpace.exp X - 1 - X) + (NormedSpace.exp Y - 1 - Y) -
          (NormedSpace.exp (X + Y) - 1 - (X + Y))‖
        ≤ ‖(NormedSpace.exp X - 1) * (NormedSpace.exp Y - 1)‖ +
          ‖NormedSpace.exp X - 1 - X‖ + ‖NormedSpace.exp Y - 1 - Y‖ +
          ‖NormedSpace.exp (X + Y) - 1 - (X + Y)‖ := h_tri
      _ ≤ ‖X‖ * ‖Y‖ * Real.exp nSum +
          ‖X‖ ^ 2 * Real.exp ‖X‖ + ‖Y‖ ^ 2 * Real.exp ‖Y‖ +
          ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ := by
          linarith [term1, term2.trans aux1,
            term3.trans aux2, term4.trans aux3]
      _ ≤ ‖X‖ * ‖Y‖ * Real.exp nSum +
          ‖X‖ ^ 2 * Real.exp nSum + ‖Y‖ ^ 2 * Real.exp nSum +
          nSum ^ 2 * Real.exp nSum := by
          -- each norm is at most `nSum`, and `exp` is monotone
          have hE : ∀ {a : ℝ}, a ≤ nSum → Real.exp a ≤ Real.exp nSum := Real.exp_le_exp.mpr
          have t2 : ‖X‖ ^ 2 * Real.exp ‖X‖ ≤ ‖X‖ ^ 2 * Real.exp nSum :=
            mul_le_mul_of_nonneg_left (hE (le_add_of_nonneg_right (norm_nonneg Y))) (sq_nonneg _)
          have t3 : ‖Y‖ ^ 2 * Real.exp ‖Y‖ ≤ ‖Y‖ ^ 2 * Real.exp nSum :=
            mul_le_mul_of_nonneg_left (hE (le_add_of_nonneg_left (norm_nonneg X))) (sq_nonneg _)
          have t4 : ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ ≤ nSum ^ 2 * Real.exp nSum :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hXY 2) (hE hXY) (Real.exp_pos _).le
              (sq_nonneg _)
          linarith
      _ = (‖X‖ * ‖Y‖ + ‖X‖ ^ 2 + ‖Y‖ ^ 2 + nSum ^ 2) * Real.exp nSum := by ring
      _ ≤ 2 * nSum ^ 2 * Real.exp nSum := by
          -- `‖X‖‖Y‖ + ‖X‖² + ‖Y‖² ≤ (‖X‖ + ‖Y‖)²`, since `‖X‖‖Y‖ ≥ 0`
          have hexp : nSum ^ 2 = ‖X‖ ^ 2 + 2 * (‖X‖ * ‖Y‖) + ‖Y‖ ^ 2 := by
            simp only [nSum]; ring
          have hXY0 : 0 ≤ ‖X‖ * ‖Y‖ := mul_nonneg (norm_nonneg X) (norm_nonneg Y)
          have h : ‖X‖ * ‖Y‖ + ‖X‖ ^ 2 + ‖Y‖ ^ 2 + nSum ^ 2 ≤ 2 * nSum ^ 2 := by linarith
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos nSum).le

/-- The Trotter product `exp(m⁻¹A) · exp(m⁻¹B)`.

    For `m = 0`, this uses Lean's totalized convention `((0 : ℂ)⁻¹) = 0`, so
    `trotterStep A B 0 = 1`. All asymptotic statements below use positive steps. -/
noncomputable def trotterStep (A B : Matrix ι ι ℂ) (m : ℕ) :
    Matrix ι ι ℂ :=
  NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • A) *
    NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • B)

/-- The single-step Trotter error `exp(m⁻¹A)·exp(m⁻¹B) - exp(m⁻¹(A+B))`.

    For `m = 0`, this follows the same totalized convention as `trotterStep`,
    so `trotterError A B 0 = 0`. -/
noncomputable def trotterError (A B : Matrix ι ι ℂ) (m : ℕ) :
    Matrix ι ι ℂ :=
  trotterStep A B m - NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • (A + B))

lemma trotterError_eq (A B : Matrix ι ι ℂ) (m : ℕ) :
    trotterError A B m =
    NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • A) *
      NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • B) -
    NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • (A + B)) := rfl

private lemma trotterError_norm_le (A B : Matrix ι ι ℂ) (m : ℕ) :
    ‖trotterError A B m‖ ≤
    2 * (‖A‖ / ((m : ℕ) : ℝ) + ‖B‖ / ((m : ℕ) : ℝ)) ^ 2 *
    Real.exp (‖A‖ / ((m : ℕ) : ℝ) + ‖B‖ / ((m : ℕ) : ℝ)) := by
  have h := norm_exp_mul_exp_sub_exp_add_le
    ((((m : ℕ) : ℂ)⁻¹) • A) ((((m : ℕ) : ℂ)⁻¹) • B)
  rw [← smul_add] at h
  simp only [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div] at h
  exact h

/-- The single-step Trotter error decays as O(1/m²): `‖trotterError A B m‖ ≤ K / m²`. -/
lemma lie_trotter_error_bound
    (A B : Matrix ι ι ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ+,
    ‖trotterError A B m‖ ≤ K / ((m : ℕ) : ℝ) ^ 2 := by
  refine ⟨2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖), by positivity, fun m => ?_⟩
  have hm_pos : (0 : ℝ) < ((m : ℕ) : ℝ) := Nat.cast_pos.mpr m.pos
  have h1 := trotterError_norm_le A B m
  calc ‖trotterError A B m‖
      ≤ 2 * (‖A‖ / (((m : ℕ) : ℝ)) + ‖B‖ / (((m : ℕ) : ℝ))) ^ 2 *
        Real.exp (‖A‖ / (((m : ℕ) : ℝ)) + ‖B‖ / (((m : ℕ) : ℝ))) := h1
    _ = 2 * ((‖A‖ + ‖B‖) / (((m : ℕ) : ℝ))) ^ 2 *
        Real.exp ((‖A‖ + ‖B‖) / (((m : ℕ) : ℝ))) := by ring_nf
    _ ≤ 2 * ((‖A‖ + ‖B‖) / (((m : ℕ) : ℝ))) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr
          (div_le_self (by positivity) (Nat.one_le_cast.mpr m.pos))
    _ = 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) / (((m : ℕ) : ℝ)) ^ 2 := by
        field_simp

/-- The Trotter product converges to `exp(A+B)` with rate O(1/n):
    `‖(exp(A/(n+1))·exp(B/(n+1)))^(n+1) - exp(A+B)‖ ≤ C/(n+1)`. -/
lemma lie_trotter_norm_estimate
    (A B : Matrix ι ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    ‖trotterStep A B (n + 1) ^ (n + 1) - NormedSpace.exp (A + B)‖ ≤
    C / ((n : ℝ) + 1) := by
  rcases isEmpty_or_nonempty ι with he | hn
  · refine ⟨0, le_refl _, fun n => ?_⟩
    simp only [zero_div]
    suffices h : trotterStep A B (n + 1) ^ (n + 1) -
        NormedSpace.exp (A + B) = 0 from h ▸ norm_zero.le
    ext i
    exact isEmptyElim i
  · have : NormOneClass (Matrix ι ι ℂ) := Matrix.linfty_opNormOneClass
    obtain ⟨K, hK_nn, hK_bound⟩ := lie_trotter_error_bound A B
    set nA := ‖A‖ with nA_def
    set nB := ‖B‖ with nB_def
    set nAB := ‖A + B‖ with nAB_def
    set M := Real.exp (max (nA + nB) nAB) with M_def
    refine ⟨K * M, mul_nonneg hK_nn (Real.exp_pos _).le, fun n => ?_⟩
    set m : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩ with m_def
    set Xm := trotterStep A B m
    set Ym := NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • (A + B))
    have hYm_pow : Ym ^ (m : ℕ) = NormedSpace.exp (A + B) := exp_inv_smul_pow n (A + B)
    rw [show (n : ℝ) + 1 = ((m : ℕ) : ℝ) from by simp [m_def]]
    rw [show n + 1 = (m : ℕ) by simp [m_def]]
    rw [← hYm_pow]
    have h_Xm_Ym : Xm - Ym = trotterError A B m := rfl
    rw [noncomm_telescope Xm Ym (m : ℕ)]
    have h_err : ‖Xm - Ym‖ ≤ K / (((m : ℕ) : ℝ)) ^ 2 := by
      rw [h_Xm_Ym]
      exact hK_bound m
    have hXm_norm : ‖Xm‖ ≤ Real.exp ((nA + nB) / ((m : ℕ) : ℝ)) := by
      simp only [Xm, trotterStep]
      calc ‖NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • A) *
            NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • B)‖
          ≤ ‖NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • A)‖ *
              ‖NormedSpace.exp ((((m : ℕ) : ℂ)⁻¹) • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖((((m : ℕ) : ℂ)⁻¹) • A)‖ *
            Real.exp ‖((((m : ℕ) : ℂ)⁻¹) • B)‖ := by
            apply mul_le_mul (norm_exp_le_exp_norm_matrix _) (norm_exp_le_exp_norm_matrix _)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (‖((((m : ℕ) : ℂ)⁻¹) • A)‖ + ‖((((m : ℕ) : ℂ)⁻¹) • B)‖) :=
            (Real.exp_add _ _).symm
        _ ≤ Real.exp ((nA + nB) / (((m : ℕ) : ℝ))) := by
            apply Real.exp_le_exp.mpr
            rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast]
            simp only [nA_def, nB_def, div_eq_mul_inv]
            ring_nf
            rfl
    have hYm_norm : ‖Ym‖ ≤ Real.exp (nAB / (((m : ℕ) : ℝ))) :=
      (norm_exp_le_exp_norm_matrix _).trans (by
        apply Real.exp_le_exp.mpr
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        simp only [nAB_def, div_eq_mul_inv]
        ring_nf
        rfl)
    calc ‖∑ j ∈ Finset.range (m : ℕ), Xm ^ j * (Xm - Ym) * Ym ^ ((m : ℕ) - 1 - j)‖
        ≤ ∑ j ∈ Finset.range (m : ℕ), ‖Xm ^ j * (Xm - Ym) * Ym ^ ((m : ℕ) - 1 - j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (m : ℕ),
            (Real.exp ((nA + nB) / (((m : ℕ) : ℝ)))) ^ j * ‖Xm - Ym‖ *
            (Real.exp (nAB / (((m : ℕ) : ℝ)))) ^ ((m : ℕ) - 1 - j) := by
          apply Finset.sum_le_sum
          intro j _
          exact norm_pow_mul_pow_bound Xm Ym (Xm - Ym) j (((m : ℕ) - 1 - j))
            (Real.exp ((nA + nB) / (((m : ℕ) : ℝ))))
            (Real.exp (nAB / (((m : ℕ) : ℝ)))) hXm_norm hYm_norm
      _ ≤ ∑ j ∈ Finset.range (m : ℕ), M * (K / (((m : ℕ) : ℝ)) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_range.mp hj
          have h_geom : (Real.exp ((nA + nB) / (((m : ℕ) : ℝ)))) ^ j *
              (Real.exp (nAB / (((m : ℕ) : ℝ)))) ^ ((m : ℕ) - 1 - j) ≤ M := by
            calc (Real.exp ((nA + nB) / (((m : ℕ) : ℝ)))) ^ j *
                (Real.exp (nAB / (((m : ℕ) : ℝ)))) ^ ((m : ℕ) - 1 - j)
                ≤ (max (Real.exp ((nA + nB) / (((m : ℕ) : ℝ))))
                    (Real.exp (nAB / (((m : ℕ) : ℝ))))) ^ ((m : ℕ) - 1) :=
                  pow_mul_pow_le_max_pow _ _ (Real.exp_pos _).le (Real.exp_pos _).le
                    (m : ℕ) j hj'
              _ ≤ Real.exp (max (nA + nB) nAB / (((m : ℕ) : ℝ))) ^ ((m : ℕ) - 1) := by
                  apply pow_le_pow_left₀ (le_max_of_le_left (Real.exp_pos _).le)
                  apply max_le
                  · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
                      (le_max_left _ _) (Nat.cast_nonneg _))
                  · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
                      (le_max_right _ _) (Nat.cast_nonneg _))
              _ ≤ Real.exp (max (nA + nB) nAB) := by
                  apply exp_div_pow_le
                  · exact le_max_of_le_left (add_nonneg (norm_nonneg A) (norm_nonneg B))
                  · omega
          calc (Real.exp ((nA + nB) / (((m : ℕ) : ℝ)))) ^ j * ‖Xm - Ym‖ *
                (Real.exp (nAB / (((m : ℕ) : ℝ)))) ^ ((m : ℕ) - 1 - j)
              = (Real.exp ((nA + nB) / (((m : ℕ) : ℝ)))) ^ j *
                (Real.exp (nAB / (((m : ℕ) : ℝ)))) ^ ((m : ℕ) - 1 - j) * ‖Xm - Ym‖ := by
                  ring
            _ ≤ M * (K / (((m : ℕ) : ℝ)) ^ 2) := by
                apply mul_le_mul h_geom h_err (norm_nonneg _) (Real.exp_pos _).le
      _ = (((m : ℕ) : ℝ)) * (M * (K / (((m : ℕ) : ℝ)) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = K * M / (((m : ℕ) : ℝ)) := by
          have hm_pos : (0 : ℝ) < (((m : ℕ) : ℝ)) := by
            exact Nat.cast_pos.mpr m.pos
          field_simp

end LieTrotterEstimates

/-- Lie-Trotter product formula for matrices:
    (exp(A/(n+1)) * exp(B/(n+1)))^(n+1) → exp(A+B) as n → ∞.
    Reference: Trotter (1959), Hall, Lie Groups ch. 2. -/
lemma lie_trotter_product_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    Filter.Tendsto
      (fun n : ℕ => (NormedSpace.exp (((n + 1 : ℕ) : ℂ)⁻¹ • A) *
                      NormedSpace.exp (((n + 1 : ℕ) : ℂ)⁻¹ • B)) ^ (n + 1))
      Filter.atTop (nhds (NormedSpace.exp (A + B))) := by
  have htop := @matrix_nhds_eq_linftyOp_nhds ι _
  rw [htop] at *
  open scoped Matrix.Norms.Operator in
  apply NormedAddCommGroup.tendsto_atTop.mpr
  open scoped Matrix.Norms.Operator in
  intro ε hε
  open scoped Matrix.Norms.Operator in
  obtain ⟨C, hC_nn, hC_bound⟩ := lie_trotter_norm_estimate A B
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C / ε)
  refine ⟨N₀, fun n hn => ?_⟩
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc ‖(NormedSpace.exp (((n + 1 : ℕ) : ℂ)⁻¹ • A) *
          NormedSpace.exp (((n + 1 : ℕ) : ℂ)⁻¹ • B)) ^ (n + 1) -
        NormedSpace.exp (A + B)‖
      ≤ C / ((n : ℝ) + 1) := hC_bound n
    _ < ε := by
        rw [div_lt_iff₀ hn1_pos]
        have hN₀_le : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        nlinarith [div_mul_cancel₀ C (ne_of_gt hε)]

/-- Scaling identity: (n+1) • ((↑(n+1))⁻¹ • A) = A for matrices. -/
lemma nsmul_inv_smul_matrix {ι : Type*} (n : ℕ)
    (A : Matrix ι ι ℂ) :
    (n + 1) • (((n + 1 : ℕ) : ℂ)⁻¹ • A) = A := by
  have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← smul_assoc, nsmul_eq_mul, mul_inv_cancel₀ h, one_smul]

/-- Powers of two give a cofinal subsequence of `ℕ` after shifting by `-1`. -/
private lemma tendsto_pow_two_sub_one_atTop :
    Filter.Tendsto (fun k : ℕ => 2 ^ k - 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro n
  have hpow : Filter.Tendsto (fun k : ℕ => 2 ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
  have hpow' : ∀ᶠ k : ℕ in Filter.atTop, n + 1 ≤ 2 ^ k :=
    (Filter.tendsto_atTop.1 hpow) (n + 1)
  filter_upwards [hpow'] with k hk
  omega

/-- The dyadic Trotter subsequence still converges to `exp(A + B)`. -/
private lemma dyadic_lie_trotter_product_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    Filter.Tendsto
      (fun k : ℕ =>
        (NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • A) *
          NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • B)) ^ (2 ^ k))
      Filter.atTop (nhds (NormedSpace.exp (A + B))) := by
  have htend := lie_trotter_product_formula A B
  have hsub := htend.comp tendsto_pow_two_sub_one_atTop
  convert hsub using 1
  ext k
  have hk : 1 ≤ 2 ^ k := by
    exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) k)
  simp [Nat.sub_add_cancel hk]

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Dyadic specialization of the finite-step Lieb-Thirring inequality.

This is strictly narrower than the all-`n` finite-step statement and is enough
for the Golden-Thompson proof because the dyadic Trotter subsequence still
converges to `exp (A + B)`. -/
private lemma dyadic_trotter_step_lieb_thirring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) :
    ((NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • A) *
      NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • B)) ^ (2 ^ k)).trace.re ≤
    (NormedSpace.exp A * NormedSpace.exp B).trace.re := by
  have hk_pos : 0 < 2 ^ k := pow_pos (by decide : 0 < (2 : ℕ)) k
  have hk_one : 1 ≤ 2 ^ k := Nat.succ_le_of_lt hk_pos
  have hA_scaled : ((((2 ^ k : ℕ) : ℂ)⁻¹) • A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA]
    simp
  have hB_scaled : ((((2 ^ k : ℕ) : ℂ)⁻¹) • B).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hB]
    simp
  have hlt := Math.SpectralTheory.re_trace_mul_pow_le_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp hA_scaled.isSelfAdjoint.exp_nonneg)
    (Matrix.nonneg_iff_posSemidef.mp hB_scaled.isSelfAdjoint.exp_nonneg) (2 ^ k)
  have hA_pow :
      NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • A) ^ (2 ^ k) = NormedSpace.exp A := by
    simpa [Nat.sub_add_cancel hk_one] using exp_inv_smul_pow (2 ^ k - 1) A
  have hB_pow :
      NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • B) ^ (2 ^ k) = NormedSpace.exp B := by
    simpa [Nat.sub_add_cancel hk_one] using exp_inv_smul_pow (2 ^ k - 1) B
  rw [hA_pow, hB_pow] at hlt
  exact hlt

/-- Golden-Thompson trace inequality: for Hermitian `A` and `B`,
`Tr(exp(A + B)) ≤ Tr(exp(A) * exp(B))`. -/
lemma golden_thompson_trace_ineq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace.re ≤
    (NormedSpace.exp A * NormedSpace.exp B).trace.re := by
  have key : ∀ k : ℕ,
      ((NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • A) *
        NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • B)) ^ (2 ^ k)).trace.re ≤
      (NormedSpace.exp A * NormedSpace.exp B).trace.re :=
    fun k => dyadic_trotter_step_lieb_thirring A B hA hB k
  have htend := dyadic_lie_trotter_product_formula A B
  have htrace_cont : Continuous (fun M : Matrix ι ι ℂ => M.trace.re) := by
    apply Complex.continuous_re.comp
    exact continuous_finsetSum _ (fun i _ => continuous_apply_apply i i)
  have htrace_tend : Filter.Tendsto
      (fun k => ((NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • A) *
                  NormedSpace.exp (((2 ^ k : ℕ) : ℂ)⁻¹ • B)) ^ (2 ^ k)).trace.re)
      Filter.atTop (nhds (NormedSpace.exp (A + B)).trace.re) :=
    (htrace_cont.tendsto _).comp htend
  exact le_of_tendsto' htrace_tend key


end Matrix
