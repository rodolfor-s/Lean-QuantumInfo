import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Classical variance and exponential-moment bounds

Finite probability distributions satisfy variance and continuity bounds controlled by
exponential moments.

## Main declarations

`classical_var_le_log_sqrt_budget` bounds variance by two exponential-moment budgets;
Taylor, Hölder, and logarithmic inequalities supply the scalar estimates.

## References

See the cited results in the declaration docstrings.
-/

open scoped BigOperators

noncomputable section

namespace InfoTheory.Renyi


section ClassicalCore

/-- **C1**, the Taylor bound with an exponential third-order remainder. -/
private lemma exp_le_taylor_three (u : ℝ) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 * Real.exp u := by
  set g : ℝ → ℝ := fun u => (1 + u + u ^ 2 / 2) * Real.exp (-u) + u ^ 3 / 6 - 1 with hgdef
  have hg' : ∀ v : ℝ, HasDerivAt g (v ^ 2 / 2 * (1 - Real.exp (-v))) v := by
    intro v
    have h1 : HasDerivAt (fun u : ℝ => 1 + u + u ^ 2 / 2) (1 + v) v := by
      have hA : HasDerivAt (fun u : ℝ => 1 + u) 1 v := (hasDerivAt_id v).const_add 1
      have hB : HasDerivAt (fun u : ℝ => u ^ 2 / 2) (2 * v ^ 1 / 2) v :=
        (hasDerivAt_pow 2 v).div_const 2
      have := hA.add hB
      apply this.congr_deriv
      ring
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-v)) v := by
      have := (Real.hasDerivAt_exp (-v)).comp v ((hasDerivAt_id v).neg)
      exact this.congr_deriv (by ring)
    have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (3 * v ^ 2 / 6) v :=
      (hasDerivAt_pow 3 v).div_const 6
    have h4 := ((h1.mul h2).add h3).sub_const 1
    apply h4.congr_deriv
    ring
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hdiff : Differentiable ℝ g := fun v => (hg' v).differentiableAt
  have hgnn : ∀ v : ℝ, 0 ≤ g v := by
    intro v
    rcases le_total 0 v with hv | hv
    · have hmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).differentiableWithinAt) fun x hx => ?_
        rw [interior_Ici] at hx
        rw [(hg' x).deriv]
        have hx0 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by simpa using hx.le)
        nlinarith [sq_nonneg x]
      have := hmono (Set.self_mem_Ici) hv hv
      linarith [hg0 ▸ this]
    · have hanti : AntitoneOn g (Set.Iic (0 : ℝ)) := by
        refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).differentiableWithinAt) fun x hx => ?_
        rw [interior_Iic] at hx
        rw [(hg' x).deriv]
        have hx0 : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (by simpa using hx.le)
        nlinarith [sq_nonneg x]
      have := hanti hv (Set.self_mem_Iic) hv
      linarith [hg0 ▸ this]
  have hv := hgnn u
  have hexp : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hmul : 0 ≤ g u * Real.exp u := mul_nonneg hv hexp.le
  have hcancel : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]; simp
  have : g u * Real.exp u
      = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 * Real.exp u - Real.exp u := by
    simp only [hgdef]
    linear_combination (1 + u + u ^ 2 / 2) * hcancel
  linarith [this ▸ hmul]

/-- **C2**. -/
private lemma sq_log_le_sq_log_add (t : ℝ) (ht : 0 < t) :
    (Real.log t) ^ 2 ≤ (Real.log (t + t⁻¹ + 1)) ^ 2 := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have h1 : Real.log t ≤ Real.log (t + t⁻¹ + 1) := Real.log_le_log ht (by linarith)
  have h2 : Real.log t⁻¹ ≤ Real.log (t + t⁻¹ + 1) := Real.log_le_log hti (by linarith)
  rw [Real.log_inv] at h2
  exact sq_le_sq' (by linarith) h1

/-- **C3**. -/
private lemma concaveOn_sq_log :
    ConcaveOn ℝ (Set.Ici (Real.exp 1)) (fun s : ℝ => (Real.log s) ^ 2) := by
  have hderiv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun x : ℝ => (Real.log x) ^ 2) (2 * (Real.log s / s)) s := by
    intro s hs
    have h := (Real.hasDerivAt_log hs.ne').pow 2
    apply h.congr_deriv
    ring
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _) ?_ ?_ ?_
  · exact fun s hs =>
      ((hderiv s (lt_of_lt_of_le (Real.exp_pos 1) hs)).continuousAt).continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact ((hderiv s (lt_trans (Real.exp_pos 1) hs)).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := lt_trans (Real.exp_pos 1) ha
    have hb' : (0 : ℝ) < b := lt_trans (Real.exp_pos 1) hb
    rw [(hderiv a ha').deriv, (hderiv b hb').deriv]
    have h := Real.log_div_self_antitoneOn (Set.mem_ofPred.mpr ha.le)
      (Set.mem_ofPred.mpr hb.le) hab
    simp only at h
    linarith

private lemma sq_log_div_antitoneOn :
    AntitoneOn (fun s : ℝ => (Real.log s) ^ 2 / s) (Set.Ici (Real.exp 2)) := by
  have key : ∀ s : ℝ, 0 < s → (Real.log s) ^ 2 / s = (Real.log s / s ^ (1 / 2 : ℝ)) ^ 2 := by
    intro s hs
    rw [div_pow, ← Real.rpow_natCast (s ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hs.le]
    norm_num
  have hnn : ∀ s : ℝ, Real.exp 2 ≤ s → 0 ≤ Real.log s / s ^ (1 / 2 : ℝ) := by
    intro s hs
    have hs' : (0 : ℝ) < s := lt_of_lt_of_le (Real.exp_pos 2) hs
    have h2 : (2 : ℝ) ≤ Real.log s := (Real.le_log_iff_exp_le hs').mpr hs
    exact div_nonneg (by linarith) (Real.rpow_nonneg hs'.le _)
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := lt_of_lt_of_le (Real.exp_pos 2) ha
  have hb' : (0 : ℝ) < b := lt_of_lt_of_le (Real.exp_pos 2) hb
  change (Real.log b) ^ 2 / b ≤ (Real.log a) ^ 2 / a
  have hanti := Real.log_div_self_rpow_antitoneOn (a := 1 / 2) (by norm_num)
  have hhalf : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
  have hmemA : Real.exp (1 / 2 : ℝ)⁻¹ ≤ a := by rw [hhalf]; exact ha
  have hmemB : Real.exp (1 / 2 : ℝ)⁻¹ ≤ b := by rw [hhalf]; exact hb
  have h : Real.log b / b ^ (1 / 2 : ℝ) ≤ Real.log a / a ^ (1 / 2 : ℝ) := hanti hmemA hmemB hab
  rw [key a ha', key b hb']
  exact pow_le_pow_left₀ (hnn b hb) h 2

/-- **C4**. -/
private lemma concaveOn_cube_log_add :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => (Real.log (t + Real.exp 2)) ^ 3) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < t + Real.exp 2 := by
    intro t ht; have := Real.exp_pos 2; linarith
  have hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun x : ℝ => (Real.log (x + Real.exp 2)) ^ 3)
        (3 * ((Real.log (t + Real.exp 2)) ^ 2 / (t + Real.exp 2))) t := by
    intro t ht
    have h0 : HasDerivAt (fun x : ℝ => x + Real.exp 2) 1 t := (hasDerivAt_id t).add_const _
    have h1 : HasDerivAt (fun x : ℝ => Real.log (x + Real.exp 2)) (1 / (t + Real.exp 2)) t :=
      h0.log (hpos t ht).ne'
    have h2 := h1.pow 3
    apply h2.congr_deriv
    ring
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _) ?_ ?_ ?_
  · exact fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact ((hderiv t ht.le).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    rw [(hderiv a ha.le).deriv, (hderiv b hb.le).deriv]
    have hma : Real.exp 2 ≤ a + Real.exp 2 := by simp only [Set.mem_Ioi] at ha; linarith
    have hmb : Real.exp 2 ≤ b + Real.exp 2 := by simp only [Set.mem_Ioi] at hb; linarith
    have h := sq_log_div_antitoneOn hma hmb (by linarith)
    simp only at h
    linarith

private lemma exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  norm_num at h
  linarith

/-- **The classical variance bound**, valid at every `ν > 0`. -/
private lemma classical_var_le {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ν : ℝ} (hν : 0 < ν) :
    ∑ i, w i * (Y i) ^ 2
      ≤ (1 / ν ^ 2) * (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by
  classical
  have hginv : ∀ i : ι, (Real.exp (ν * Y i))⁻¹ = Real.exp (-ν * Y i) := by
    intro i; rw [← Real.exp_neg]; ring_nf
  have hg3 : ∀ i : ι, (3 : ℝ) ≤ Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1 := by
    intro i
    have h1 : Real.exp (ν * Y i) * Real.exp (-ν * Y i) = 1 := by
      rw [← Real.exp_add, show ν * Y i + -ν * Y i = 0 by ring, Real.exp_zero]
    have h2 : 0 < Real.exp (ν * Y i) := Real.exp_pos _
    nlinarith [sq_nonneg (Real.exp (ν * Y i) - 1)]
  have hpt : ∀ i : ι, (ν * Y i) ^ 2
      ≤ (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2 := by
    intro i
    have h := sq_log_le_sq_log_add (Real.exp (ν * Y i)) (Real.exp_pos _)
    rw [Real.log_exp, hginv i] at h
    exact h
  have hsplit : ∑ i, w i * (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
      = (∑ i, w i * Real.exp (ν * Y i)) + (∑ i, w i * Real.exp (-ν * Y i)) + 1 := by
    have hterm : ∀ i : ι, w i * (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
        = w i * Real.exp (ν * Y i) + w i * Real.exp (-ν * Y i) + w i := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, hw1]
  have hjensen : ∑ i, w i * (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2
      ≤ (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by
    have h := concaveOn_sq_log.le_map_sum (t := (Finset.univ : Finset ι)) (w := w)
      (p := fun i => Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
      (fun i _ => hw i) hw1 (fun i _ => le_trans exp_one_le_three (hg3 i))
    simp only [smul_eq_mul] at h
    rw [hsplit] at h
    exact h
  have hstep : ∑ i, w i * (ν * Y i) ^ 2
      ≤ ∑ i, w i * (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw i)
  have hfac : ∑ i, w i * (ν * Y i) ^ 2 = ν ^ 2 * ∑ i, w i * (Y i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hν2 : (0 : ℝ) < ν ^ 2 := by positivity
  rw [hfac] at hstep
  have hchain := hstep.trans hjensen
  rw [← le_div_iff₀' hν2] at hchain
  calc ∑ i, w i * (Y i) ^ 2
      ≤ (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 / ν ^ 2 := hchain
    _ = (1 / ν ^ 2) * (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by ring

/-- `sinh x < x · cosh x` for `x > 0`: the function `x·cosh x − sinh x` has derivative
`x·sinh x > 0` on `(0, ∞)` and vanishes at `0`. -/
private lemma sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : Real.sinh x < x * Real.cosh x := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
      (y * Real.sinh y) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => z * Real.cosh z)
        (1 * Real.cosh y + y * Real.sinh y) y := (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
    have h2 : HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
        (1 * Real.cosh y + y * Real.sinh y - Real.cosh y) y := h1.sub (Real.hasDerivAt_sinh y)
    simpa using h2
  have hdiff : Differentiable ℝ (fun z : ℝ => z * Real.cosh z - Real.sinh z) :=
    fun y => (hderiv y).differentiableAt
  have hmono : StrictMonoOn (fun z : ℝ => z * Real.cosh z - Real.sinh z) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hdiff.continuous.continuousOn ?_
    rw [interior_Ici]
    intro y hy
    rw [(hderiv y).deriv]
    exact mul_pos (Set.mem_Ioi.mp hy) (Real.sinh_pos_iff.mpr (Set.mem_Ioi.mp hy))
  have hgt := hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx.le) hx
  simp only at hgt
  norm_num at hgt
  linarith

/-- `sinh x / x` is strictly increasing on `(0, ∞)`: its derivative
`(x·cosh x − sinh x)/x²` is positive there, by `sinh_lt_mul_cosh`. -/
private lemma sinh_div_strictMonoOn :
    StrictMonoOn (fun x : ℝ => Real.sinh x / x) (Set.Ioi 0) := by
  have hderiv : ∀ y ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z : ℝ => Real.sinh z / z)
      ((Real.cosh y * y - Real.sinh y) / y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => Real.sinh z) (Real.cosh y) y := Real.hasDerivAt_sinh y
    have h2 : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have h3 := h1.div h2 (ne_of_gt hy)
    simp only [mul_one] at h3
    exact h3
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => Real.sinh z / z) (Set.Ioi 0) :=
    fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hdiff.continuousOn ?_
  rw [interior_Ioi]
  intro y hy
  rw [(hderiv y hy).deriv]
  have hnum : (0 : ℝ) < Real.cosh y * y - Real.sinh y := by linarith [sinh_lt_mul_cosh hy]
  exact div_pos hnum (pow_pos hy 2)

/-- **The tangent majorant.** For `L > 0` and every real `z`,
`z² ≤ L² + (2L/sinh L)·(cosh z − cosh L)`, with equality exactly at `z = ±L`: the even function
`z ↦ L² + (2L/sinh L)(cosh z − cosh L) − z²` is antitone on `[0, L]` and monotone on `[L, ∞)`
because its derivative `k·sinh x − 2x` is negative on `(0, L)` and positive on `(L, ∞)`, which
follows from the strict monotonicity of `sinh x / x`. -/
private lemma sq_le_cosh_tangent (L : ℝ) (hL : 0 < L) (z : ℝ) :
    z ^ 2 ≤ L ^ 2 + (2 * L / Real.sinh L) * (Real.cosh z - Real.cosh L) := by
  classical
  set k : ℝ := 2 * L / Real.sinh L with hk
  have hsinhL : (0 : ℝ) < Real.sinh L := Real.sinh_pos_iff.mpr hL
  have hkpos : (0 : ℝ) < k := by rw [hk]; positivity
  have hkL : k * Real.sinh L = 2 * L := by rw [hk]; field_simp
  set f : ℝ → ℝ := fun x => L ^ 2 + k * (Real.cosh x - Real.cosh L) - x ^ 2 with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (k * Real.sinh x - 2 * x) x := by
    intro x
    have h0 : HasDerivAt (fun z : ℝ => Real.cosh z - Real.cosh L) (Real.sinh x) x := by
      simpa using (Real.hasDerivAt_cosh x).sub_const (Real.cosh L)
    have h1 : HasDerivAt (fun z : ℝ => k * (Real.cosh z - Real.cosh L)) (k * Real.sinh x) x :=
      h0.const_mul k
    have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact (h1.const_add (L ^ 2)).sub h2
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  -- the derivative of `f` is negative on `(0, L)` and positive on `(L, ∞)`
  have hsign : ∀ x ∈ Set.Ioo 0 L, deriv f x < 0 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hmono : Real.sinh x / x < Real.sinh L / L :=
      sinh_div_strictMonoOn (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hL) hx.2
    have hcross : L * Real.sinh x < x * Real.sinh L := by
      rw [mul_comm L (Real.sinh x), mul_comm x (Real.sinh L)]
      exact (div_lt_div_iff₀ hx0 hL).mp hmono
    rw [(hderiv x).deriv]
    have hstep : k * Real.sinh x < 2 * x := by
      rw [show (2 : ℝ) * x = (2 * L * x) / L from by field_simp, lt_div_iff₀ hL]
      calc k * Real.sinh x * L = k * (L * Real.sinh x) := by ring
        _ < k * (x * Real.sinh L) := mul_lt_mul_of_pos_left hcross hkpos
        _ = (2 * L) * x := by rw [← hkL]; ring
        _ = 2 * L * x := by ring
    linarith
  have hsign' : ∀ x ∈ Set.Ioi L, deriv f x > 0 := by
    intro x hx
    have hsx : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr (lt_trans hL hx)
    have hxpos : (0 : ℝ) < x := lt_trans hL hx
    have hmono : Real.sinh L / L < Real.sinh x / x :=
      sinh_div_strictMonoOn (Set.mem_Ioi.mpr hL) (Set.mem_Ioi.mpr (lt_trans hL hx)) hx
    have hcross : x * Real.sinh L < L * Real.sinh x := by
      rw [mul_comm x (Real.sinh L), mul_comm L (Real.sinh x)]
      exact (div_lt_div_iff₀ hL hxpos).mp hmono
    rw [(hderiv x).deriv]
    have hstep : (2 : ℝ) * x < k * Real.sinh x := by
      rw [show k * Real.sinh x = k * Real.sinh x * L / L from by field_simp, lt_div_iff₀ hL]
      calc 2 * x * L = k * (x * Real.sinh L) := by rw [mul_left_comm, hkL]; ring
        _ < k * (L * Real.sinh x) := mul_lt_mul_of_pos_left hcross hkpos
        _ = k * Real.sinh x * L := by ring
    linarith
  -- `f` decreases on `[0, L]` and increases on `[L, ∞)`, so `f ≥ f L = 0` everywhere
  have hfL : f L = 0 := by simp only [hf]; ring
  have hanti : AntitoneOn f (Set.Icc 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L) hdiff.continuous.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun x _ => (hdiff x).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have := hsign x ⟨hx.1, hx.2⟩
      linarith
  have hmono' : MonotoneOn f (Set.Ici L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici L) hdiff.continuous.continuousOn ?_ ?_
    · rw [interior_Ici]
      exact fun x _ => (hdiff x).differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have := hsign' x hx
      linarith
  have hpos : ∀ x : ℝ, 0 < x → (0 : ℝ) ≤ f x := by
    intro x hx
    rcases le_or_gt L x with hLx | hLx
    · have h1 := hmono' (Set.mem_Ici.mpr (le_refl L)) (Set.mem_Ici.mpr hLx) hLx
      rw [hfL] at h1
      exact h1
    · have h1 := hanti (Set.mem_Icc.mpr ⟨hx.le, hLx.le⟩)
        (Set.mem_Icc.mpr ⟨hL.le, le_refl L⟩) hLx.le
      rw [hfL] at h1
      exact h1
  have heven : ∀ x : ℝ, f x = f (-x) := by
    intro x
    simp only [hf]
    rw [Real.cosh_neg]
    ring
  have hfz : (0 : ℝ) ≤ f z := by
    rcases le_or_gt 0 z with hz | hz
    · rcases le_or_gt L z with hLz | hLz
      · have h1 := hmono' (Set.mem_Ici.mpr (le_refl L)) (Set.mem_Ici.mpr hLz) hLz
        rw [hfL] at h1
        exact h1
      · have h1 := hanti (Set.mem_Icc.mpr ⟨hz, hLz.le⟩)
          (Set.mem_Icc.mpr ⟨hL.le, le_refl L⟩) hLz.le
        rw [hfL] at h1
        exact h1
    · rw [heven z]
      exact hpos (-z) (neg_pos.mpr hz)
  simp only [hf] at hfz
  linarith

/-- The mean minimises the second moment.  Only `∑ w = 1` is used — there is NO `0 ≤ w` binder. -/
private lemma classical_var_le_shift {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw1 : ∑ i, w i = 1) (c : ℝ) :
    ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2 ≤ ∑ i, w i * (Y i - c) ^ 2 := by
  classical
  set D : ℝ := ∑ j, w j * Y j with hD
  have hgen : ∀ a : ℝ, ∑ i, w i * (Y i - a) ^ 2
      = (∑ i, w i * (Y i) ^ 2) - 2 * a * D + a ^ 2 := by
    intro a
    have hterm : ∀ i : ι, w i * (Y i - a) ^ 2
        = w i * (Y i) ^ 2 - 2 * a * (w i * Y i) + a ^ 2 * w i := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, ← hD]
    ring
  rw [hgen D, hgen c]
  nlinarith [sq_nonneg (D - c)]

/-- `exp (log x / 2) = √x` for `x > 0`. -/
private lemma exp_log_half {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  have h : Real.exp (Real.log x / 2) ^ 2 = x := by
    rw [sq, ← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring,
      Real.exp_log hx]
  have h2 : Real.sqrt x = Real.sqrt (Real.exp (Real.log x / 2) ^ 2) := by rw [h]
  rw [h2, Real.sqrt_sq (Real.exp_pos _).le]

/-- `cosh t ≥ 1 + t²/2`, equivalently `t² ≤ 2(cosh t − 1)`. -/
private lemma one_add_sq_div_two_le_cosh (t : ℝ) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h := Real.cosh_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  have hcs := Real.cosh_sq (t / 2)
  have hsq : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := by
    rcases le_or_gt (0:ℝ) (t / 2) with h0 | h0
    · have := Real.self_le_sinh_iff.mpr h0
      nlinarith
    · have h1 : (0 : ℝ) ≤ -(t / 2) := by linarith
      have h2 := Real.self_le_sinh_iff.mpr h1
      rw [Real.sinh_neg] at h2
      nlinarith
  nlinarith [hsq, h, hcs]

/-- **Jensen's shadow**: the centred moment generating function is at least `1`. -/
private lemma one_le_sum_mul_exp_of_sum_mul_eq_zero {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hY0 : ∑ i, w i * Y i = 0) (s : ℝ) :
    (1 : ℝ) ≤ ∑ i, w i * Real.exp (s * Y i) := by
  have hle : ∀ i : ι, w i * (1 + s * Y i) ≤ w i * Real.exp (s * Y i) := fun i =>
    mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (s * Y i)]) (hw i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  have hcomp : ∑ i, w i * (1 + s * Y i) = 1 := by
    have hterm : ∀ i : ι, w i * (1 + s * Y i) = w i + s * (w i * Y i) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hw1,
      ← Finset.mul_sum, hY0]
    ring
  rw [hcomp] at hsum
  exact hsum

private lemma cube_le_cube {a b : ℝ} (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- **The classical second-order continuity bound**. -/
private lemma classical_continuity_le {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hY0 : ∑ i, w i * Y i = 0)
    {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 < μ) :
    Real.log (∑ i, w i * Real.exp (ν * Y i))
      ≤ ν ^ 2 * (∑ i, w i * (Y i) ^ 2) / 2
        + ν ^ 3 / (6 * μ ^ 3) * (∑ i, w i * Real.exp (ν * Y i))
          * (Real.log ((∑ i, w i * Real.exp ((ν + μ) * Y i)) + Real.exp 2)) ^ 3 := by
  classical
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  set Mv : ℝ := ∑ i, w i * Real.exp (ν * Y i) with hMv
  set Mvm : ℝ := ∑ i, w i * Real.exp ((ν + μ) * Y i) with hMvm
  set V : ℝ := ∑ i, w i * (Y i) ^ 2 with hV
  set R : ℝ := ∑ i, w i * ((Y i) ^ 3 * Real.exp (ν * Y i)) with hR
  have hweight : ∀ i : ι, 0 ≤ w i * Real.exp (ν * Y i) :=
    fun i => mul_nonneg (hw i) (Real.exp_pos _).le
  have hM1 : (1 : ℝ) ≤ Mv := by
    have hle : ∀ i : ι, w i * (1 + ν * Y i) ≤ w i * Real.exp (ν * Y i) := fun i =>
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (ν * Y i)]) (hw i)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
    have hcomp : ∑ i, w i * (1 + ν * Y i) = 1 := by
      have hterm : ∀ i : ι, w i * (1 + ν * Y i) = w i + ν * (w i * Y i) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hw1,
        ← Finset.mul_sum, hY0]
      ring
    rw [hcomp] at hsum
    exact hsum
  have hMpos : (0 : ℝ) < Mv := lt_of_lt_of_le zero_lt_one hM1
  have hMvmnn : (0 : ℝ) ≤ Mvm :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  have htaylor : Mv ≤ 1 + ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
    have hle : ∀ i : ι, w i * Real.exp (ν * Y i)
        ≤ w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
            + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i)) := fun i =>
      mul_le_mul_of_nonneg_left (exp_le_taylor_three (ν * Y i)) (hw i)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
    have hrhs : ∑ i, w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
          + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i))
        = 1 + ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
      have hterm : ∀ i : ι, w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
            + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i))
          = w i + ν * (w i * Y i) + ν ^ 2 / 2 * (w i * (Y i) ^ 2)
            + ν ^ 3 / 6 * (w i * ((Y i) ^ 3 * Real.exp (ν * Y i))) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, hw1, hY0, ← hV, ← hR]
      ring
    rw [hrhs] at hsum
    exact hsum
  have hlogle : Real.log Mv ≤ ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
    have h1 : Real.log Mv ≤ Mv - 1 := Real.log_le_sub_one_of_pos hMpos
    linarith
  -- the third-order remainder
  have hstep1 : R ≤ (1 / μ ^ 3) * ∑ i, (w i * Real.exp (ν * Y i))
      * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 := by
    rw [hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hcube : (Y i) ^ 3 = (1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i))) ^ 3 := by
      rw [Real.log_exp]; field_simp
    have hmono : (Real.log (Real.exp (μ * Y i))) ^ 3
        ≤ (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 :=
      cube_le_cube (Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_pos 2]))
    calc w i * ((Y i) ^ 3 * Real.exp (ν * Y i))
        = (w i * Real.exp (ν * Y i))
            * ((1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i))) ^ 3) := by rw [← hcube]; ring
      _ ≤ (w i * Real.exp (ν * Y i))
            * ((1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (hweight i)
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (1 / μ ^ 3) * ((w i * Real.exp (ν * Y i))
            * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3) := by ring
  have hJ : ∑ i, (w i * Real.exp (ν * Y i))
      * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
      ≤ Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3 := by
    have hvnn : ∀ i : ι, 0 ≤ w i * Real.exp (ν * Y i) / Mv :=
      fun i => div_nonneg (hweight i) hMpos.le
    have hv1 : ∑ i, w i * Real.exp (ν * Y i) / Mv = 1 := by
      rw [← Finset.sum_div, ← hMv]
      exact div_self hMpos.ne'
    have hjen := concaveOn_cube_log_add.le_map_sum (t := (Finset.univ : Finset ι))
      (w := fun i => w i * Real.exp (ν * Y i) / Mv)
      (p := fun i => Real.exp (μ * Y i)) (fun i _ => hvnn i) hv1
      (fun i _ => (Real.exp_pos _).le)
    simp only [smul_eq_mul] at hjen
    have hpt : ∑ i, w i * Real.exp (ν * Y i) / Mv * Real.exp (μ * Y i) = Mvm / Mv := by
      rw [hMvm, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add,
        show ν * Y i + μ * Y i = (ν + μ) * Y i from by ring]
    rw [hpt] at hjen
    have hmul := mul_le_mul_of_nonneg_left hjen hMpos.le
    calc ∑ i, (w i * Real.exp (ν * Y i))
          * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
        = Mv * ∑ i, w i * Real.exp (ν * Y i) / Mv
            * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
      _ ≤ Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3 := hmul
  have hdiv : Mvm / Mv ≤ Mvm := div_le_self hMvmnn hM1
  have hlast : (Real.log (Mvm / Mv + Real.exp 2)) ^ 3
      ≤ (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    refine cube_le_cube (Real.log_le_log ?_ (by linarith))
    have hq : (0:ℝ) ≤ Mvm / Mv := div_nonneg hMvmnn hMpos.le
    linarith [Real.exp_pos 2]
  have hRbound : R ≤ (1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    have h1 : (1 / μ ^ 3) * ∑ i, (w i * Real.exp (ν * Y i))
        * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
        ≤ (1 / μ ^ 3) * (Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have h2 : (1 / μ ^ 3) * (Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3)
        ≤ (1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
      have : Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3
          ≤ Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left hlast hMpos.le
      nlinarith [this, (by positivity : (0:ℝ) < 1 / μ ^ 3)]
    linarith
  have hν3 : (0 : ℝ) < ν ^ 3 / 6 := by positivity
  have hfin : ν ^ 3 * R / 6
      ≤ ν ^ 3 / (6 * μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hRbound hν3.le
    calc ν ^ 3 * R / 6 = ν ^ 3 / 6 * R := by ring
      _ ≤ ν ^ 3 / 6 * ((1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3) := this
      _ = ν ^ 3 / (6 * μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
          field_simp
  linarith

/-- **C6**, Hölder in the three-factor (NS) form. -/
private lemma holder_three {ι : Type*} [Fintype ι] (a b wt : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hwt : ∀ i, 0 ≤ wt i)
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1)
    (hA : 0 < ∑ i, a i * wt i) (hB : 0 < ∑ i, b i * wt i) :
    ∑ i, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ (∑ i, a i * wt i) ^ (1 - ν) * (∑ i, b i * wt i) ^ ν := by
  classical
  set A : ℝ := ∑ i, a i * wt i with hAdef
  set B : ℝ := ∑ i, b i * wt i with hBdef
  have key : ∀ i : ι, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ (A ^ (1 - ν) * B ^ ν) * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) := by
    intro i
    have hgm := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - ν) hν0.le
      (div_nonneg (ha i) hA.le) (div_nonneg (hb i) hB.le) (by ring)
    have h1 : A ^ (1 - ν) * (a i / A) ^ (1 - ν) = (a i) ^ (1 - ν) := by
      rw [← Real.mul_rpow hA.le (div_nonneg (ha i) hA.le)]
      congr 1
      field_simp
    have h2 : B ^ ν * (b i / B) ^ ν = (b i) ^ ν := by
      rw [← Real.mul_rpow hB.le (div_nonneg (hb i) hB.le)]
      congr 1
      field_simp
    have hfact : (a i) ^ (1 - ν) * (b i) ^ ν
        = (A ^ (1 - ν) * B ^ ν) * ((a i / A) ^ (1 - ν) * (b i / B) ^ ν) := by
      rw [← h1, ← h2]; ring
    calc (a i) ^ (1 - ν) * (b i) ^ ν * wt i
        = (A ^ (1 - ν) * B ^ ν) * (((a i / A) ^ (1 - ν) * (b i / B) ^ ν) * wt i) := by
          rw [hfact]; ring
      _ ≤ (A ^ (1 - ν) * B ^ ν) * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgm (hwt i)) (by positivity)
  calc ∑ i, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ ∑ i, (A ^ (1 - ν) * B ^ ν)
          * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (A ^ (1 - ν) * B ^ ν)
          * ∑ i, ((1 - ν) * (a i / A) + ν * (b i / B)) * wt i := by rw [Finset.mul_sum]
    _ = A ^ (1 - ν) * B ^ ν := by
        have hterm : ∀ i : ι, ((1 - ν) * (a i / A) + ν * (b i / B)) * wt i
            = ((1 - ν) / A) * (a i * wt i) + (ν / B) * (b i * wt i) := fun i => by ring
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← hAdef, ← hBdef]
        field_simp
        ring

/-- **C7**, Klein's inequality with the reference rescaled, in three-factor (NS) form. -/
private lemma klein_scaled {ι : Type*} [Fintype ι] (a b wt : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hwt : ∀ i, 0 ≤ wt i)
    (hA : ∑ i, a i * wt i = 1) (hB : 0 < ∑ i, b i * wt i)
    (hsupp : ∀ i, b i = 0 → a i * wt i = 0) :
    - Real.log (∑ i, b i * wt i)
      ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) * wt i := by
  classical
  set Q : ℝ := ∑ i, b i * wt i with hQdef
  have key : ∀ i : ι, a i * wt i - b i * wt i / Q
      ≤ a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i := by
    intro i
    rcases eq_or_lt_of_le (hwt i) with hw0 | hwpos
    · simp [← hw0]
    rcases eq_or_lt_of_le (ha i) with ha0 | hapos
    · have : b i * wt i / Q ≥ 0 := div_nonneg (mul_nonneg (hb i) (hwt i)) hB.le
      simp only [← ha0]
      nlinarith
    have hbne : b i ≠ 0 := by
      intro h0
      have := hsupp i h0
      nlinarith
    have hbpos : 0 < b i := lt_of_le_of_ne (hb i) (Ne.symm hbne)
    have hs : 0 < b i / (a i * Q) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hs
    rw [Real.log_div hbne (by positivity), Real.log_mul (ne_of_gt hapos) (ne_of_gt hB)] at hlog
    have hstep : a i * (Real.log (a i) - Real.log (b i) + Real.log Q) ≥ a i - b i / Q := by
      have h2 := mul_le_mul_of_nonneg_left hlog hapos.le
      have h3 : a i * (b i / (a i * Q) - 1) = b i / Q - a i := by field_simp
      rw [h3] at h2
      linarith
    have := mul_le_mul_of_nonneg_right hstep hwpos.le
    calc a i * wt i - b i * wt i / Q = (a i - b i / Q) * wt i := by field_simp
      _ ≤ a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i := this
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  have hlhs : ∑ i, (a i * wt i - b i * wt i / Q) = 0 := by
    rw [Finset.sum_sub_distrib, hA, ← Finset.sum_div, ← hQdef, div_self (ne_of_gt hB)]
    ring
  have hrhs : ∑ i, a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i
      = (∑ i, a i * (Real.log (a i) - Real.log (b i)) * wt i) + Real.log Q := by
    have hterm : ∀ i : ι, a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i
        = a i * (Real.log (a i) - Real.log (b i)) * wt i + Real.log Q * (a i * wt i) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum, hA]
    ring
  rw [hlhs, hrhs] at hsum
  linarith

end ClassicalCore
/-- **Variance under two exponential-moment budgets.** If a probability vector `w` and a real
`Y` satisfy `∑ w e^{Y} ≤ a` and `∑ w e^{−Y} ≤ b`, then the variance of `Y` under `w` is at most
`log²(√(ab) + √(ab − 1)) = arcosh²√(ab)`. The bound is attained by a two-point law. -/
theorem classical_var_le_log_sqrt_budget {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {a b : ℝ}
    (hMp : ∑ i, w i * Real.exp (Y i) ≤ a) (hMm : ∑ i, w i * Real.exp (-(Y i)) ≤ b) :
    ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2
      ≤ Real.log (Real.sqrt (a * b) + Real.sqrt (a * b - 1)) ^ 2 := by
  classical
  set t : ℝ := Real.sqrt (a * b) with htdef
  set s : ℝ := Real.sqrt (a * b - 1) with hsdef
  set E1 : ℝ := ∑ i, w i * Real.exp (Y i) with hE1def
  set E2 : ℝ := ∑ i, w i * Real.exp (-(Y i)) with hE2def
  set c : ℝ := (Real.log a - Real.log b) / 2 with hcdef
  -- strict positivity of the two budgets: both moments are strictly positive
  have hwpos : ∃ i, 0 < w i := by
    by_contra hcon
    push Not at hcon
    have h := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hcon i)
    rw [hw1] at h
    norm_num at h
  have hEp : (0 : ℝ) < E1 := by
    obtain ⟨i, hi⟩ := hwpos
    rw [hE1def]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have hEm : (0 : ℝ) < E2 := by
    obtain ⟨i, hi⟩ := hwpos
    rw [hE2def]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have ha : (0 : ℝ) < a := lt_of_lt_of_le hEp hMp
  have hb : (0 : ℝ) < b := lt_of_lt_of_le hEm hMm
  -- the shift `c` makes the two budgeted moments meet at `√(ab) = t`
  have hkey1 : Real.exp (-c) * E1 ≤ t := by
    have hlogE1 : Real.log E1 ≤ Real.log a := Real.log_le_log hEp hMp
    have hexp : Real.exp (-c) * E1 = Real.exp (-c + Real.log E1) := by
      rw [← Real.exp_log hEp, ← Real.exp_add, Real.log_exp]
    have hkey : Real.exp (-c + Real.log E1) ≤ Real.exp (Real.log (a * b) / 2) := by
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb), hcdef]
      linarith
    calc Real.exp (-c) * E1 = Real.exp (-c + Real.log E1) := hexp
      _ ≤ Real.exp (Real.log (a * b) / 2) := hkey
      _ = t := by rw [htdef, exp_log_half (mul_pos ha hb)]
  have hkey2 : Real.exp c * E2 ≤ t := by
    have hlogE2 : Real.log E2 ≤ Real.log b := Real.log_le_log hEm hMm
    have hexp : Real.exp c * E2 = Real.exp (c + Real.log E2) := by
      rw [← Real.exp_log hEm, ← Real.exp_add, Real.log_exp]
    have hkey : Real.exp (c + Real.log E2) ≤ Real.exp (Real.log (a * b) / 2) := by
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb), hcdef]
      linarith
    calc Real.exp c * E2 = Real.exp (c + Real.log E2) := hexp
      _ ≤ Real.exp (Real.log (a * b) / 2) := hkey
      _ = t := by rw [htdef, exp_log_half (mul_pos ha hb)]
  -- the shifted `cosh` moment combines the two budgets
  have hcosh_sum : ∑ i, w i * Real.cosh (Y i - c)
      = (Real.exp (-c) * E1 + Real.exp c * E2) / 2 := by
    have hterm : ∀ i : ι, w i * Real.cosh (Y i - c)
        = (Real.exp (-c) * (w i * Real.exp (Y i))
          + Real.exp c * (w i * Real.exp (-(Y i)))) / 2 := by
      intro i
      have e1 : Real.exp (Y i - c) = Real.exp (-c) * Real.exp (Y i) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : Real.exp (-(Y i - c)) = Real.exp c * Real.exp (-(Y i)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [Real.cosh_eq, e1, e2]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hE1def, ← hE2def]
  -- Cauchy–Schwarz: `1 = (∑ w)² ≤ E1 · E2 ≤ a · b`
  have hab1 : (1 : ℝ) ≤ a * b := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => Real.sqrt (w i * Real.exp (Y i)))
      (fun i => Real.sqrt (w i * Real.exp (-(Y i))))
    have hterm : ∀ i : ι, Real.sqrt (w i * Real.exp (Y i))
        * Real.sqrt (w i * Real.exp (-(Y i))) = w i := by
      intro i
      rw [← Real.sqrt_mul (mul_nonneg (hw i) (Real.exp_pos _).le) (w i * Real.exp (-(Y i)))]
      have huv : w i * Real.exp (Y i) * (w i * Real.exp (-(Y i))) = w i ^ 2 := by
        rw [mul_mul_mul_comm, ← Real.exp_add, show (Y i : ℝ) + -(Y i) = 0 from by ring,
          Real.exp_zero]
        ring
      rw [huv, Real.sqrt_sq (hw i)]
    have hsum : ∑ i, Real.sqrt (w i * Real.exp (Y i))
        * Real.sqrt (w i * Real.exp (-(Y i))) = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i), hw1]
    have hE1sq : ∑ i, Real.sqrt (w i * Real.exp (Y i)) ^ 2 = E1 :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le))
    have hE2sq : ∑ i, Real.sqrt (w i * Real.exp (-(Y i))) ^ 2 = E2 :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le))
    rw [hE1sq, hE2sq, hsum, sq] at hcs
    have h2 : E1 * E2 ≤ a * b := mul_le_mul hMp hMm hEm.le ha.le
    linarith
  rcases eq_or_lt_of_le hab1 with hab_eq | hab1'
  · -- degenerate case `ab = 1`: Cauchy–Schwarz is attained and the variance vanishes
    have habeq : a * b = 1 := hab_eq.symm
    have ht1 : t = 1 := by rw [htdef, habeq, Real.sqrt_one]
    have hs0 : s = 0 := by rw [hsdef, habeq, sub_self, Real.sqrt_zero]
    have hb1 : Real.exp (-c) * E1 ≤ 1 := by rw [← ht1]; exact hkey1
    have hb2 : Real.exp c * E2 ≤ 1 := by rw [← ht1]; exact hkey2
    have hsumcosh : ∑ i, w i * Real.cosh (Y i - c) ≤ 1 := by
      rw [hcosh_sum]
      have hle : Real.exp (-c) * E1 + Real.exp c * E2 ≤ 2 := by linarith
      linarith
    have hshift : ∑ i, w i * (Y i - c) ^ 2 ≤ 0 := by
      have hpoint : ∀ i : ι, w i * (Y i - c) ^ 2
          ≤ 2 * (w i * Real.cosh (Y i - c)) - 2 * w i := by
        intro i
        have h1 : (Y i - c) ^ 2 ≤ 2 * Real.cosh (Y i - c) - 2 := by
          have hc := one_add_sq_div_two_le_cosh (Y i - c)
          linarith
        calc w i * (Y i - c) ^ 2
            ≤ w i * (2 * Real.cosh (Y i - c) - 2) := mul_le_mul_of_nonneg_left h1 (hw i)
          _ = 2 * (w i * Real.cosh (Y i - c)) - 2 * w i := by ring
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
      have hsplit : (∑ i, (2 * (w i * Real.cosh (Y i - c)) - 2 * w i))
          = 2 * (∑ i, w i * Real.cosh (Y i - c)) - 2 * (∑ i, w i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [hsplit, hw1] at hsum
      linarith
    refine (classical_var_le_shift w Y hw1 c).trans ?_
    rw [ht1, hs0, add_zero, Real.log_one]
    norm_num
    exact hshift
  · -- the non-degenerate case `ab > 1`
    have ht1 : (1 : ℝ) < t := by
      rw [htdef]
      calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
        _ < Real.sqrt (a * b) := Real.sqrt_lt_sqrt zero_le_one hab1'
    have hts : (0 : ℝ) < t + s := by
      have := Real.sqrt_nonneg (a * b - 1)
      linarith
    have hs_nn : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
    set L : ℝ := Real.log (t + s) with hLdef
    have hL : (0 : ℝ) < L := Real.log_pos (by linarith)
    -- `cosh L = t`
    have hmul : (t + s) * (t - s) = 1 := by
      have h1 : (t + s) * (t - s) = t * t - s * s := by ring
      have ht2 : t * t = a * b := by
        rw [htdef, Real.mul_self_sqrt (mul_nonneg ha.le hb.le)]
      have hs2 : s * s = a * b - 1 := by rw [hsdef, Real.mul_self_sqrt (by linarith)]
      rw [h1, ht2, hs2]
      linarith
    have hinv : (t + s)⁻¹ = t - s :=
      (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm
    have hcoshL : Real.cosh L = t := by
      rw [hLdef, Real.cosh_eq, Real.exp_log hts, Real.exp_neg, Real.exp_log hts, hinv]
      ring
    -- the tangent majorant, summed against `w`
    have ht_nn : (0 : ℝ) ≤ t := by rw [htdef]; exact Real.sqrt_nonneg _
    have hcoef : (0 : ℝ) ≤ 2 * L / Real.sinh L := by positivity
    have hsumcosh : ∑ i, w i * Real.cosh (Y i - c) ≤ Real.cosh L := by
      have hnum : Real.exp (-c) * E1 + Real.exp c * E2 ≤ t + t := by
        have h1 := hkey1
        have h2 := hkey2
        linarith
      have hstep : (Real.exp (-c) * E1 + Real.exp c * E2) / 2 ≤ (t + t) / 2 :=
        div_le_div₀ (show (0 : ℝ) ≤ t + t by linarith) hnum zero_lt_two (le_refl 2)
      rw [hcosh_sum]
      refine hstep.trans ?_
      rw [show (t + t) / 2 = t from by ring, hcoshL]
    have hshift : ∑ i, w i * (Y i - c) ^ 2 ≤ L ^ 2 := by
      have hpoint : ∀ i : ι, w i * (Y i - c) ^ 2
          ≤ w i * (L ^ 2 + (2 * L / Real.sinh L) * (Real.cosh (Y i - c) - Real.cosh L)) :=
        fun i => mul_le_mul_of_nonneg_left (sq_le_cosh_tangent L hL (Y i - c)) (hw i)
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
      have hsplit : ∑ i, w i * (L ^ 2 + (2 * L / Real.sinh L)
            * (Real.cosh (Y i - c) - Real.cosh L))
          = L ^ 2 + (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
            - (2 * L / Real.sinh L) * Real.cosh L := by
        have hexpand : ∑ i, w i * (L ^ 2 + (2 * L / Real.sinh L)
              * (Real.cosh (Y i - c) - Real.cosh L))
            = L ^ 2 * (∑ i, w i) + (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
              - (2 * L / Real.sinh L) * Real.cosh L * (∑ i, w i) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hexpand, hw1]
        ring
      rw [hsplit] at hsum
      have hmid : (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
          ≤ (2 * L / Real.sinh L) * Real.cosh L :=
        mul_le_mul_of_nonneg_left hsumcosh hcoef
      linarith
    calc ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2
        ≤ ∑ i, w i * (Y i - c) ^ 2 := classical_var_le_shift w Y hw1 c
      _ ≤ L ^ 2 := hshift

end InfoTheory.Renyi

end
