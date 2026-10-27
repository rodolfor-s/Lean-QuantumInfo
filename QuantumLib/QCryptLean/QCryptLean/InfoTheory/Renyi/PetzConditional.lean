import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.TensorPower

/-! # Petz Rényi divergence and matrix order estimates -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi


/-- `Tr[ρ^α σ^{1−α}]`, the argument of the Petz Rényi divergence
(Dupuis–Fawzi `\label{def:petz-renyi-divergence}`, `:294`).

Both powers are `CFC.rpow`; at the negative exponent `1 − α < 0` this is the support
pseudo-inverse power. The definition applies to matrices on any finite index type. -/
def petzTrace {m : Type*} [Fintype m] [DecidableEq m]
    (α : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  ((ρ ^ (α : ℝ)) * (σ ^ (1 - α : ℝ))).trace.re

/-- `D'_α(ρ‖σ) = 1/(α−1) · log₂ Tr[ρ^α σ^{1−α}]`, Dupuis–Fawzi `:294`.

This is the `1 < α ≤ 2`, `Supp ρ ⊆ Supp σ` branch of `:294` only. The `α = 1`,
`0 < α < 1` and out-of-support (`+∞`) branches of that definition are **not** part of
this declaration and must not be assumed of it. -/
def petzRenyiDivergence {m : Type*} [Fintype m] [DecidableEq m]
    (α : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  (1 / (α - 1)) * Real.logb 2 (petzTrace α ρ σ)


section Toolkit

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `CStarAlgebra (Matrix m m ℂ)`, assembled from the `Matrix.Norms.L2Operator` scoped
`NormedRing` / `NormedAlgebra` / `CStarRing` instances that are already open in this file.
Löwner–Heinz (`CFC.rpow_le_rpow`), the C⋆-identity and `CFC.log_le_log` are all stated for
`[CStarAlgebra A]`. Declared as a `local instance` so the L2Operator `NormedRing` does not
leak into downstream typeclass synthesis. -/
@[implicit_reducible] private noncomputable def instCStarAlgebraMatrix
    (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

attribute [local instance] instCStarAlgebraMatrix

/-- The real matrix power `A ^ (r : ℝ)` (`CFC.rpow`), stated once for this section. It is the
instance typeclass search finds; declaring it short-circuits that search, which is slow here and
would otherwise rerun at every `^`. -/
private local instance instHPowRealMatrix : HPow (Matrix m m ℂ) ℝ (Matrix m m ℂ) :=
  inferInstance

/-- The real spectrum of a matrix is finite, hence discrete, hence every real function is
continuous on it. This is what lets `cfc` be used at `t ^ (-ν)` and at `Real.log`, both of
which are discontinuous at `0`, without excluding singular operators. -/
private lemma contOn_spec (f : ℝ → ℝ) (a : Matrix m m ℂ) : ContinuousOn f (spectrum ℝ a) :=
  (Matrix.finite_real_spectrum (A := a)).continuousOn f

omit [DecidableEq m] in
/-- Conjugation preserves the Loewner order. -/
private lemma conj_le_conj (A B R : Matrix m m ℂ) (h : A ≤ B) : Rᴴ * A * R ≤ Rᴴ * B * R := by
  rw [Matrix.le_iff] at h ⊢
  rw [show Rᴴ * B * R - Rᴴ * A * R = Rᴴ * (B - A) * R by rw [mul_sub, sub_mul]]
  exact h.conjTranspose_mul_mul_same _

omit [DecidableEq m] in
/-- The Loewner order dominates the real trace. -/
private lemma trace_re_mono (A B : Matrix m m ℂ) (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  rw [Matrix.le_iff] at h
  have h2 := h.trace_nonneg
  rw [Matrix.trace_sub] at h2
  have h3 := (Complex.nonneg_iff.mp h2).1
  simp only [Complex.sub_re] at h3
  linarith

omit [Fintype m] [DecidableEq m] in
private lemma selfadj_of_nonneg {A : Matrix m m ℂ} (h : 0 ≤ A) : Aᴴ = A :=
  (Matrix.nonneg_iff_posSemidef.mp h).isHermitian

omit [DecidableEq m] in
private lemma conj_nonneg (D R : Matrix m m ℂ) (hD : 0 ≤ D) : 0 ≤ Rᴴ * D * R := by
  simpa using conj_le_conj 0 D R hD

/-- `CFC.rpow` through the real functional calculus, where the spectrum is finite. -/
private lemma rpow_eq_cfc (a : Matrix m m ℂ) (ha : 0 ≤ a) (y : ℝ) :
    a ^ y = cfc (fun t : ℝ => t ^ y) a := CFC.rpow_eq_cfc_real ha

private lemma rpow_mul_rpow_eq (a : Matrix m m ℂ) (ha : 0 ≤ a) (x y : ℝ) :
    a ^ x * a ^ y = cfc (fun t : ℝ => t ^ x * t ^ y) a := by
  rw [rpow_eq_cfc a ha x, rpow_eq_cfc a ha y,
    ← cfc_mul _ _ a (contOn_spec _ a) (contOn_spec _ a)]

/-- `a^x · a^y = a^(x+y)` for a positive semidefinite `a`, with **no** invertibility
hypothesis (unlike Mathlib's `CFC.rpow_add`). The three `≠ 0` side conditions are exactly
what the pseudo-inverse convention `0 ^ y = 0` (`y ≠ 0`) needs at the kernel of `a`. -/
private lemma rpow_add_ne (a : Matrix m m ℂ) (ha : 0 ≤ a) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) : a ^ x * a ^ y = a ^ (x + y) := by
  rw [rpow_mul_rpow_eq a ha x y, rpow_eq_cfc a ha (x + y)]
  refine cfc_congr fun t ht => ?_
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg ha ht) with h | h
  · simp [← h, Real.zero_rpow hx, Real.zero_rpow hy, Real.zero_rpow hxy]
  · rw [Real.rpow_add h]

private lemma rpow_half_mul_self (a : Matrix m m ℂ) (ha : 0 ≤ a) :
    a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rw [rpow_add_ne a ha (by norm_num) (by norm_num) (by norm_num),
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, CFC.rpow_one a ha]

/-- `a^{-ν/2} a^ν a^{-ν/2}` is the support projection of `a`, hence `≤ 1`. -/
private lemma rpow_sandwich_self_le_one (a : Matrix m m ℂ) (ha : 0 ≤ a) {ν : ℝ} (hν : 0 < ν) :
    a ^ (-ν / 2) * a ^ ν * a ^ (-ν / 2) ≤ 1 := by
  rw [rpow_mul_rpow_eq a ha (-ν / 2) ν, rpow_eq_cfc a ha (-ν / 2),
    ← cfc_mul _ _ a (contOn_spec _ a) (contOn_spec _ a)]
  refine cfc_le_one _ _ fun t ht => ?_
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg ha ht) with h | h
  · simp [← h, Real.zero_rpow (by linarith : -ν / 2 ≠ 0), Real.zero_rpow hν.ne']
  · rw [← Real.rpow_add h, ← Real.rpow_add h,
      show -ν / 2 + ν + -ν / 2 = 0 by ring, Real.rpow_zero]

/-- **The Löwner–Heinz step**, Dupuis–Fawzi `:493` with the exponent `-1/2` generalised to
`-ν`: for `0 ≤ A ≤ B` and `ν ∈ (0,1]`, `A^{ν/2} B^{-ν} A^{ν/2} ≤ 1`.

`ν ≤ 1` is used exactly once, in `CFC.rpow_le_rpow`; that is the whole reason the range of
the main theorem is `(1,2]`. Douglas' lemma is replaced by the C⋆-identity
`‖T*T‖ = ‖T‖² = ‖TT*‖`, which is in Mathlib. -/
private lemma sandwich_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    A ^ (ν / 2) * B ^ (-ν) * A ^ (ν / 2) ≤ 1 := by
  have hB : 0 ≤ B := hA.trans hAB
  -- The half exponents are nonzero, and each pair of halves adds up to the full exponent.
  have hν2 : (ν / 2 : ℝ) ≠ 0 := (half_pos hν0).ne'
  have hnν2 : (-ν / 2 : ℝ) ≠ 0 := by rw [neg_div]; exact neg_ne_zero.mpr hν2
  have hsaA : (A ^ (ν / 2 : ℝ))ᴴ = A ^ (ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  have hsaB : (B ^ (-ν / 2 : ℝ))ᴴ = B ^ (-ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  set T : Matrix m m ℂ := B ^ (-ν / 2 : ℝ) * A ^ (ν / 2 : ℝ) with hTdef
  have hTstar : star T = A ^ (ν / 2 : ℝ) * B ^ (-ν / 2 : ℝ) := by
    rw [hTdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hsaA, hsaB]
  have hTT : star T * T = A ^ (ν / 2 : ℝ) * B ^ (-ν) * A ^ (ν / 2 : ℝ) := by
    rw [hTstar, hTdef, ← mul_assoc, mul_assoc (A ^ (ν / 2 : ℝ)),
      rpow_add_ne B hB hnν2 hnν2 (by rw [add_halves]; exact neg_ne_zero.mpr hν0.ne'),
      add_halves]
  have hTTstar : T * star T = B ^ (-ν / 2 : ℝ) * A ^ ν * B ^ (-ν / 2 : ℝ) := by
    rw [hTstar, hTdef, ← mul_assoc, mul_assoc (B ^ (-ν / 2 : ℝ)),
      rpow_add_ne A hA hν2 hν2 (by rw [add_halves]; exact hν0.ne'), add_halves]
  have hstep : T * star T ≤ 1 := by
    rw [hTTstar]
    calc B ^ (-ν / 2 : ℝ) * A ^ ν * B ^ (-ν / 2 : ℝ)
        ≤ B ^ (-ν / 2 : ℝ) * B ^ ν * B ^ (-ν / 2 : ℝ) := by
          have := conj_le_conj (A ^ ν) (B ^ ν) (B ^ (-ν / 2 : ℝ))
            (CFC.rpow_le_rpow ⟨hν0.le, hν1⟩ hAB)
          rwa [hsaB] at this
      _ ≤ 1 := rpow_sandwich_self_le_one B hB hν0
  have hTTs_nonneg : 0 ≤ T * star T := by
    have := Matrix.posSemidef_conjTranspose_mul_self (star T)
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at this
    exact Matrix.nonneg_iff_posSemidef.mpr this
  have hsTT_nonneg : 0 ≤ star T * T := by
    have := Matrix.posSemidef_conjTranspose_mul_self T
    rw [← Matrix.star_eq_conjTranspose] at this
    exact Matrix.nonneg_iff_posSemidef.mpr this
  have hnorm1 : ‖T * star T‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hTTs_nonneg).mpr hstep
  have hnorm2 : ‖star T * T‖ ≤ 1 := by
    exact ((CStarRing.norm_star_mul_self (x := T)).trans
      (CStarRing.norm_self_mul_star (x := T)).symm).le.trans hnorm1
  rw [← hTT]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hsTT_nonneg).mp hnorm2

/-- **Dupuis–Fawzi `:493`, in trace form.** For `0 ≤ A ≤ B` and `ν ∈ (0,1]`,
`0 ≤ Tr[A^{1+ν} B^{-ν}] ≤ Tr[A]`. No support or positive-definiteness hypothesis is
needed: the sandwich by `A^{ν/2}` projects onto `Supp A ⊆ Supp B` automatically. -/
private lemma petzTrace_bound {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    0 ≤ (A ^ (1 + ν) * B ^ (-ν)).trace.re ∧
      (A ^ (1 + ν) * B ^ (-ν)).trace.re ≤ A.trace.re := by
  have hsaN : (A ^ (ν / 2 : ℝ))ᴴ = A ^ (ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  have hsaH : (A ^ (1 / 2 : ℝ))ᴴ = A ^ (1 / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  set M : Matrix m m ℂ := A ^ (ν / 2 : ℝ) * B ^ (-ν) * A ^ (ν / 2 : ℝ) with hMdef
  have hM1 : M ≤ 1 := sandwich_le_one hν0 hν1 A B hA hAB
  have hM0 : 0 ≤ M := by
    have := conj_nonneg (B ^ (-ν)) (A ^ (ν / 2 : ℝ)) CFC.rpow_nonneg
    rwa [hsaN] at this
  have hAnu : A ^ (ν / 2 : ℝ) * A * A ^ (ν / 2 : ℝ) = A ^ (1 + ν) := by
    have hAnu' : A ^ (ν / 2 : ℝ) * A ^ (1 : ℝ) * A ^ (ν / 2 : ℝ) = A ^ (1 + ν) := by
      rw [rpow_add_ne A hA (by positivity) one_ne_zero (by positivity),
        rpow_add_ne A hA (by positivity) (by positivity) (by positivity),
        show (ν / 2 + 1 + ν / 2 : ℝ) = 1 + ν by ring]
    rwa [CFC.rpow_one A hA] at hAnu'
  have htr : (A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ)).trace
      = (A ^ (1 + ν) * B ^ (-ν)).trace := by
    rw [Matrix.trace_mul_comm (A ^ (1 / 2 : ℝ) * M) (A ^ (1 / 2 : ℝ)), ← mul_assoc,
      rpow_half_mul_self A hA, hMdef, ← mul_assoc, ← mul_assoc,
      Matrix.trace_mul_comm (A * A ^ (ν / 2 : ℝ) * B ^ (-ν)) (A ^ (ν / 2 : ℝ)),
      ← mul_assoc, ← mul_assoc]
    congr 2
  refine ⟨?_, ?_⟩
  · rw [← htr]
    have h0 : (0 : Matrix m m ℂ) ≤ A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ) := by
      have := conj_nonneg M (A ^ (1 / 2 : ℝ)) hM0
      rwa [hsaH] at this
    simpa using trace_re_mono 0 _ h0
  · rw [← htr]
    have h1 : A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ) ≤ A := by
      have := conj_le_conj M 1 (A ^ (1 / 2 : ℝ)) hM1
      rwa [hsaH, mul_one, rpow_half_mul_self A hA] at this
    exact trace_re_mono _ _ h1

omit [DecidableEq m] in
private lemma trace_mul_nonneg (A D : Matrix m m ℂ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ (A * D).trace.re := by
  classical
  have h := conj_nonneg D (A ^ (1 / 2 : ℝ)) hD
  rw [selfadj_of_nonneg (CFC.rpow_nonneg : (0 : Matrix m m ℂ) ≤ A ^ (1 / 2 : ℝ))] at h
  have htr : (A * D).trace = (A ^ (1 / 2 : ℝ) * D * A ^ (1 / 2 : ℝ)).trace := by
    rw [Matrix.trace_mul_comm (A ^ (1 / 2 : ℝ) * D) (A ^ (1 / 2 : ℝ)), ← mul_assoc,
      rpow_half_mul_self A hA]
  rw [htr]
  simpa using trace_re_mono 0 _ h

omit [DecidableEq m] in
private lemma trace_mul_mono (A C D : Matrix m m ℂ) (hA : 0 ≤ A) (h : C ≤ D) :
    (A * C).trace.re ≤ (A * D).trace.re := by
  have h2 := trace_mul_nonneg A (D - C) hA (sub_nonneg.mpr h)
  rw [mul_sub, Matrix.trace_sub] at h2
  simp only [Complex.sub_re] at h2
  linarith

private lemma isStrictlyPositive_smul_one {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive (ε • (1 : Matrix m m ℂ)) :=
  ⟨smul_nonneg hε.le zero_le_one,
    ⟨⟨ε • (1 : Matrix m m ℂ), ε⁻¹ • (1 : Matrix m m ℂ),
      by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hε.ne', one_smul],
      by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hε.ne', one_smul]⟩, rfl⟩⟩

private lemma add_smul_one_eq_cfc (a : Matrix m m ℂ) (ha : 0 ≤ a) (ε : ℝ) :
    a + ε • (1 : Matrix m m ℂ) = cfc (fun t : ℝ => t + ε) a := by
  rw [cfc_add a (fun t : ℝ => t) (fun _ : ℝ => ε) (contOn_spec _ a) (contOn_spec _ a),
    cfc_id' ℝ a ha.isSelfAdjoint, cfc_const ε a ha.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]

private lemma log_add_smul_one (a : Matrix m m ℂ) (ha : 0 ≤ a) (ε : ℝ) :
    CFC.log (a + ε • (1 : Matrix m m ℂ)) = cfc (fun t : ℝ => Real.log (t + ε)) a := by
  rw [add_smul_one_eq_cfc a ha ε]
  exact (cfc_comp Real.log (fun t : ℝ => t + ε) a ha.isSelfAdjoint
    (((Matrix.finite_real_spectrum (A := a)).image _).continuousOn _) (contOn_spec _ a)).symm

private lemma mul_cfc_eq (a : Matrix m m ℂ) (ha : 0 ≤ a) (g : ℝ → ℝ) :
    a * cfc g a = cfc (fun t : ℝ => t * g t) a := by
  rw [cfc_mul (fun t : ℝ => t) g a (contOn_spec _ a) (contOn_spec _ a),
    cfc_id' ℝ a ha.isSelfAdjoint]

private lemma log_eq_cfc (a : Matrix m m ℂ) : CFC.log a = cfc Real.log a := rfl

/-- `Tr[A log A] ≤ Tr[A log (A + ε)]`: both sides are `cfc`s of the *same* operator, so
this is the pointwise `t log t ≤ t log (t + ε)` on `[0,∞)` — no operator monotonicity, and
in particular no positive-definiteness, is involved. -/
private lemma mul_log_le_mul_log_add (A : Matrix m m ℂ) (hA : 0 ≤ A) {ε : ℝ} (hε0 : 0 < ε) :
    A * CFC.log A ≤ A * CFC.log (A + ε • (1 : Matrix m m ℂ)) := by
  rw [log_eq_cfc A, log_add_smul_one A hA ε, mul_cfc_eq A hA Real.log,
    mul_cfc_eq A hA (fun t : ℝ => Real.log (t + ε))]
  refine cfc_mono (fun t ht => ?_) (contOn_spec _ A) (contOn_spec _ A)
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg hA ht) with h | h
  · simp [← h]
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (by linarith)) h.le

/-- `log (B + ε) ≤ log B + ε · B⁻¹` (pseudo-inverse), for `0 < ε ≤ 1`. Again both sides are
`cfc`s of `B`; pointwise this is `log ε ≤ 0` at `t = 0` and `log (1 + ε/t) ≤ ε/t` at
`t > 0`. This is what replaces an `ε → 0` limit of `CFC.log (B + ε)`, which does **not**
converge when `B` is singular. -/
private lemma log_add_le_log_add_smul (B : Matrix m m ℂ) (hB : 0 ≤ B) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    CFC.log (B + ε • (1 : Matrix m m ℂ)) ≤ CFC.log B + ε • cfc (fun t : ℝ => t⁻¹) B := by
  rw [log_add_smul_one B hB ε, log_eq_cfc B,
    ← cfc_smul ε (fun t : ℝ => t⁻¹) B (contOn_spec _ B),
    ← cfc_add B Real.log (fun t : ℝ => ε • t⁻¹) (contOn_spec _ B) (contOn_spec _ B)]
  refine cfc_mono (fun t ht => ?_) (contOn_spec _ B) (contOn_spec _ B)
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg hB ht) with h | h
  · simp [← h, Real.log_nonpos hε0.le hε1]
  · have h1 : Real.log ((t + ε) / t) ≤ (t + ε) / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) h.ne'] at h1
    have h2 : (t + ε) / t - 1 = ε * t⁻¹ := by field_simp; ring
    simp only [smul_eq_mul]
    linarith

private lemma trace_mul_log_le_aux (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (A * CFC.log A).trace.re
      ≤ (A * CFC.log B).trace.re + ε * (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := by
  have hB : 0 ≤ B := hA.trans hAB
  have hsp : IsStrictlyPositive (A + ε • (1 : Matrix m m ℂ)) :=
    IsStrictlyPositive.nonneg_add hA (isStrictlyPositive_smul_one hε0)
  have stepB : CFC.log (A + ε • (1 : Matrix m m ℂ))
      ≤ CFC.log (B + ε • (1 : Matrix m m ℂ)) :=
    CFC.log_le_log (add_le_add hAB (le_refl (ε • (1 : Matrix m m ℂ)))) hsp
  calc (A * CFC.log A).trace.re
      ≤ (A * CFC.log (A + ε • (1 : Matrix m m ℂ))).trace.re :=
        trace_re_mono _ _ (mul_log_le_mul_log_add A hA hε0)
    _ ≤ (A * CFC.log (B + ε • (1 : Matrix m m ℂ))).trace.re :=
        trace_mul_mono A _ _ hA stepB
    _ ≤ (A * (CFC.log B + ε • cfc (fun t : ℝ => t⁻¹) B)).trace.re :=
        trace_mul_mono A _ _ hA (log_add_le_log_add_smul B hB hε0 hε1)
    _ = (A * CFC.log B).trace.re + ε * (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := by
        rw [mul_add, Matrix.trace_add, Complex.add_re, mul_smul_comm, Matrix.trace_smul]
        simp

/-- **The `ν → 0` shadow of `:493`** (Tomamichel `cond.tex:577`): for `0 ≤ A ≤ B`,
`Tr[A log A] ≤ Tr[A log B]`, with `CFC.log = cfc Real.log` and `Real.log 0 = 0`.

The *operator* inequality `log A ≤ log B` is false on `ker A`; the proof therefore runs the
operator-monotone step on the strictly positive `A + ε`, `B + ε`, and pays for removing the
`ε` with the two same-operator `cfc` comparisons above, whose cost `ε · Tr[A B⁻¹]` vanishes
as `ε → 0`. -/
private lemma trace_mul_log_le_of_le (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    (A * CFC.log A).trace.re ≤ (A * CFC.log B).trace.re := by
  have hB : 0 ≤ B := hA.trans hAB
  have hC0 : (0 : Matrix m m ℂ) ≤ cfc (fun t : ℝ => t⁻¹) B :=
    cfc_nonneg fun t ht => inv_nonneg.mpr (spectrum_nonneg_of_nonneg hB ht)
  have hK0 : 0 ≤ (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := trace_mul_nonneg A _ hA hC0
  set K : ℝ := (A * cfc (fun t : ℝ => t⁻¹) B).trace.re with hKdef
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hε0 : 0 < min 1 (δ / (K + 1)) := lt_min one_pos (by positivity)
  have hkey := trace_mul_log_le_aux A B hA hAB hε0 (min_le_left _ _)
  rw [← hKdef] at hkey
  have hεb : min 1 (δ / (K + 1)) ≤ δ / (K + 1) := min_le_right _ _
  have hεK : min 1 (δ / (K + 1)) * K ≤ δ := by
    have h1 : min 1 (δ / (K + 1)) * K ≤ δ / (K + 1) * K :=
      mul_le_mul_of_nonneg_right hεb hK0
    have h2 : δ / (K + 1) * K ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
      nlinarith
    linarith
  linarith

end Toolkit

attribute [local instance] instCStarAlgebraMatrix


section TensorPowerToolkit

end TensorPowerToolkit


end InfoTheory.Renyi

end
