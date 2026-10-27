import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.MixtureFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.FlaggedBounds
import QCryptLean.Quantum.Metrics.Scaling
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Mixture Distance -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder MatrixOrder
open private InfoTheory.SmoothMinEntropy.le_sum_mul_add_sqrt_mul_of_forall_le
  from QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.MixtureFloor
variable {Q I : Type*} [Fintype Q] [Fintype I] [Nonempty Q]

/-- Subconvex mixtures preserve any common purified-distance bound. -/
theorem purifiedDistance_subconvex_mixture
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (a b : I → SubDensityOp Q) (ρ σ : SubDensityOp Q)
    (hρ : ρ.toOp = ∑ i, (p i : ℂ) • (a i).toOp)
    (hσ : σ.toOp = ∑ i, (p i : ℂ) • (b i).toOp)
    {ε : ℝ} (hε : 0 ≤ ε) (hab : ∀ i, purifiedDistance (a i) (b i) ≤ ε) :
    purifiedDistance ρ σ ≤ ε := by
  classical
  let A : I → PosSemidefOp Q := fun i =>
    ⟨(p i : ℂ) • (a i).toOp, (a i).posSemidef.smul (RCLike.ofReal_nonneg.mpr (hp i))⟩
  let B : I → PosSemidefOp Q := fun i =>
    ⟨(p i : ℂ) • (b i).toOp, (b i).posSemidef.smul (RCLike.ofReal_nonneg.mpr (hp i))⟩
  have hsum : ∑ i, p i * fidelity (a i).toPosSemidefOp (b i).toPosSemidefOp ≤
      fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
    rcases isEmpty_or_nonempty I with he | hn
    · simpa only [Finset.sum_of_isEmpty] using fidelity_nonneg ρ.toPosSemidefOp σ.toPosSemidefOp
    · have hf (i : I) := fidelity_smul_smul (hp i) (hp i)
        (a i).toPosSemidefOp (b i).toPosSemidefOp (A i) (B i) rfl rfl
      simp only [Real.sqrt_mul_self (hp _)] at hf
      have ha : sumPosSemidefOp Finset.univ A = ρ.toPosSemidefOp := Subtype.ext hρ.symm
      have hb : sumPosSemidefOp Finset.univ B = σ.toPosSemidefOp := Subtype.ext hσ.symm
      simpa only [ha, hb, hf] using sum_fidelity_le_fidelity_sum A B
  have htrace (v : I → SubDensityOp Q) (τ : SubDensityOp Q)
      (hτ : τ.toOp = ∑ i, (p i : ℂ) • (v i).toOp) :
      τ.trace = ∑ i, p i * (v i).trace := by
    simp only [SubDensityOp.trace, hτ, Matrix.trace_sum, Complex.re_sum,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  let w : Option I → ℝ := fun o => Option.elim o (1 - ∑ i, p i) p
  let f : Option I → ℝ := fun o => Option.elim o 0
    (fun i => fidelity (a i).toPosSemidefOp (b i).toPosSemidefOp)
  let u : Option I → ℝ := fun o => Option.elim o 1 (fun i => 1 - (a i).trace)
  let v : Option I → ℝ := fun o => Option.elim o 1 (fun i => 1 - (b i).trace)
  have hw : ∀ i, 0 ≤ w i := by
    intro i; cases i with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hp i
  have hf : ∀ i, 0 ≤ f i := by
    intro i; cases i with
    | none => exact le_rfl
    | some i => exact fidelity_nonneg _ _
  have hu : ∀ i, 0 ≤ u i := by
    intro i; cases i with
    | none => exact zero_le_one
    | some i => exact sub_nonneg.mpr (a i).trace_le_one
  have hv : ∀ i, 0 ≤ v i := by
    intro i; cases i with
    | none => exact zero_le_one
    | some i => exact sub_nonneg.mpr (b i).trace_le_one
  have hc : Real.sqrt (1 - ε ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (sub_le_self _ (sq_nonneg _))
  have hw1 : ∑ i, w i = 1 := by
    simp only [Fintype.sum_option, w, Option.elim_none, Option.elim_some]
    ring
  have hcpt : ∀ i, Real.sqrt (1 - ε ^ 2) ≤ f i + Real.sqrt (u i * v i) := by
    intro i
    cases i with
    | none => simpa only [f, u, v, Option.elim_none, one_mul, Real.sqrt_one, zero_add] using hc
    | some i =>
      have hsq := (Real.sqrt_le_iff.mp (hab i)).2
      have hnn := fidelityGen_nonneg (a i) (b i)
      change Real.sqrt (1 - ε ^ 2) ≤ fidelityGen (a i) (b i)
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hnn, by linarith⟩
  have hkey := InfoTheory.SmoothMinEntropy.le_sum_mul_add_sqrt_mul_of_forall_le
    w f u v (Real.sqrt (1 - ε ^ 2)) hw hf hu hv hc hw1 hcpt
  have htu : ∑ i, w i * u i = 1 - ρ.trace := by
    simp only [Fintype.sum_option, w, u, Option.elim_none, Option.elim_some, mul_one,
      mul_sub, Finset.sum_sub_distrib, htrace a ρ hρ]
    ring
  have htv : ∑ i, w i * v i = 1 - σ.trace := by
    simp only [Fintype.sum_option, w, v, Option.elim_none, Option.elim_some, mul_one,
      mul_sub, Finset.sum_sub_distrib, htrace b σ hσ]
    ring
  rw [htu, htv] at hkey
  simp only [Fintype.sum_option, w, f, Option.elim_none, Option.elim_some, mul_zero,
    zero_add] at hkey
  have hfg : Real.sqrt (1 - ε ^ 2) ≤ fidelityGen ρ σ :=
    hkey.trans (add_le_add hsum le_rfl)
  have hsq := (Real.sqrt_le_iff.mp hfg).2
  exact (Real.sqrt_le_iff).mpr ⟨hε, by linarith⟩

end InfoTheory.SmoothMinEntropy
