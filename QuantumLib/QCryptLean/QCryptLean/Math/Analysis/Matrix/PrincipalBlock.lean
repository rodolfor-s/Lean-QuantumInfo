import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QCryptLean.Math.LinearAlgebra.BlockLinear

/-!
# Principal blocks for variational data processing

Block compression, inverse bounds and operator concavity.  This file studies the `₁₁`
principal block of positive block matrices and proves the resulting
order inequalities for inverse, `rpow`, and logarithm expressions arising in variational formulas.

## Main definitions
- `toBlocks₁₁CLM`: continuous linear map extracting the `₁₁` principal block

## Main statements
- `inv_toBlocks₁₁_le_toBlocks₁₁_inv`: inverse comparison between a principal block and the full
inverse
- `toBlocks₁₁_rpow_le_rpow_toBlocks₁₁`: operator concavity of `rpow` on the `₁₁` block
- `toBlocks₁₁_log_le_log_toBlocks₁₁`: principal-block logarithm inequality
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology
open Matrix

noncomputable section

namespace Matrix

/-- The C⋆-algebra structure inherited from complex CStarMatrix for principal-block functional
calculus. -/
noncomputable local instance instCStarAlgebraMatrixPrincipalBlock
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) :=
  inferInstanceAs (CStarAlgebra (CStarMatrix n n ℂ))

private local instance (n m : Type*) [Fintype n] [Fintype m] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ × Matrix m m ℂ) IsSelfAdjoint := by
  classical
  exact NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunctionalCalculus

/-- Continuous linear map sending a block matrix to its `₁₁` principal block. -/
noncomputable def toBlocks₁₁CLM (n m : Type*) [Fintype n] [Fintype m] :
    Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℂ] Matrix n n ℂ :=
  let L : Matrix (n ⊕ m) (n ⊕ m) ℂ →ₗ[ℂ] Matrix n n ℂ :=
      { toFun := Matrix.toBlocks₁₁
        map_add' := by
          intro A B
          ext i j
          rfl
        map_smul' := by
          intro c A
          ext i j
          rfl }
  { toLinearMap := L
    cont := by
      simpa [L] using L.continuous_of_finiteDimensional }

@[simp]
lemma toBlocks₁₁CLM_apply {n m : Type*} [Fintype n] [Fintype m]
      (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    toBlocks₁₁CLM n m M = M.toBlocks₁₁ :=
  rfl

@[simp]
lemma toBlocks₁₁_one {n m : Type*}
    [DecidableEq n] [DecidableEq m] :
    (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ).toBlocks₁₁ = (1 : Matrix n n ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.toBlocks₁₁]
  · simp [Matrix.toBlocks₁₁, hij]

@[simp]
lemma toBlocks₁₁_sub {n m : Type*} (A B : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ :=
  rfl

@[simp]
lemma toBlocks₁₁_real_smul {n m : Type*} (c : ℝ) (A : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ :=
  rfl

@[simp]
lemma toBlocks₁₁_neg {n m : Type*} (A : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (-A).toBlocks₁₁ = -A.toBlocks₁₁ :=
  rfl

lemma toBlocks₁₁_one_add_smul {n m : Type*}
    [DecidableEq n] [DecidableEq m] (t : ℝ) (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (1 + t • M).toBlocks₁₁ = 1 + t • M.toBlocks₁₁ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.toBlocks₁₁]
  · simp [Matrix.toBlocks₁₁, hij]

/-- The inverse of a positive-definite principal block is bounded by the
corresponding principal block of the full inverse. -/
lemma inv_toBlocks₁₁_le_toBlocks₁₁_inv {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosDef) :
    M.toBlocks₁₁⁻¹ ≤ (M⁻¹).toBlocks₁₁ := by
  let A : Matrix n n ℂ := M.toBlocks₁₁
  let B : Matrix n m ℂ := M.toBlocks₁₂
  let D : Matrix m m ℂ := M.toBlocks₂₂
  let S : Matrix m m ℂ := D - B.conjTranspose * A⁻¹ * B
  have hB : M.toBlocks₂₁ = B.conjTranspose := by
    ext i j
    have h := congr_fun (congr_fun hM.isHermitian.eq (Sum.inr i)) (Sum.inl j)
    simpa [A, B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply] using h.symm
  have hM_eq : M = Matrix.fromBlocks A B B.conjTranspose D := by
    rw [← Matrix.fromBlocks_toBlocks M, hB]
  have hA : A.PosDef := hM.submatrix Sum.inl_injective
  let : Invertible A := hA.isUnit.invertible
  let : Invertible M := hM.isUnit.invertible
  let : Invertible (Matrix.fromBlocks A B B.conjTranspose D) := by
    simpa [hM_eq] using (inferInstance : Invertible M)
  have hM_psd : (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef := by
    simpa [hM_eq] using hM.posSemidef
  have hS_psd : S.PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₁₁ (B := B) (D := D) hA).mp hM_psd
  let : Invertible (D - B.conjTranspose * ⅟A * B) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible A B B.conjTranspose D
  have hS_pd : S.PosDef := by
    refine hS_psd.posDef_iff_isUnit.mpr ?_
    simpa [S, invOf_eq_inv] using
      (show IsUnit (D - B.conjTranspose * ⅟A * B) from isUnit_of_invertible _)
  have htop :
      (M⁻¹).toBlocks₁₁ = A⁻¹ + A⁻¹ * B * S⁻¹ * B.conjTranspose * A⁻¹ := by
    rw [hM_eq]
    simpa [S, invOf_eq_inv] using
      congr_arg Matrix.toBlocks₁₁ (Matrix.invOf_fromBlocks₁₁_eq A B B.conjTranspose D)
  have hExtra_psd : (A⁻¹ * B * S⁻¹ * B.conjTranspose * A⁻¹).PosSemidef := by
    have hS_inv_psd : S⁻¹.PosSemidef := hS_pd.inv.posSemidef
    have hA_inv_herm : (A⁻¹).IsHermitian := hA.inv.isHermitian
    have hrewrite :
        A⁻¹ * B * S⁻¹ * B.conjTranspose * A⁻¹ =
          (A⁻¹ * B) * S⁻¹ * (A⁻¹ * B).conjTranspose := by
      simp [Matrix.mul_assoc, hA_inv_herm.eq]
    rw [hrewrite]
    exact hS_inv_psd.mul_mul_conjTranspose_same (A⁻¹ * B)
  have hExtra_nonneg :
      0 ≤ A⁻¹ * B * S⁻¹ * B.conjTranspose * A⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hExtra_psd
  calc
    M.toBlocks₁₁⁻¹ = A⁻¹ := by rfl
    _ ≤ A⁻¹ + A⁻¹ * B * S⁻¹ * B.conjTranspose * A⁻¹ := by
        simpa using add_le_add_left hExtra_nonneg A⁻¹
    _ = (M⁻¹).toBlocks₁₁ := htop.symm

lemma cfcₙ_one_sub_one_add_inv_real_eq {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : 0 ≤ A) :
    cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) A = 1 - (1 + A)⁻¹ := by
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  -- `1 + x > 0` on the nonnegative quasispectrum of `A`, so `(1 + x)⁻¹` is continuous there.
  have hne : ∀ x ∈ quasispectrum ℝ A, 1 + x ≠ 0 := fun x hx =>
    (add_pos_of_pos_of_nonneg one_pos (quasispectrum_nonneg_of_nonneg A hA x hx)).ne'
  have hne' : ∀ x ∈ spectrum ℝ A, 1 + x ≠ 0 := fun x hx =>
    hne x (spectrum_subset_quasispectrum ℝ A hx)
  have hcont : ContinuousOn (fun x : ℝ => 1 + x) (spectrum ℝ A) :=
    continuousOn_const.add continuousOn_id
  have hcontₙ : ContinuousOn (fun x : ℝ => 1 - (1 + x)⁻¹) (quasispectrum ℝ A) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).inv₀ hne)
  -- `cfc (1 + ·) A = 1 + A`.
  have hone_add : cfc (fun x : ℝ => 1 + x) A = 1 + A := by
    rw [cfc_const_add (1 : ℝ) (fun x => x) A continuousOn_id hA_sa, map_one, cfc_id' ℝ A hA_sa]
  -- `cfcₙ = cfc` (the function vanishes at `0`); split off the constant `1`, and invert
  -- `cfc (1 + ·) A = 1 + A` through `cfc_inv`.
  rw [cfcₙ_eq_cfc (f := fun x : ℝ => 1 - (1 + x)⁻¹) hcontₙ
      (show (1 : ℝ) - (1 + 0)⁻¹ = 0 by rw [add_zero, inv_one, sub_self]),
    cfc_sub (fun _ => (1 : ℝ)) (fun x => (1 + x)⁻¹) A continuousOn_const (hcont.inv₀ hne'),
    cfc_const_one ℝ A hA_sa, cfc_inv (fun x : ℝ => 1 + x) A hne' hcont hA_sa, hone_add,
    Matrix.nonsing_inv_eq_ringInverse]

lemma cfc_rpow_sub_one_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (p : ℝ) (hA : 0 ≤ A) (hp : 0 ≤ p) :
    cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) A = p⁻¹ • (A ^ p - 1) := by
  have hpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ A) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x hx
    exact Or.inr hp
  change cfc (fun x : ℝ => p⁻¹ • (x ^ p - 1)) A = p⁻¹ • (A ^ p - 1)
  rw [cfc_smul (s := p⁻¹) (f := fun x : ℝ => x ^ p - 1) (a := A) (hf := by
      exact hpow_cont.sub continuousOn_const),
    cfc_sub (a := A) (f := fun x : ℝ => x ^ p) (g := fun _ : ℝ => 1),
    CFC.rpow_eq_cfc_real (a := A) (y := p) hA,
    cfc_const_one (R := ℝ) A]

open scoped Classical in
private lemma fst_cfcₙ_nnrpow_prod {n m : Type*}
    [Fintype n] [Fintype m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} {N : Matrix n n ℂ} {q : NNReal}
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    (ContinuousLinearMap.fst ℂ (Matrix (n ⊕ m) (n ⊕ m) ℂ) (Matrix n n ℂ))
      (cfcₙ (fun x => NNReal.nnrpow x q) (M, N)) = M ^ q := by
  classical
  exact
    congrArg Prod.fst (CFC.nnrpow_map_prod hM hN)

open scoped Classical in
private lemma snd_cfcₙ_nnrpow_prod {n m : Type*}
    [Fintype n] [Fintype m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} {N : Matrix n n ℂ} {q : NNReal}
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    (ContinuousLinearMap.snd ℂ (Matrix (n ⊕ m) (n ⊕ m) ℂ) (Matrix n n ℂ))
      (cfcₙ (fun x => NNReal.nnrpow x q) (M, N)) = N ^ q := by
  classical
  exact
    congrArg Prod.snd (CFC.nnrpow_map_prod hM hN)

/-- The `rpow` integrand at scale `t` is a rescaled resolvent: for `X ≥ 0`,
`cfcₙ (rpowIntegrand₀₁ p t) X = t ^ (p - 1) • (1 - (1 + t⁻¹ • X)⁻¹)`. -/
private lemma cfcₙ_rpowIntegrand₀₁_eq_smul_one_sub_inv {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix k k ℂ} (hX : 0 ≤ X) {p t : ℝ} (hp : p ∈ Set.Ioo 0 1) (ht : 0 < t) :
    cfcₙ (Real.rpowIntegrand₀₁ p t) X = (t ^ (p - 1) : ℝ) • (1 - (1 + (t⁻¹ : ℝ) • X)⁻¹) := by
  have hfun : Real.rpowIntegrand₀₁ p 1 = fun x : ℝ => 1 - (1 + x)⁻¹ := by
    funext x; rw [Real.rpowIntegrand₀₁, Real.one_rpow, one_mul, inv_one]
  have hscale : cfcₙ (Real.rpowIntegrand₀₁ p t) X =
      t ^ (p - 1) • cfcₙ (Real.rpowIntegrand₀₁ p 1) ((t⁻¹ : ℝ) • X) :=
    CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht X hX
  rw [hscale, hfun,
    cfcₙ_one_sub_one_add_inv_real_eq (smul_nonneg (inv_nonneg.mpr ht.le) hX)]

open scoped Classical in
lemma toBlocks₁₁_cfcₙ_rpowIntegrand₀₁_le {n m : Type*}
    [Fintype n] [Fintype m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosDef) {p t : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (ht : 0 < t) :
    (cfcₙ (Real.rpowIntegrand₀₁ p t) M).toBlocks₁₁ ≤
      cfcₙ (Real.rpowIntegrand₀₁ p t) M.toBlocks₁₁ := by
  classical
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hM11_nonneg : 0 ≤ M.toBlocks₁₁ :=
    Matrix.nonneg_iff_posSemidef.mpr (hM.submatrix Sum.inl_injective).posSemidef
  have hShift_pd : (1 + (t⁻¹ : ℝ) • M).PosDef :=
    Matrix.PosDef.one.add_posSemidef (hM.smul (inv_pos.mpr ht)).posSemidef
  -- Principal-block inverse comparison for the shifted matrix `1 + t⁻¹ • M`.
  have hinv : (1 + (t⁻¹ : ℝ) • M.toBlocks₁₁)⁻¹ ≤ ((1 + (t⁻¹ : ℝ) • M)⁻¹).toBlocks₁₁ := by
    have h := inv_toBlocks₁₁_le_toBlocks₁₁_inv hShift_pd
    rwa [toBlocks₁₁_add, toBlocks₁₁_one, toBlocks₁₁_real_smul] at h
  -- Both sides are `t ^ (p - 1) • (1 - resolvent)`, and the resolvents are ordered by `hinv`.
  calc (cfcₙ (Real.rpowIntegrand₀₁ p t) M).toBlocks₁₁
      = (t ^ (p - 1) : ℝ) • (1 - ((1 + (t⁻¹ : ℝ) • M)⁻¹).toBlocks₁₁) := by
        rw [cfcₙ_rpowIntegrand₀₁_eq_smul_one_sub_inv hM_nonneg hp ht, toBlocks₁₁_real_smul,
          toBlocks₁₁_sub, toBlocks₁₁_one]
    _ ≤ (t ^ (p - 1) : ℝ) • (1 - (1 + (t⁻¹ : ℝ) • M.toBlocks₁₁)⁻¹) :=
        smul_le_smul_of_nonneg_left (sub_le_sub_left hinv 1) (Real.rpow_nonneg ht.le _)
    _ = cfcₙ (Real.rpowIntegrand₀₁ p t) M.toBlocks₁₁ :=
        (cfcₙ_rpowIntegrand₀₁_eq_smul_one_sub_inv hM11_nonneg hp ht).symm

/-- Principal-block operator-concavity for `rpow` on `Ioo (0 : ℝ) 1`. -/
lemma toBlocks₁₁_rpow_le_rpow_toBlocks₁₁ {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosDef) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (M ^ p).toBlocks₁₁ ≤ M.toBlocks₁₁ ^ p := by
  let q : NNReal := ⟨p, hp.1.le⟩
  have hq : q ∈ Set.Ioo (0 : NNReal) (1 : NNReal) := hp
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hM11_pd : M.toBlocks₁₁.PosDef := hM.submatrix Sum.inl_injective
  have hM11_nonneg : 0 ≤ M.toBlocks₁₁ := Matrix.nonneg_iff_posSemidef.mpr hM11_pd.posSemidef
  -- Löwner's integral representation in the product C⋆-algebra, at the pair `(M, M₁₁)`:
  -- `(M, M₁₁) ^ q = ∫_{t > 0} cfcₙ (rpowIntegrand₀₁ q t) (M, M₁₁) dμ`.
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (A := Matrix (n ⊕ m) (n ⊕ m) ℂ × Matrix n n ℂ) hq
  obtain ⟨hInt, hPow⟩ := hμ (M, M.toBlocks₁₁) ⟨hM_nonneg, hM11_nonneg⟩
  have hIntM := MeasureTheory.Integrable.fst hInt
  -- The two components of the representation: `M ^ q = ∫ (…).1` and `M₁₁ ^ q = ∫ (…).2`.
  have hPowFst := (fst_cfcₙ_nnrpow_prod (q := q) hM_nonneg hM11_nonneg).symm.trans
    ((congrArg Prod.fst hPow).trans (fst_integral hInt))
  have hPowSnd := (snd_cfcₙ_nnrpow_prod (q := q) hM_nonneg hM11_nonneg).symm.trans
    ((congrArg Prod.snd hPow).trans (snd_integral hInt))
  -- Integrate the pointwise comparison `toBlocks₁₁_cfcₙ_rpowIntegrand₀₁_le` over `t > 0`.
  let : OrderClosedTopology (Matrix n n ℂ) := CStarAlgebra.instOrderClosedTopology
  have hmono := MeasureTheory.integral_mono_ae ((toBlocks₁₁CLM n m).integrable_comp hIntM)
    (MeasureTheory.Integrable.snd hInt) <| by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have hf : ContinuousOn (Real.rpowIntegrand₀₁ q t)
          (quasispectrum ℝ M ∪ quasispectrum ℝ M.toBlocks₁₁) := by
        refine (Real.continuousOn_rpowIntegrand₀₁_Ici hp ht).mono ?_
        rintro x (hx | hx)
        · exact quasispectrum_nonneg_of_nonneg _ hM_nonneg _ hx
        · exact quasispectrum_nonneg_of_nonneg _ hM11_nonneg _ hx
      -- `cfcₙ f (M, M₁₁) = (cfcₙ f M, cfcₙ f M₁₁)`.
      have hprod : cfcₙ (Real.rpowIntegrand₀₁ q t) (M, M.toBlocks₁₁) =
          (cfcₙ (Real.rpowIntegrand₀₁ q t) M,
            cfcₙ (Real.rpowIntegrand₀₁ q t) M.toBlocks₁₁) :=
        cfcₙ_map_prod (S := ℝ) (Real.rpowIntegrand₀₁ q t) M M.toBlocks₁₁ hf
          (IsSelfAdjoint.of_nonneg (show 0 ≤ (M, M.toBlocks₁₁) from ⟨hM_nonneg, hM11_nonneg⟩))
          hM.isHermitian hM11_pd.isHermitian
      change (cfcₙ (Real.rpowIntegrand₀₁ q t) (M, M.toBlocks₁₁)).1.toBlocks₁₁ ≤
        (cfcₙ (Real.rpowIntegrand₀₁ q t) (M, M.toBlocks₁₁)).2
      rw [hprod]
      exact toBlocks₁₁_cfcₙ_rpowIntegrand₀₁_le hM hp ht
  calc (M ^ p).toBlocks₁₁
      = (M ^ q).toBlocks₁₁ := congrArg Matrix.toBlocks₁₁ (CFC.nnrpow_eq_rpow hq.1).symm
    _ = _ := congrArg Matrix.toBlocks₁₁ hPowFst
    _ = _ := ((toBlocks₁₁CLM n m).integral_comp_comm hIntM).symm
    _ ≤ _ := hmono
    _ = M.toBlocks₁₁ ^ q := hPowSnd.symm
    _ = M.toBlocks₁₁ ^ p := CFC.nnrpow_eq_rpow hq.1

/-- Principal-block operator-concavity for the logarithm on strictly positive matrices. -/
lemma toBlocks₁₁_log_le_log_toBlocks₁₁ {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosDef) :
    (CFC.log M).toBlocks₁₁ ≤ CFC.log M.toBlocks₁₁ := by
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hM11_pd : M.toBlocks₁₁.PosDef := hM.submatrix Sum.inl_injective
  have hM11_nonneg : 0 ≤ M.toBlocks₁₁ := Matrix.nonneg_iff_posSemidef.mpr hM11_pd.posSemidef
  have hTendM :
      Filter.Tendsto (fun p : ℝ => (p⁻¹ : ℝ) • (M ^ p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (CFC.log M)) := by
    have hEq :
        ∀ᶠ p : ℝ in 𝓝[>] 0,
          cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) M = (p⁻¹ : ℝ) • (M ^ p - 1) := by
      filter_upwards [nhdsGT_basis 0 |>.mem_of_mem zero_lt_one] with p hp
      simpa using cfc_rpow_sub_one_eq M p hM_nonneg hp.1.le
    exact Filter.Tendsto.congr' hEq
      (CFC.tendsto_cfc_rpow_sub_one_log (a := M) (ha := hM.isStrictlyPositive))
  have hTendM11 :
      Filter.Tendsto (fun p : ℝ => (p⁻¹ : ℝ) • (M.toBlocks₁₁ ^ p - 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (CFC.log M.toBlocks₁₁)) := by
    have hEq :
        ∀ᶠ p : ℝ in 𝓝[>] 0,
          cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) M.toBlocks₁₁ =
            (p⁻¹ : ℝ) • (M.toBlocks₁₁ ^ p - 1) := by
      filter_upwards [nhdsGT_basis 0 |>.mem_of_mem zero_lt_one] with p hp
      simpa using cfc_rpow_sub_one_eq M.toBlocks₁₁ p hM11_nonneg hp.1.le
    exact Filter.Tendsto.congr' hEq
      (CFC.tendsto_cfc_rpow_sub_one_log (a := M.toBlocks₁₁) (ha := hM11_pd.isStrictlyPositive))
  have hTendBlock :
      Filter.Tendsto (fun p : ℝ => (p⁻¹ : ℝ) • ((M ^ p).toBlocks₁₁ - 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((CFC.log M).toBlocks₁₁)) := by
    have hTmp :
        Filter.Tendsto
          (fun p : ℝ => (toBlocks₁₁CLM n m) ((p⁻¹ : ℝ) • (M ^ p - 1)))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((CFC.log M).toBlocks₁₁)) :=
      ((toBlocks₁₁CLM n m).continuous.tendsto _).comp hTendM
    simpa [toBlocks₁₁CLM_apply, sub_eq_add_neg] using hTmp
  have hEventually :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (p⁻¹ : ℝ) • ((M ^ p).toBlocks₁₁ - 1) ≤
          (p⁻¹ : ℝ) • (M.toBlocks₁₁ ^ p - 1) := by
    filter_upwards [nhdsGT_basis 0 |>.mem_of_mem zero_lt_one] with p hp
    have hpow :
        (M ^ p).toBlocks₁₁ ≤ M.toBlocks₁₁ ^ p := by
      exact toBlocks₁₁_rpow_le_rpow_toBlocks₁₁ hM hp
    have hsub : (M ^ p).toBlocks₁₁ - 1 ≤ M.toBlocks₁₁ ^ p - 1 := sub_le_sub_right hpow 1
    have hpinv : 0 ≤ (p⁻¹ : ℝ) := by exact inv_nonneg.mpr hp.1.le
    exact smul_le_smul_of_nonneg_left hsub hpinv
  let : OrderClosedTopology (Matrix n n ℂ) := CStarAlgebra.instOrderClosedTopology
  exact le_of_tendsto_of_tendsto hTendBlock hTendM11 hEventually

end Matrix
