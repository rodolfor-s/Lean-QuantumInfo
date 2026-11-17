import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# CFC spectral helpers: simultaneous diagonalization of commuting PSD matrices

General operator-algebra facts about the continuous functional calculus
(`cfc`, and the real power `· ^ (· : ℝ)` = `CFC.rpow`) on Hermitian / PSD matrices,
isolated from the Renner-specific tail file. Two layers:

* **Abstract spectral resolution.** For a Hermitian `A = Σ_z λ_z • P_z` over *any*
  family of mutually orthogonal Hermitian idempotents `{P_z}` summing to `1` (not
  necessarily Mathlib's canonical eigenbasis), `cfc` acts coefficientwise:
  `cfc f A = Σ_z f(λ_z) • P_z` (`cfc_of_orthogonalResolution`), and likewise for the
  real power (`rpow_of_orthogonalResolution`). Proven by Lagrange interpolation
  through `cfc_polynomial` and `aeval_of_orthogonalResolution`.

* **Simultaneous diagonalization.** For commuting PSD matrices `c, d`, the real power
  is multiplicative, `(c · d) ^ y = c ^ y · d ^ y` (`matrix_rpow_mul_of_commute`).
  The proof builds the joint indicator spectral resolution `{Q_l · R_m}` over the
  finite eigenvalue pairs `(l, m) ∈ spectrum c × spectrum d` — where `Q_l = cfc 1_{l} c`,
  `R_m = cfc 1_{m} d` (`specProj`) are commuting Hermitian idempotents — and evaluates
  all three powers `c^y`, `d^y`, `(c·d)^y` coefficientwise on the shared family,
  recombining via `(l·m)^y = l^y · m^y`.

The simultaneous-diagonalization core is the spectral content not in Mathlib (which
only offers `cfc_mul` for two functions of the *same* element) behind
the commuting-operator power identity, hence behind the tensor-power
factorization of Renner's tilted collision MGF; `rpow_of_orthogonalResolution` also
serves the witness-eigenbasis evaluation in `IIDChernoffTail.lean`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Math.SpectralTheory.CfcSpectral

/-- **Power of an orthogonal-projector spectral resolution.** If `A = Σ_z λ_z • P_z`
for mutually orthogonal idempotents `{P_z}` summing to `1`, then
`A ^ k = Σ_z λ_z ^ k • P_z`. Proven by induction on `k` using orthogonality
(`P_z P_w = δ_{zw} P_z`). -/
lemma pow_of_orthogonalResolution {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
    (A : Matrix n n ℂ) (lam : ι → ℂ)
    (P : ι → Matrix n n ℂ)
    (hidem : ∀ z, P z * P z = P z)
    (horth : ∀ z w, z ≠ w → P z * P w = 0)
    (hsum : ∑ z, P z = 1)
    (hA : A = ∑ z, lam z • P z) (k : ℕ) :
    A ^ k = ∑ z, lam z ^ k • P z := by
  classical
  -- the resolution is multiplicatively diagonal: `(Σ λ_z P_z)(Σ μ_w P_w) = Σ λ_z μ_z P_z`
  have hmul_diag : ∀ (c d : ι → ℂ),
      (∑ z, c z • P z) * (∑ w, d w • P w) = ∑ z, (c z * d z) • P z := by
    intro c d
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.sum_eq_single z]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hidem z, smul_smul]
    · intro w _ hw
      rw [Matrix.smul_mul, Matrix.mul_smul, horth z w (Ne.symm hw), smul_zero, smul_zero]
    · intro hz; exact absurd (Finset.mem_univ z) hz
  induction k with
  | zero =>
      simp only [pow_zero]
      rw [← hsum]
      exact Finset.sum_congr rfl (fun z _ => by rw [one_smul])
  | succ j ih =>
      rw [pow_succ, ih, hA, hmul_diag]
      exact Finset.sum_congr rfl (fun z _ => by rw [pow_succ])

/-- **Polynomial application to an orthogonal-projector spectral resolution.** With
`A = Σ_z λ_z • P_z` (orthogonal idempotents summing to `1`), polynomial application
is coefficientwise: `aeval A q = Σ_z (algebraMap ℝ ℂ) (q.eval λ_z) • P_z`. Extends
`pow_of_orthogonalResolution` from monomials to all polynomials by linearity. -/
lemma aeval_of_orthogonalResolution {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
    (A : Matrix n n ℂ) (lam : ι → ℝ)
    (P : ι → Matrix n n ℂ)
    (hidem : ∀ z, P z * P z = P z)
    (horth : ∀ z w, z ≠ w → P z * P w = 0)
    (hsum : ∑ z, P z = 1)
    (hA : A = ∑ z, (lam z : ℂ) • P z) (q : Polynomial ℝ) :
    (Polynomial.aeval A) q
      = ∑ z, ((algebraMap ℝ ℂ) (q.eval (lam z))) • P z := by
  classical
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hp, hr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Polynomial.eval_add, map_add, add_smul]
  | monomial k c =>
      have hpow : A ^ k = ∑ z, (lam z : ℂ) ^ k • P z :=
        pow_of_orthogonalResolution A (fun z => (lam z : ℂ)) P hidem horth hsum hA k
      rw [Polynomial.aeval_monomial, hpow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Polynomial.eval_monomial, map_mul, map_pow,
        show (algebraMap ℝ (Matrix n n ℂ)) c = ((algebraMap ℝ ℂ) c) • 1 by
          rw [Algebra.algebraMap_eq_smul_one]; norm_cast,
        smul_mul_assoc, one_mul, smul_smul]
      simp only [Complex.coe_algebraMap]

/-- **CFC of an abstract orthogonal-projector spectral resolution** (lemma (b)).
If a Hermitian operator `A` decomposes as `A = Σ_z λ_z • P_z` over a family of
mutually orthogonal Hermitian idempotents `{P_z}` (`P_z² = P_z`, `P_z P_w = 0` for
`z ≠ w`, `Σ_z P_z = 1`) — not necessarily Mathlib's canonical eigenbasis — then
the continuous functional calculus acts coefficientwise:

  `cfc f A = Σ_z f(λ_z) • P_z`.

This is the spectral-resolution form of the matrix CFC. The continuous `f` agrees
on the finite spectrum `spectrum ℝ A` with a Lagrange-interpolating polynomial `q`
(`cfc_congr`); the CFC of a polynomial is honest polynomial application
(`cfc_polynomial`), which is coefficientwise on the resolution
(`aeval_of_orthogonalResolution`); and `q.eval λ_z = f λ_z` on the spectrum, while
off-spectrum labels `λ_z` carry a zero projector `P_z` (so the coefficient is
irrelevant). -/
lemma cfc_of_orthogonalResolution {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
    (A : Matrix n n ℂ) (lam : ι → ℝ)
    (P : ι → Matrix n n ℂ)
    (hHerm : ∀ z, (P z).IsHermitian)
    (hidem : ∀ z, P z * P z = P z)
    (horth : ∀ z w, z ≠ w → P z * P w = 0)
    (hsum : ∑ z, P z = 1)
    (hA : A = ∑ z, (lam z : ℂ) • P z)
    (f : ℝ → ℝ) :
    cfc f A = ∑ z, (f (lam z) : ℂ) • P z := by
  classical
  -- `A` is Hermitian/self-adjoint (a real combination of Hermitian idempotents).
  have hAherm : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hA, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.conjTranspose_smul, (hHerm z).eq, Complex.star_def, Complex.conj_ofReal]
  have hAsa : IsSelfAdjoint A := hAherm
  -- Lagrange-interpolating polynomial agreeing with `f` on the (finite) real spectrum.
  set s : Finset ℝ := (Matrix.finite_real_spectrum (A := A)).toFinset with hs
  set q : Polynomial ℝ := (Lagrange.interpolate s id) f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) ↑s := Set.injOn_id _
  have hspec : ∀ μ ∈ spectrum ℝ A, Polynomial.eval μ q = f μ := by
    intro μ hμ
    have hμs : μ ∈ s := by rw [hs, Set.Finite.mem_toFinset]; exact hμ
    have := Lagrange.eval_interpolate_at_node (s := s) (v := (id : ℝ → ℝ)) f hInj hμs
    exact this
  -- `cfc f A = aeval A q` (agree on spectrum, then `cfc` of a polynomial is `aeval`).
  have hcfc_eq : cfc f A = (Polynomial.aeval A) q := by
    rw [← cfc_polynomial (R := ℝ) q A]
    exact cfc_congr (fun μ hμ => (hspec μ hμ).symm)
  rw [hcfc_eq, aeval_of_orthogonalResolution A lam P hidem horth hsum hA q]
  -- coefficientwise: on-spectrum `λ_z` gives `q.eval λ_z = f λ_z`; off-spectrum `P_z = 0`.
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hPz : P z = 0
  · rw [hPz, smul_zero, smul_zero]
  · -- `A` acts on the projector `P_z` by `λ_z` (orthogonality): `A · P_z = λ_z • P_z`.
    have hAP : A * P z = (lam z : ℂ) • P z := by
      rw [hA, Finset.sum_mul]
      rw [Finset.sum_eq_single z]
      · rw [Matrix.smul_mul, hidem z]
      · intro w _ hwz
        rw [Matrix.smul_mul, horth w z hwz, smul_zero]
      · intro hz; exact absurd (Finset.mem_univ z) hz
    -- hence `(algebraMap ℝ ℂ λ_z • 1 − A) · P_z = 0`; since `P_z ≠ 0`, `λ_z ∈ spectrum`.
    have hmem : lam z ∈ spectrum ℝ A := by
      rw [spectrum.mem_iff]
      intro hunit
      apply hPz
      have he : (algebraMap ℝ (Matrix n n ℂ)) (lam z) = (lam z : ℂ) • 1 := by
        rw [Algebra.algebraMap_eq_smul_one]; norm_cast
      have hkey : ((algebraMap ℝ (Matrix n n ℂ)) (lam z) - A) * P z = 0 := by
        rw [he, Matrix.sub_mul, hAP, smul_mul_assoc, one_mul, sub_self]
      obtain ⟨u, hu⟩ := hunit
      calc P z
          = (↑u⁻¹ : Matrix n n ℂ)
              * (((algebraMap ℝ (Matrix n n ℂ)) (lam z) - A) * P z) := by
            rw [← mul_assoc, ← hu, Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [hkey, Matrix.mul_zero]
    rw [hspec (lam z) hmem, Complex.coe_algebraMap]

/-- **CFC real power of an abstract orthogonal-projector spectral resolution.** For
a positive-semidefinite `A = Σ_z λ_z • P_z` over mutually orthogonal Hermitian
idempotents `{P_z}` summing to `1`, the continuous-functional-calculus real power
acts coefficientwise:

  `A ^ y = Σ_z (λ_z ^ y) • P_z`  (`λ_z ^ y = Real.rpow λ_z y`).

Specialization of `cfc_of_orthogonalResolution` to `f = (· ^ y)` via
`CFC.rpow_eq_cfc_real`. This is the spectral-resolution evaluation of the tilted
operator powers `R ^ (1+s)`, `τ ^ (−s)` over the witness eigenbasis / reference
increments in Renner's collision-trace identity. -/
lemma rpow_of_orthogonalResolution {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
    (A : Matrix n n ℂ) (lam : ι → ℝ)
    (P : ι → Matrix n n ℂ)
    (hA_nonneg : 0 ≤ A)
    (hHerm : ∀ z, (P z).IsHermitian)
    (hidem : ∀ z, P z * P z = P z)
    (horth : ∀ z w, z ≠ w → P z * P w = 0)
    (hsum : ∑ z, P z = 1)
    (hA : A = ∑ z, (lam z : ℂ) • P z)
    (y : ℝ) :
    A ^ y = ∑ z, ((lam z ^ y : ℝ) : ℂ) • P z := by
  rw [CFC.rpow_eq_cfc_real hA_nonneg]
  exact cfc_of_orthogonalResolution A lam P hHerm hidem horth hsum hA (fun x => x ^ y)

/-- **Indicator spectral projector** of a Hermitian matrix at a real value `l`:
`Q_l = cfc 1_{l} c`, the orthogonal projection onto the `l`-eigenspace of `c` (zero
if `l` is not an eigenvalue). A Hermitian idempotent that is a `cfc`-function of `c`,
hence commutes with everything commuting with `c`. -/
def specProj {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (l : ℝ) : Matrix n n ℂ :=
  cfc (Set.indicator ({l} : Set ℝ) (fun _ => (1 : ℝ))) c

/-- The (finite) real spectrum of a matrix as a `Finset ℝ`. -/
def specFinset {n : Type*} [Fintype n] [DecidableEq n] (c : Matrix n n ℂ) : Finset ℝ :=
  (Matrix.finite_real_spectrum (A := c)).toFinset

lemma mem_specFinset {n : Type*} [Fintype n] [DecidableEq n]
    {c : Matrix n n ℂ} {l : ℝ} :
    l ∈ specFinset c ↔ l ∈ spectrum ℝ c := by
  rw [specFinset, Set.Finite.mem_toFinset]

lemma isHermitian_specProj {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (l : ℝ) :
    (specProj c l).IsHermitian :=
  IsSelfAdjoint.cfc

lemma continuousOn_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (g : ℝ → ℝ) :
    ContinuousOn g (spectrum ℝ c) :=
  (Matrix.finite_real_spectrum (A := c)).continuousOn g

/-- Indicator spectral projectors at distinct eigenvalues are orthogonal:
`Q_l · Q_l' = 0` for `l ≠ l'` (the indicators have disjoint support). -/
lemma specProj_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) {l l' : ℝ}
    (h : l ≠ l') : specProj c l * specProj c l' = 0 := by
  rw [specProj, specProj, ← cfc_mul _ _ c (continuousOn_spectrum c _) (continuousOn_spectrum c _),
    show (fun x => Set.indicator ({l} : Set ℝ) (fun _ => (1:ℝ)) x
            * Set.indicator ({l'} : Set ℝ) (fun _ => (1:ℝ)) x)
          = (fun _ => (0:ℝ)) from ?_, cfc_const_zero]
  funext x
  by_cases hx1 : x = l <;> by_cases hx2 : x = l' <;> simp_all [Set.indicator]

/-- Indicator spectral projectors are idempotent: `Q_l · Q_l = Q_l`. -/
lemma specProj_idem {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (l : ℝ) :
    specProj c l * specProj c l = specProj c l := by
  rw [specProj, ← cfc_mul _ _ c (continuousOn_spectrum c _) (continuousOn_spectrum c _)]
  apply cfc_congr
  intro x _
  by_cases hx : x = l <;> simp [Set.indicator, hx]

/-- Completeness of the indicator spectral projectors: `Σ_{l ∈ spectrum} Q_l = 1`. -/
lemma sum_specProj {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (hc : IsSelfAdjoint c) :
    ∑ l ∈ specFinset c, specProj c l = (1 : Matrix n n ℂ) := by
  simp only [specProj]
  rw [← cfc_sum (s := specFinset c) _ c (fun l _ => continuousOn_spectrum c _),
    ← cfc_one (R := ℝ) c]
  apply cfc_congr
  intro x hx
  have hx' : x ∈ specFinset c := mem_specFinset.mpr hx
  simp only [Finset.sum_apply, Pi.one_apply, Set.indicator_apply, Set.mem_singleton_iff]
  rw [Finset.sum_ite_eq (specFinset c) x (fun _ => (1:ℝ))]
  simp [hx']

/-- Spectral decomposition through the indicator projectors: `c = Σ_{l} l • Q_l`. -/
lemma eq_sum_specProj {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (hc : IsSelfAdjoint c) :
    c = ∑ l ∈ specFinset c, (l : ℂ) • specProj c l := by
  simp only [specProj]
  conv_lhs => rw [← cfc_id ℝ c]
  rw [show ∑ l ∈ specFinset c,
          (l : ℂ) • cfc (Set.indicator ({l} : Set ℝ) (fun _ => (1:ℝ))) c
        = ∑ l ∈ specFinset c,
          cfc (fun x => l * Set.indicator ({l} : Set ℝ) (fun _ => (1:ℝ)) x) c from ?_]
  · rw [← cfc_sum (s := specFinset c) _ c (fun l _ => continuousOn_spectrum c _)]
    apply cfc_congr
    intro x hx
    have hx' : x ∈ specFinset c := mem_specFinset.mpr hx
    simp only [id_eq, Finset.sum_apply, Set.indicator_apply, Set.mem_singleton_iff, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq (specFinset c) x (fun l => l)]
    simp [hx']
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [cfc_const_mul (l : ℝ) _ c (continuousOn_spectrum c _)]
    norm_cast

/-- A `cfc`-function projector of `c` commutes with any `b` that commutes with `c`. -/
lemma specProj_commute {n : Type*} [Fintype n] [DecidableEq n]
    (c b : Matrix n n ℂ) (l : ℝ)
    (hcb : Commute c b) : Commute (specProj c l) b :=
  Commute.cfc_real hcb _

/-- **Real power is multiplicative across a commuting Hermitian/PSD matrix pair**
(the matrix simultaneous-diagonalization core). For commuting Hermitian `c, d` with
`c, d ≥ 0`, the CFC real power distributes: `(c · d) ^ y = c ^ y · d ^ y`.

The honest proof builds the *joint* spectral resolution `{Q_l · R_m}` over the
finite eigenvalue pairs `(l, m) ∈ spectrum c × spectrum d`, where `Q_l = cfc 1_{l} c`
and `R_m = cfc 1_{m} d` are the indicator spectral projectors. These commute
(`specProj_commute`, since each is a `cfc`-function of one factor and the factors
commute), so each `P_{l,m} = Q_l R_m` is a Hermitian idempotent, the family is
mutually orthogonal and sums to `1`, and

  `c = Σ_{l,m} l • P_{l,m}`,  `d = Σ_{l,m} m • P_{l,m}`,  `c d = Σ_{l,m} (l·m) • P_{l,m}`.

`rpow_of_orthogonalResolution` then evaluates all three real powers coefficientwise
on the shared family, and `(l·m)^y = l^y · m^y` (`Real.mul_rpow`, nonneg eigenvalues)
recombines them into `c^y · d^y`. -/
lemma matrix_rpow_mul_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    (c d : Matrix n n ℂ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : Commute c d) (y : ℝ) :
    (c * d) ^ y = c ^ y * d ^ y := by
  classical
  have hcsa : IsSelfAdjoint c := (Matrix.nonneg_iff_posSemidef.mp hc).isHermitian
  have hdsa : IsSelfAdjoint d := (Matrix.nonneg_iff_posSemidef.mp hd).isHermitian
  -- eigenvalues are nonnegative on the (real) spectra of PSD matrices
  have hc_eig_nn : ∀ l ∈ specFinset c, 0 ≤ l := fun l hl =>
    spectrum_nonneg_of_nonneg hc (mem_specFinset.mp hl)
  have hd_eig_nn : ∀ m ∈ specFinset d, 0 ≤ m := fun m hm =>
    spectrum_nonneg_of_nonneg hd (mem_specFinset.mp hm)
  -- index the joint family by the product Finset as a `Fintype` subtype, with the
  -- coordinate eigenvalues `a`, `b` and the joint projectors `P` as plain functions.
  let S : Finset (ℝ × ℝ) := specFinset c ×ˢ specFinset d
  let a : ↥S → ℝ := fun lm => (lm : ℝ × ℝ).1
  let b : ↥S → ℝ := fun lm => (lm : ℝ × ℝ).2
  let P : ↥S → Matrix n n ℂ := fun lm => specProj c (lm : ℝ × ℝ).1 * specProj d (lm : ℝ × ℝ).2
  have haS : ∀ lm : ↥S, a lm ∈ specFinset c := fun lm => (Finset.mem_product.mp lm.2).1
  have hbS : ∀ lm : ↥S, b lm ∈ specFinset d := fun lm => (Finset.mem_product.mp lm.2).2
  -- the projectors `Q_l` and `R_m` commute (cfc of commuting factors)
  have hQR_comm : ∀ (l m : ℝ), Commute (specProj c l) (specProj d m) := fun l m =>
    specProj_commute c (specProj d m) l (specProj_commute d c m hcd.symm).symm
  -- joint projectors are Hermitian
  have hP_herm : ∀ lm : ↥S, (P lm).IsHermitian := by
    intro lm
    change (specProj c (a lm) * specProj d (b lm)).IsHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      (isHermitian_specProj d (b lm)).eq, (isHermitian_specProj c (a lm)).eq,
      (hQR_comm (a lm) (b lm))]
  -- joint projectors are idempotent: `(Q R)(Q R) = Q (R Q) R = Q (Q R) R = Q² R²`
  have hP_idem : ∀ lm : ↥S, P lm * P lm = P lm := by
    intro lm
    change specProj c (a lm) * specProj d (b lm) * (specProj c (a lm) * specProj d (b lm))
        = specProj c (a lm) * specProj d (b lm)
    rw [mul_assoc, ← mul_assoc (specProj d (b lm)), ← (hQR_comm (a lm) (b lm)),
      mul_assoc, specProj_idem, ← mul_assoc, specProj_idem]
  -- joint projectors are mutually orthogonal
  have hP_orth : ∀ lm lm' : ↥S, lm ≠ lm' → P lm * P lm' = 0 := by
    intro lm lm' hne
    have hne' : a lm ≠ a lm' ∨ b lm ≠ b lm' := by
      by_contra hcon
      push Not at hcon
      exact hne (Subtype.ext (Prod.ext hcon.1 hcon.2))
    change specProj c (a lm) * specProj d (b lm) * (specProj c (a lm') * specProj d (b lm')) = 0
    -- reorder to `(Q_l Q_l') (R_m R_m')` using commutation, then one factor vanishes
    rw [mul_assoc, ← mul_assoc (specProj d (b lm)), ← (hQR_comm (a lm') (b lm)),
      mul_assoc, ← mul_assoc (specProj c (a lm))]
    rcases hne' with hl | hm
    · rw [specProj_orthogonal c hl, Matrix.zero_mul]
    · rw [specProj_orthogonal d hm, Matrix.mul_zero]
  -- joint projectors sum to 1: `Σ_{l,m} Q_l R_m = (Σ_l Q_l)(Σ_m R_m) = 1·1`
  have hP_sum : ∑ lm : ↥S, P lm = 1 := by
    have hconv : (∑ lm : ↥S, P lm) = ∑ x ∈ S, (specProj c x.1 * specProj d x.2) := by
      rw [← Finset.sum_attach S (fun x => specProj c x.1 * specProj d x.2)]; rfl
    rw [hconv, Finset.sum_product,
      show (∑ l ∈ specFinset c, ∑ m ∈ specFinset d, specProj c l * specProj d m)
          = (∑ l ∈ specFinset c, specProj c l) * (∑ m ∈ specFinset d, specProj d m) by
        rw [Finset.sum_mul_sum],
      sum_specProj c hcsa, sum_specProj d hdsa, mul_one]
  -- spectral decompositions of `c`, `d`, `c*d` over the shared family
  have hc_decomp : c = ∑ lm : ↥S, (a lm : ℂ) • P lm := by
    have hconv : (∑ lm : ↥S, (a lm : ℂ) • P lm)
        = ∑ x ∈ S, (x.1 : ℂ) • (specProj c x.1 * specProj d x.2) := by
      rw [← Finset.sum_attach S (fun x => (x.1 : ℂ) • (specProj c x.1 * specProj d x.2))]; rfl
    rw [hconv, Finset.sum_product,
      show (∑ l ∈ specFinset c, ∑ m ∈ specFinset d, (l : ℂ) • (specProj c l * specProj d m))
          = ∑ l ∈ specFinset c, (l : ℂ) • (specProj c l * ∑ m ∈ specFinset d, specProj d m) by
        exact Finset.sum_congr rfl (fun l _ => by rw [Finset.mul_sum, Finset.smul_sum]),
      sum_specProj d hdsa]
    simp only [mul_one]
    exact eq_sum_specProj c hcsa
  have hd_decomp : d = ∑ lm : ↥S, (b lm : ℂ) • P lm := by
    have hconv : (∑ lm : ↥S, (b lm : ℂ) • P lm)
        = ∑ x ∈ S, (x.2 : ℂ) • (specProj c x.1 * specProj d x.2) := by
      rw [← Finset.sum_attach S (fun x => (x.2 : ℂ) • (specProj c x.1 * specProj d x.2))]; rfl
    rw [hconv, Finset.sum_product,
      show (∑ l ∈ specFinset c, ∑ m ∈ specFinset d, (m : ℂ) • (specProj c l * specProj d m))
          = ∑ m ∈ specFinset d, (m : ℂ) • ((∑ l ∈ specFinset c, specProj c l) * specProj d m) by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_mul, Finset.smul_sum]),
      sum_specProj c hcsa]
    simp only [one_mul]
    exact eq_sum_specProj d hdsa
  -- the product of two resolutions over the shared family collapses onto the diagonal
  have hmul_diag : ∀ (u v : ↥S → ℝ),
      (∑ lm : ↥S, (u lm : ℂ) • P lm) * (∑ lm : ↥S, (v lm : ℂ) • P lm)
        = ∑ lm : ↥S, ((u lm * v lm : ℝ) : ℂ) • P lm := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun lm _ => ?_)
    rw [Finset.sum_eq_single lm]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hP_idem, smul_smul]; push_cast; ring_nf
    · intro lm' _ hlm'
      rw [Matrix.smul_mul, Matrix.mul_smul, hP_orth lm lm' hlm'.symm, smul_zero, smul_zero]
    · intro hcon; exact absurd (Finset.mem_univ lm) hcon
  have hcd_decomp : c * d = ∑ lm : ↥S, ((a lm * b lm : ℝ) : ℂ) • P lm := by
    conv_lhs => rw [hc_decomp, hd_decomp]
    exact hmul_diag a b
  have hcd_nonneg : 0 ≤ c * d := hcd.mul_nonneg hc hd
  -- evaluate all three real powers coefficientwise and recombine
  rw [rpow_of_orthogonalResolution (c * d) (fun lm => a lm * b lm) P hcd_nonneg
      hP_herm hP_idem hP_orth hP_sum hcd_decomp y,
    rpow_of_orthogonalResolution c a P hc hP_herm hP_idem hP_orth hP_sum hc_decomp y,
    rpow_of_orthogonalResolution d b P hd hP_herm hP_idem hP_orth hP_sum hd_decomp y,
    hmul_diag (fun lm => a lm ^ y) (fun lm => b lm ^ y)]
  -- `(l·m)^y = l^y · m^y` coefficientwise (nonnegative eigenvalues)
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  rw [Real.mul_rpow (hc_eig_nn (a lm) (haS lm)) (hd_eig_nn (b lm) (hbS lm))]

end Math.SpectralTheory.CfcSpectral

end
