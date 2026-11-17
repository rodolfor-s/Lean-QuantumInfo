import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The kernel isometry of a Hermitian matrix, and the kernel completion of a partial isometry

For a Hermitian `M : Matrix (Fin d) (Fin d) ℂ` let `zeroEigCount M` be the multiplicity of the
eigenvalue `0` — the dimension of `ker M`.  `Matrix.kerComplIso M` is the explicit
`d × zeroEigCount M` matrix whose columns are the eigenvalue-`0` eigenvectors of `M`, enumerated
by the canonical order isomorphism of the zero-eigenvalue index set. This noncomputable formula
uses Mathlib's chosen orthonormal eigenbasis; the resulting basis is not basis-choice-independent.

The two structural facts are:

* `Matrix.kerComplIso_conjTranspose_mul_self` — the columns are orthonormal, `Cᴴ C = 1`;
* `Matrix.kerComplIso_mul_conjTranspose` — for a Hermitian **idempotent** `M`, the columns span
  exactly `ker M`, so `C Cᴴ = 1 − M` is the complementary projector.

For projectors this makes `kerComplIso` an explicit orthonormal basis of the kernel, and
`Matrix.zeroEigCount_eq_sub_trace` the usual co-rank count `dim ker M = d − tr M`.

## The explicit isometric extension

`Matrix.exists_isometric_extension_of_partialIsometry` (`PartialIsometryExtension.lean`) and
`Quantum.Metrics.TraceNormHoelder.partialIsometry_extend_isometry` both assert *existence* of a
full isometry extending a partial isometry.  The second half of this file gives the same object as
a **function** of the input,

```
partialIsometryExtend V₀ := V₀  +  C_{V₀V₀ᴴ} · E · (C_{V₀ᴴV₀})ᴴ ,
```

where `E` is the zero-padded identity `Fin (dim ker V₀ᴴV₀) ↪ Fin (dim ker V₀V₀ᴴ)`, available
because `q ≤ p` forces `dim ker (V₀ᴴV₀) ≤ dim ker (V₀V₀ᴴ)`
(`zeroEigCount_conjTranspose_mul_self_le`, a
co-rank count through `zeroEigCount_eq_sub_trace` and `tr (V₀ᴴV₀) = tr (V₀V₀ᴴ)`).  The added term
maps `ker (V₀ᴴV₀)` isometrically into `ker (V₀V₀ᴴ)` and is orthogonal to `V₀` on both sides, which
is exactly what makes the sum a full isometry agreeing with `V₀` on its initial support.

`exists_isometric_extension_partialIsometryExtend` records that this matrix realizes the
existential statement; this file is a leaf, so adding it does not change the import graph of the
existing extension theorem or of its many consumers.

## Main definitions

* `Matrix.zeroEigCount`, `Matrix.kerComplIso`, `Matrix.partialIsometryExtend`

## Main statements

* `Matrix.kerComplIso_conjTranspose_mul_self`, `Matrix.kerComplIso_mul_conjTranspose`,
  `Matrix.kerComplIso_left_annihilate`, `Matrix.zeroEigCount_eq_sub_trace`;
* `Matrix.partialIsometryExtend_conjTranspose_mul_self`, `Matrix.partialIsometryExtend_mul_proj`,
  `Matrix.exists_isometric_extension_partialIsometryExtend`.
-/

open scoped ComplexOrder

noncomputable section

namespace Matrix

variable {d : ℕ}

/-- The multiplicity of the eigenvalue `0` of a Hermitian matrix — the dimension of its kernel,
and its co-rank when it is idempotent. -/
def zeroEigCount (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) : ℕ :=
  (Finset.univ.filter (fun i => hM.eigenvalues i = 0)).card

/-- **The explicit isometry onto `ker M`** for a Hermitian `M`: its columns are the eigenvectors
of `M` with eigenvalue `0`, enumerated by the canonical order isomorphism of the zero-eigenvalue
index set. It is a submatrix of Mathlib's eigenvector unitary and depends on that chosen
orthonormal eigenbasis. -/
def kerComplIso (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) :
    Matrix (Fin d) (Fin (zeroEigCount M hM)) ℂ :=
  Matrix.of fun a j =>
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) a
      (((Finset.univ.filter (fun i => hM.eigenvalues i = 0)).orderIsoOfFin
        (rfl : _ = zeroEigCount M hM) j : Fin d))

/-- `kerComplIso` has orthonormal columns: `Cᴴ C = 1`. They are distinct columns of a unitary
matrix. -/
theorem kerComplIso_conjTranspose_mul_self (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) :
    (kerComplIso M hM)ᴴ * kerComplIso M hM = 1 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set g := (Finset.univ.filter (fun i => hM.eigenvalues i = 0)).orderIsoOfFin
    (rfl : _ = zeroEigCount M hM) with hg
  have hC : kerComplIso M hM =
      Matrix.of (fun (a : Fin d) (j : Fin (zeroEigCount M hM)) => U a (g j : Fin d)) := rfl
  have hUU : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rw [← hU, Matrix.star_eq_conjTranspose] at h; exact h
  ext i j
  have h1 : ((kerComplIso M hM)ᴴ * kerComplIso M hM) i j
      = (Uᴴ * U) ((g i : Fin d)) ((g j : Fin d)) := by
    rw [hC]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [h1, hUU]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne, Matrix.one_apply_ne h]
    intro hc
    exact h (g.injective (Subtype.coe_injective hc))

section Idempotent

variable {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) (hidem : M * M = M)
include hM hidem

/-- The eigenvalues of a Hermitian idempotent are `0` or `1`. -/
lemma eigenvalues_eq_zero_or_one (i : Fin d) : hM.eigenvalues i = 0 ∨ hM.eigenvalues i = 1 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) with hD
  have hSpec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpec
  have hUstarU : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rw [← hU, Matrix.star_eq_conjTranspose] at h; exact h
  have h_spec' : M = U * D * Uᴴ := by simpa [hU, hD, Matrix.star_eq_conjTranspose] using hSpec
  have hD_idem : D * D = D := by
    calc D * D
        = (Uᴴ * U) * D * ((Uᴴ * U) * D) * (Uᴴ * U) := by
          rw [hUstarU]; simp only [Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (U * D * Uᴴ) * (U * D * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * (M * M) * U := by rw [← h_spec']; simp only [Matrix.mul_assoc]
      _ = Uᴴ * (U * D * Uᴴ) * U := by rw [hidem, h_spec']
      _ = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [hUstarU]; simp only [Matrix.one_mul, Matrix.mul_one]
  have h := Matrix.ext_iff.mpr hD_idem i i
  rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  simp only [Function.comp_apply] at h
  have h_real : hM.eigenvalues i * hM.eigenvalues i = hM.eigenvalues i := by exact_mod_cast h
  have h_factor : hM.eigenvalues i * (hM.eigenvalues i - 1) = 0 := by nlinarith [h_real]
  rcases mul_eq_zero.mp h_factor with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

/-- **For a Hermitian idempotent, `kerComplIso` projects onto the kernel:** `C Cᴴ = 1 − M`. The
eigenvalues are `0` or `1` (`eigenvalues_eq_zero_or_one`), so the zero-eigenvalue columns of the
eigenvector unitary assemble exactly the complementary spectral projector. -/
theorem kerComplIso_mul_conjTranspose :
    kerComplIso M hM * (kerComplIso M hM)ᴴ = 1 - M := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  have hSpec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpec
  set D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) with hD
  set g := (Finset.univ.filter (fun i => hM.eigenvalues i = 0)).orderIsoOfFin
    (rfl : _ = zeroEigCount M hM) with hg
  have hC : kerComplIso M hM =
      Matrix.of (fun (a : Fin d) (j : Fin (zeroEigCount M hM)) => U a (g j : Fin d)) := rfl
  have hUstarU : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rw [← hU, Matrix.star_eq_conjTranspose] at h; exact h
  have hU_r : U * Uᴴ = 1 := mul_eq_one_comm.mpr hUstarU
  have h_spec' : M = U * D * Uᴴ := by simpa [hU, hD, Matrix.star_eq_conjTranspose] using hSpec
  have entry : ∀ (v : Fin d → ℂ) (a b : Fin d),
      (U * Matrix.diagonal v * Uᴴ) a b = ∑ i, U a i * v i * star (U b i) := by
    intro v a b
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have h_comp : (1 : Matrix (Fin d) (Fin d) ℂ) - M
      = U * Matrix.diagonal (fun i => 1 - ((RCLike.ofReal ∘ hM.eigenvalues) i : ℂ)) * Uᴴ := by
    calc (1 : Matrix (Fin d) (Fin d) ℂ) - M
        = U * 1 * Uᴴ - U * D * Uᴴ := by rw [Matrix.mul_one, hU_r, ← h_spec']
      _ = U * (1 - D) * Uᴴ := by rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = U * Matrix.diagonal (fun i => 1 - ((RCLike.ofReal ∘ hM.eigenvalues) i : ℂ)) * Uᴴ := by
          rw [hD, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  ext a b
  rw [h_comp, entry]
  have lhs_eq : (kerComplIso M hM * (kerComplIso M hM)ᴴ) a b
      = ∑ j : Fin (zeroEigCount M hM), U a ((g j : Fin d)) * star (U b ((g j : Fin d))) := by
    rw [hC]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [lhs_eq]
  have lhs_eq2 : ∑ j : Fin (zeroEigCount M hM), U a ((g j : Fin d)) * star (U b ((g j : Fin d)))
      = ∑ i ∈ (Finset.univ.filter (fun i => hM.eigenvalues i = 0)), U a i * star (U b i) := by
    rw [← Finset.sum_coe_sort (Finset.univ.filter (fun i => hM.eigenvalues i = 0))
      (fun i => U a i * star (U b i))]
    exact Fintype.sum_equiv g.toEquiv _ _ (fun j => rfl)
  rw [lhs_eq2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eigenvalues_eq_zero_or_one hM hidem i with h | h
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right (by rw [h]; norm_num)]; simp [h]

/-- For a Hermitian idempotent, `kerComplIso` lands in the kernel: `M · C = 0`. -/
theorem kerComplIso_left_annihilate : M * kerComplIso M hM = 0 := by
  have h1 : (1 - M) * kerComplIso M hM = kerComplIso M hM := by
    rw [← kerComplIso_mul_conjTranspose hM hidem, Matrix.mul_assoc,
      kerComplIso_conjTranspose_mul_self, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul] at h1
  exact sub_eq_self.mp h1

/-- **Co-rank identity** `dim ker M = d − tr M` for a Hermitian idempotent: its eigenvalues are
`0` or `1`, so the trace counts the ones and `zeroEigCount` counts the zeros. -/
theorem zeroEigCount_eq_sub_trace : (zeroEigCount M hM : ℝ) = d - M.trace.re := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) with hD
  have hSpec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpec
  have hUstarU : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rw [← hU, Matrix.star_eq_conjTranspose] at h; exact h
  have h_spec' : M = U * D * Uᴴ := by simpa [hU, hD, Matrix.star_eq_conjTranspose] using hSpec
  have htrace : M.trace = ∑ i, ((hM.eigenvalues i : ℝ) : ℂ) := by
    calc M.trace = (U * D * Uᴴ).trace := by rw [← h_spec']
      _ = (Uᴴ * U * D).trace := by rw [Matrix.trace_mul_cycle]
      _ = D.trace := by rw [hUstarU, Matrix.one_mul]
      _ = ∑ i, ((hM.eigenvalues i : ℝ) : ℂ) := by rw [hD, Matrix.trace_diagonal]; rfl
  have htr_re : M.trace.re = ∑ i, hM.eigenvalues i := by
    rw [htrace, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hsum : ∑ i, hM.eigenvalues i
      = ((Finset.univ.filter (fun i => ¬ hM.eigenvalues i = 0)).card : ℝ) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eigenvalues_eq_zero_or_one hM hidem i with h | h
    · simp [h]
    · rw [h]; norm_num
  have hcards : zeroEigCount M hM
      + (Finset.univ.filter (fun i => ¬ hM.eigenvalues i = 0)).card = d := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d))) (p := fun i => hM.eigenvalues i = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hcards' : (zeroEigCount M hM : ℝ)
      + ((Finset.univ.filter (fun i => ¬ hM.eigenvalues i = 0)).card : ℝ) = (d : ℝ) := by
    exact_mod_cast hcards
  rw [htr_re, hsum]; linarith

end Idempotent

/-!
## The explicit kernel completion of a partial isometry
-/

variable {p q : ℕ}

/-- A partial isometry absorbs its initial support projector: `V₀ (V₀ᴴ V₀) = V₀`. This is the
converse of `partialIsometry_proj_idem_of_absorb`, so the two hypotheses `(V₀ᴴV₀)² = V₀ᴴV₀` and
`V₀ V₀ᴴ V₀ = V₀` used in the library are equivalent. -/
theorem partialIsometry_absorb (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) :
    V₀ * (V₀ᴴ * V₀) = V₀ := by
  set P := V₀ᴴ * V₀ with hP
  have hPh : P.IsHermitian := isHermitian_conjTranspose_mul_self V₀
  have hexp : (V₀ * P - V₀)ᴴ * (V₀ * P - V₀) = P * P * P - P * P - P * P + P := by
    have hct : (V₀ * P - V₀)ᴴ = P * V₀ᴴ - V₀ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPh.eq]
    rw [hct, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have e1 : P * V₀ᴴ * (V₀ * P) = P * P * P := by rw [hP]; simp only [Matrix.mul_assoc]
    have e2 : P * V₀ᴴ * V₀ = P * P := by rw [hP]; simp only [Matrix.mul_assoc]
    have e3 : V₀ᴴ * (V₀ * P) = P * P := by rw [hP]; simp only [Matrix.mul_assoc]
    rw [e1, e2, e3, ← hP]; abel
  have h0 : (V₀ * P - V₀)ᴴ * (V₀ * P - V₀) = 0 := by rw [hexp, hproj, hproj]; abel
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp h0)

/-- The initial support projector of a partial isometry is idempotent: from `V₀ V₀ᴴ V₀ = V₀`,
`(V₀ᴴ V₀)² = V₀ᴴ (V₀ V₀ᴴ V₀) = V₀ᴴ V₀`. -/
theorem partialIsometry_proj_idem_of_absorb (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hV : V₀ * V₀ᴴ * V₀ = V₀) :
    (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀ := by
  calc (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * (V₀ * V₀ᴴ * V₀) := by simp only [Matrix.mul_assoc]
    _ = V₀ᴴ * V₀ := by rw [hV]

/-- The final support projector `V₀ V₀ᴴ` of a partial isometry is idempotent. -/
theorem partialIsometry_final_idem (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) :
    (V₀ * V₀ᴴ) * (V₀ * V₀ᴴ) = V₀ * V₀ᴴ := by
  calc (V₀ * V₀ᴴ) * (V₀ * V₀ᴴ) = V₀ * (V₀ᴴ * V₀) * V₀ᴴ := by simp only [Matrix.mul_assoc]
    _ = V₀ * V₀ᴴ := by rw [partialIsometry_absorb V₀ hproj]

/-- The zero-padded identity embedding `Fin kP ↪ Fin kQ` (`kP ≤ kQ`) has orthonormal columns. -/
theorem castLE_indicator_isometry {kP kQ : ℕ} (h : kP ≤ kQ) :
    (Matrix.of (fun (a : Fin kQ) (b : Fin kP) => if a = Fin.castLE h b then (1 : ℂ) else 0))ᴴ *
        (Matrix.of (fun (a : Fin kQ) (b : Fin kP) =>
          if a = Fin.castLE h b then (1 : ℂ) else 0)) = 1 := by
  ext i j
  have h1 : ((Matrix.of
        (fun (a : Fin kQ) (b : Fin kP) => if a = Fin.castLE h b then (1 : ℂ) else 0))ᴴ *
      (Matrix.of (fun (a : Fin kQ) (b : Fin kP) =>
        if a = Fin.castLE h b then (1 : ℂ) else 0))) i j
      = ∑ a, (if a = Fin.castLE h i then (1 : ℂ) else 0) *
          (if a = Fin.castLE h j then (1 : ℂ) else 0) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (starRingEnd ℂ)]
  rw [h1]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (Fin.castLE h i)
    (fun a => if a = Fin.castLE h j then (1 : ℂ) else 0)]
  simp [Matrix.one_apply, Fin.castLE_inj]

/-- **The co-rank order of the two support projectors**, from `q ≤ p`:
`dim ker (V₀ᴴ V₀) ≤ dim ker (V₀ V₀ᴴ)`. The two projectors have equal trace
(`Matrix.trace_mul_comm`) and live on spaces of dimension `q ≤ p`, so `zeroEigCount_eq_sub_trace`
gives the inequality. -/
theorem zeroEigCount_conjTranspose_mul_self_le (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) (hdim : q ≤ p) :
    zeroEigCount (V₀ᴴ * V₀) (isHermitian_conjTranspose_mul_self V₀) ≤
      zeroEigCount (V₀ * V₀ᴴ) (isHermitian_mul_conjTranspose_self V₀) := by
  set P := V₀ᴴ * V₀ with hP
  set Q := V₀ * V₀ᴴ with hQ
  have hPh : P.IsHermitian := isHermitian_conjTranspose_mul_self V₀
  have hQh : Q.IsHermitian := isHermitian_mul_conjTranspose_self V₀
  have hQ_idem : Q * Q = Q := partialIsometry_final_idem V₀ hproj
  have htr : P.trace = Q.trace := by rw [hP, hQ]; exact Matrix.trace_mul_comm V₀ᴴ V₀
  have hP' : (zeroEigCount P hPh : ℝ) = q - P.trace.re := zeroEigCount_eq_sub_trace hPh hproj
  have hQ' : (zeroEigCount Q hQh : ℝ) = p - Q.trace.re := zeroEigCount_eq_sub_trace hQh hQ_idem
  have h : (zeroEigCount P hPh : ℝ) ≤ (zeroEigCount Q hQh : ℝ) := by
    rw [hP', hQ', htr]
    have hqp : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hdim
    linarith
  exact_mod_cast h

/-- **The explicit isometric extension of a partial isometry.** `V₀` plus the spectral
kernel completion `C_{V₀V₀ᴴ} · E · (C_{V₀ᴴV₀})ᴴ`; see the module docstring. Its two defining
properties are `partialIsometryExtend_conjTranspose_mul_self` and
`partialIsometryExtend_mul_proj`. -/
def partialIsometryExtend (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) (hdim : q ≤ p) :
    Matrix (Fin p) (Fin q) ℂ :=
  V₀ +
    kerComplIso (V₀ * V₀ᴴ) (isHermitian_mul_conjTranspose_self V₀) *
      (Matrix.of fun a b =>
        if a = Fin.castLE (zeroEigCount_conjTranspose_mul_self_le V₀ hproj hdim) b then (1 : ℂ)
          else 0) *
      (kerComplIso (V₀ᴴ * V₀) (isHermitian_conjTranspose_mul_self V₀))ᴴ

/-- Generic algebraic assembly: `V₀` plus a kernel completion `W = DQ · E · Cᴴ` is a full isometry
extending `V₀`, given the spectral properties of the three pieces. The cross terms `V₀ᴴ W` and
`Wᴴ V₀` vanish because `W` lands in `ker (V₀V₀ᴴ)`, and `W P = 0` because `W` starts from
`ker (V₀ᴴV₀)`. -/
private theorem partialIsometry_assembly {kP kQ : ℕ} (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin kP) ℂ) (DQ : Matrix (Fin p) (Fin kQ) ℂ)
    (E : Matrix (Fin kQ) (Fin kP) ℂ)
    (hCCH : C * Cᴴ = 1 - V₀ᴴ * V₀) (hDD : DQᴴ * DQ = 1) (hDDH : DQ * DQᴴ = 1 - V₀ * V₀ᴴ)
    (hEE : Eᴴ * E = 1) (hV₀P : V₀ * (V₀ᴴ * V₀) = V₀)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) :
    (V₀ + DQ * E * Cᴴ)ᴴ * (V₀ + DQ * E * Cᴴ) = 1 ∧
      (V₀ + DQ * E * Cᴴ) * (V₀ᴴ * V₀) = V₀ := by
  set P := V₀ᴴ * V₀ with hP
  set Q := V₀ * V₀ᴴ with hQ
  set W := DQ * E * Cᴴ with hW
  have hPh : P.IsHermitian := isHermitian_conjTranspose_mul_self V₀
  have hWW : Wᴴ * W = 1 - P := by
    calc Wᴴ * W = C * Eᴴ * (DQᴴ * DQ) * E * Cᴴ := by
          rw [hW]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = C * (Eᴴ * E) * Cᴴ := by rw [hDD]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = C * Cᴴ := by rw [hEE, Matrix.mul_one]
      _ = 1 - P := hCCH
  have hQD : Q * DQ = 0 := by
    have h1 : (1 - Q) * DQ = DQ := by rw [← hDDH, Matrix.mul_assoc, hDD, Matrix.mul_one]
    rw [Matrix.sub_mul, Matrix.one_mul] at h1
    exact sub_eq_self.mp h1
  have hQW : Q * W = 0 := by
    rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQD, Matrix.zero_mul, Matrix.zero_mul]
  have hV₀HW : V₀ᴴ * W = 0 := by
    have hV₀Q : V₀ᴴ * Q = V₀ᴴ := by
      calc V₀ᴴ * Q = (V₀ᴴ * V₀) * V₀ᴴ := by rw [hQ]; simp only [Matrix.mul_assoc]
        _ = (V₀ * P)ᴴ := by rw [Matrix.conjTranspose_mul, hPh.eq]
        _ = V₀ᴴ := by rw [hV₀P]
    calc V₀ᴴ * W = (V₀ᴴ * Q) * W := by rw [hV₀Q]
      _ = V₀ᴴ * (Q * W) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQW, Matrix.mul_zero]
  have hWV₀ : Wᴴ * V₀ = 0 := by
    have h := congrArg Matrix.conjTranspose hV₀HW
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
    exact h
  have hWP : W * P = 0 := by
    have h0 : (W * P)ᴴ * (W * P) = 0 := by
      calc (W * P)ᴴ * (W * P) = P * (Wᴴ * W) * P := by
            rw [Matrix.conjTranspose_mul, hPh.eq]
            simp only [Matrix.mul_assoc]
        _ = P * (1 - P) * P := by rw [hWW]
        _ = (P - P * P) * P := by rw [Matrix.mul_sub, Matrix.mul_one]
        _ = 0 := by rw [hproj, sub_self, Matrix.zero_mul]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h0
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hV₀HW, hWV₀, hWW, ← hP]
    abel
  · rw [Matrix.add_mul, hV₀P, hWP, add_zero]

/-- **The explicit extension is a full isometry:** `Wᴴ W = 1`. -/
theorem partialIsometryExtend_conjTranspose_mul_self (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) (hdim : q ≤ p) :
    (partialIsometryExtend V₀ hproj hdim)ᴴ * partialIsometryExtend V₀ hproj hdim = 1 := by
  rw [partialIsometryExtend]
  exact (partialIsometry_assembly V₀ _ _ _
    (kerComplIso_mul_conjTranspose (isHermitian_conjTranspose_mul_self V₀) hproj)
    (kerComplIso_conjTranspose_mul_self (V₀ * V₀ᴴ) (isHermitian_mul_conjTranspose_self V₀))
    (kerComplIso_mul_conjTranspose (isHermitian_mul_conjTranspose_self V₀)
      (partialIsometry_final_idem V₀ hproj))
    (castLE_indicator_isometry (zeroEigCount_conjTranspose_mul_self_le V₀ hproj hdim))
    (partialIsometry_absorb V₀ hproj) hproj).1

/-- **The explicit extension agrees with `V₀` on its initial support:** `W (V₀ᴴ V₀) = V₀`. -/
theorem partialIsometryExtend_mul_proj (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀) (hdim : q ≤ p) :
    partialIsometryExtend V₀ hproj hdim * (V₀ᴴ * V₀) = V₀ := by
  rw [partialIsometryExtend]
  exact (partialIsometry_assembly V₀ _ _ _
    (kerComplIso_mul_conjTranspose (isHermitian_conjTranspose_mul_self V₀) hproj)
    (kerComplIso_conjTranspose_mul_self (V₀ * V₀ᴴ) (isHermitian_mul_conjTranspose_self V₀))
    (kerComplIso_mul_conjTranspose (isHermitian_mul_conjTranspose_self V₀)
      (partialIsometry_final_idem V₀ hproj))
    (castLE_indicator_isometry (zeroEigCount_conjTranspose_mul_self_le V₀ hproj hdim))
    (partialIsometry_absorb V₀ hproj) hproj).2

/-- **The existential extension theorem is realized by the explicit matrix.** Same hypotheses as
`Matrix.exists_isometric_extension_of_partialIsometry` (`PartialIsometryExtension.lean`), with the
witness named. -/
theorem exists_isometric_extension_partialIsometryExtend
    (V₀ : Matrix (Fin p) (Fin q) ℂ) (hV : V₀ * V₀ᴴ * V₀ = V₀) (hdim : q ≤ p) :
    ∃ W : Matrix (Fin p) (Fin q) ℂ,
      W = partialIsometryExtend V₀ (partialIsometry_proj_idem_of_absorb V₀ hV) hdim ∧
      Wᴴ * W = (1 : Matrix (Fin q) (Fin q) ℂ) ∧ W * (V₀ᴴ * V₀) = V₀ :=
  ⟨_, rfl,
    partialIsometryExtend_conjTranspose_mul_self V₀ (partialIsometry_proj_idem_of_absorb V₀ hV)
      hdim,
    partialIsometryExtend_mul_proj V₀ (partialIsometry_proj_idem_of_absorb V₀ hV) hdim⟩

end Matrix

end -- noncomputable section
