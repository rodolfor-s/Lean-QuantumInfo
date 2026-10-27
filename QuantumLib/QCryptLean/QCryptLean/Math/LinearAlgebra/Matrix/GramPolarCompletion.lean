import Mathlib.LinearAlgebra.Matrix.PosDef
import QCryptLean.Math.LinearAlgebra.Matrix.HermitianPinv

/-!
# A spectral-gauge polar completion for matrices with equal Gram

Uhlmann-type arguments repeatedly need the following linear-algebra step.  Two square matrices `A`
and `B` have the same left Gram matrix, `A · Aᴴ = B · B` with `B` positive semidefinite (so
`B = √(A · Aᴴ)`); produce a **co-isometry** `Y` that intertwines them, `A · Y = B` and
`Y · Yᴴ = 1`.

The pseudoinverse term `Aᴴ · B⁺` gives the map on the support of `B`; the remaining kernel map
depends on a choice of gauge. `Matrix.gramPolarCompletion` uses the spectral gauge:

```
gramPolarCompletion A B  :=  Aᴴ · B⁺  +  W_{AᴴA} · D₀ · W_{BᴴB}ᴴ ,
```

where `B⁺` is `Matrix.hermitianPinv` (`HermitianPinv.lean`), `W_H` is Mathlib's eigenvector
unitary `Matrix.IsHermitian.eigenvectorUnitary` and `D₀` is the `0/1` diagonal supported on the
zero-eigenvalue indices of `AᴴA`.  Under the Gram hypothesis the two antitone-sorted eigenvalue
functions of `AᴴA` and `BᴴB` agree (`Matrix.charpoly_mul_comm` together with
`Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`), so the connector is a partial isometry from
`ker (BᴴB)` onto `ker (AᴴA)`, orthogonal on both sides to the pseudoinverse part. The two pieces
are complementary projectors and add to `1`.

This is a noncomputable matrix formula using Mathlib's chosen orthonormal eigenbases, not a
choice-free or basis-canonical completion. Its proved intertwining and co-isometry laws are the
properties used downstream.

## Main definitions

* `Matrix.gramPolarCompletion`

## Main statements

* `Matrix.gramPolarCompletion_transfer` — `A · Y = B`;
* `Matrix.gramPolarCompletion_mul_conjTranspose` — `Y · Yᴴ = 1`;
* `Matrix.exists_coisometry_of_gram_eq` — the resulting existence statement, with `Y` explicit.
-/

open scoped ComplexOrder

noncomputable section

namespace Matrix

variable {m : ℕ}

/-- **The explicit Uhlmann/polar gauge completion.** For square matrices `A`, `B` with equal left
Gram `A · Aᴴ = B · B` (`B` positive semidefinite, so `B = √(A·Aᴴ)`), the matrix

`Y := Aᴴ · B⁺ + W_{AᴴA} · D₀ · W_{BᴴB}ᴴ`

satisfying `A · Y = B` (`gramPolarCompletion_transfer`) and `Y · Yᴴ = 1`
(`gramPolarCompletion_mul_conjTranspose`). The first summand is the canonical pseudoinverse
partial isometry, the second the spectral kernel connector; see the module docstring. -/
def gramPolarCompletion (A B : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Aᴴ * hermitianPinv B +
    ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary :
        Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (fun i =>
        if (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i = 0
        then (1 : ℂ) else 0) *
      ((Matrix.posSemidef_conjTranspose_mul_self B).isHermitian.eigenvectorUnitary :
        Matrix (Fin m) (Fin m) ℂ)ᴴ

/-- **The range of `A` is annihilated on the kernel selector.** `A · W_{AᴴA} · D₀ = 0`, where
`W_{AᴴA}` is the eigenvector unitary of `AᴴA` and `D₀` selects the zero-eigenvalue columns.
Proof: `(A W D₀)ᴴ (A W D₀) = D₀ (Wᴴ (AᴴA) W) D₀ = D₀ · diag(eig) · D₀ = 0` by the spectral
diagonalization, since `D₀` is supported exactly on the zero eigenvalues; then apply
`Matrix.conjTranspose_mul_self_eq_zero`. -/
lemma mul_eigenvectorUnitary_zeroSelector_eq_zero (A : Matrix (Fin m) (Fin m) ℂ)
    (hH : (Aᴴ * A).IsHermitian) :
    A * (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (fun i => if hH.eigenvalues i = 0 then (1 : ℂ) else 0) = 0 := by
  refine Matrix.conjTranspose_mul_self_eq_zero.mp ?_
  set Wv : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
    with hWvdef
  set D₀ : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => if hH.eigenvalues i = 0 then (1 : ℂ) else 0) with hD₀def
  have hdiag : Wvᴴ * (Aᴴ * A) * Wv = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have h := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] at h
    rw [← hWvdef] at h
    exact h
  have hexp : (A * Wv * D₀)ᴴ * (A * Wv * D₀) = D₀ᴴ * (Wvᴴ * (Aᴴ * A) * Wv) * D₀ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hexp, hdiag, hD₀def, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.star_apply]
  by_cases h : hH.eigenvalues i = 0 <;> simp [h]

/-- **The zero-eigenvalue connector square is the kernel projector**, as a `cfc`:
`W · D₀ · Wᴴ = cfc 1_{=0} H`, for the eigenvector unitary `W` and the `0/1` zero-eigenvalue
selector `D₀` of a Hermitian `H`. Immediate from the spectral form `cfc_eq_conj_diagonal`. -/
lemma eigenvectorUnitary_zeroSelector_conj {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal (fun i => if hH.eigenvalues i = 0 then (1 : ℂ) else 0) *
        (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ =
      cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) H := by
  have hfun : (fun i => if hH.eigenvalues i = 0 then (1 : ℂ) else 0)
      = (RCLike.ofReal ∘ (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) ∘ hH.eigenvalues) := by
    funext i
    simp only [Function.comp_apply]
    by_cases h : hH.eigenvalues i = 0 <;> simp [h]
  rw [cfc_eq_conj_diagonal hH, hfun]

/-- **Transfer identity of the polar completion** (first defining property): for `B` positive
semidefinite with `A · Aᴴ = B · B`,

`A · gramPolarCompletion A B = B` .

`A · Aᴴ · B⁺ = B · B · B⁺ = B` by the kernel-safe cancellation `mul_self_mul_hermitianPinv`, and
the connector term is annihilated by `mul_eigenvectorUnitary_zeroSelector_eq_zero`. -/
theorem gramPolarCompletion_transfer (A B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.PosSemidef) (hGram : A * Aᴴ = B * B) :
    A * gramPolarCompletion A B = B := by
  have hterm2 := mul_eigenvectorUnitary_zeroSelector_eq_zero A
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  unfold gramPolarCompletion
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hGram, mul_self_mul_hermitianPinv hB.isHermitian,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hterm2, Matrix.zero_mul, add_zero]

/-- **Co-isometry certificate of the polar completion** (second defining property): for `B`
positive semidefinite with `A · Aᴴ = B · B`,

`gramPolarCompletion A B · (gramPolarCompletion A B)ᴴ = 1` .

Expand `Yᴴ · Y` into four terms. `Aᴴ · B⁺ · B⁺ · A = Aᴴ · (A·Aᴴ)⁺ · A` is the support projection of
`AᴴA` (`hermitianPinv_mul_sq_mul_hermitianPinv` through `hGram`); the connector square
`W_{AᴴA} · D₀ · D₀ᴴ · W_{AᴴA}ᴴ` is the complementary kernel projection
(`eigenvectorUnitary_zeroSelector_conj`, using `W_{BᴴB}ᴴ · W_{BᴴB} = 1`); the cross terms vanish
because `B⁺` annihilates the zero-eigenvalue columns of `W_{BᴴB}`. The eigenvalue matching
`eig(AᴴA) = eig(BᴴB)` (`Matrix.charpoly_mul_comm` through `hGram` and `Bᴴ = B`, then
`Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`) is what aligns `D₀` with `ker(BᴴB)`. The two
projections sum to `1`. -/
theorem gramPolarCompletion_mul_conjTranspose (A B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.PosSemidef) (hGram : A * Aᴴ = B * B) :
    gramPolarCompletion A B * (gramPolarCompletion A B)ᴴ = 1 := by
  unfold gramPolarCompletion
  rw [mul_eq_one_comm]
  set hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian with hAAdef
  set hBB := (Matrix.posSemidef_conjTranspose_mul_self B).isHermitian with hBBdef
  have hpinvsa : (hermitianPinv B)ᴴ = hermitianPinv B := isHermitian_hermitianPinv B
  have hDsa : (Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0))ᴴ
      = Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : hAA.eigenvalues i = 0 <;> simp [h]
  have heig : hAA.eigenvalues = hBB.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, Matrix.charpoly_mul_comm Aᴴ A, hGram,
      hB.isHermitian]
  have hanniA : A * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
      * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0) = 0 :=
    mul_eigenvectorUnitary_zeroSelector_eq_zero A hAA
  have hanniAdag : Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
      * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * Aᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hanniA
    simpa [Matrix.conjTranspose_mul, hDsa, Matrix.mul_assoc] using h
  have hWAu : (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
      * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hDidem : Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
      * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
      = Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : hAA.eigenvalues i = 0 <;> simp [h]
  have hYdag : (Aᴴ * hermitianPinv B
        + (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)ᴴ
      = hermitianPinv B * A
        + (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hpinvsa, hDsa, Matrix.mul_assoc]
  have hT1 : hermitianPinv B * A * (Aᴴ * hermitianPinv B)
      = cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Bᴴ * B) := by
    rw [show hermitianPinv B * A * (Aᴴ * hermitianPinv B)
        = hermitianPinv B * (A * Aᴴ) * hermitianPinv B from by simp only [Matrix.mul_assoc],
      hGram, hermitianPinv_mul_sq_mul_hermitianPinv hB.isHermitian, hB.isHermitian]
  have hT2 : hermitianPinv B * A
      * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ) = 0 := by
    rw [show hermitianPinv B * A
          * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
        = hermitianPinv B
          * (A * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0))
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ from by
        simp only [Matrix.mul_assoc], hanniA, Matrix.mul_zero, Matrix.zero_mul]
  have hT3 : (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
        * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
        * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * (Aᴴ * hermitianPinv B) = 0 := by
    rw [show (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * (Aᴴ * hermitianPinv B)
        = (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * (Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * Aᴴ)
          * hermitianPinv B from by simp only [Matrix.mul_assoc], hanniAdag, Matrix.mul_zero,
      Matrix.zero_mul]
  have hT4 : (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
        * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
        * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
      * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
      = cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (Bᴴ * B) := by
    rw [show (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
        * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
        = (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
            * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ))
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ from by
        simp only [Matrix.mul_assoc], hWAu, Matrix.mul_one]
    rw [show (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
        = (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * (Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0))
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ from by
        simp only [Matrix.mul_assoc], hDidem,
      show Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          = Matrix.diagonal (fun i => if hBB.eigenvalues i = 0 then (1 : ℂ) else 0) from by
        rw [heig],
      eigenvectorUnitary_zeroSelector_conj hBB]
  have hBBsa : IsSelfAdjoint (Bᴴ * B) := Matrix.isHermitian_iff_isSelfAdjoint.mp hBB
  have hsum : cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (Bᴴ * B)
      + cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (Bᴴ * B) = 1 := by
    rw [← cfc_add (Bᴴ * B) (fun x => if x = 0 then (0 : ℝ) else 1)
      (fun x => if x = 0 then (1 : ℝ) else 0) (continuousOn_real_spectrum _ _)
      (continuousOn_real_spectrum _ _),
      show (fun x : ℝ => (if x = 0 then (0 : ℝ) else 1) + (if x = 0 then (1 : ℝ) else 0))
        = (fun _ : ℝ => (1 : ℝ)) from by funext x; by_cases hx : x = 0 <;> simp [hx],
      cfc_const_one ℝ (Bᴴ * B) hBBsa]
  rw [hYdag]
  have hexpand : (hermitianPinv B * A
        + (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
      * (Aᴴ * hermitianPinv B
        + (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
          * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
          * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
      = hermitianPinv B * A * (Aᴴ * hermitianPinv B)
        + hermitianPinv B * A
          * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ)
        + (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * (Aᴴ * hermitianPinv B)
        + (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ
          * ((hAA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
            * Matrix.diagonal (fun i => if hAA.eigenvalues i = 0 then (1 : ℂ) else 0)
            * (hBB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ) := by
    noncomm_ring
  rw [hexpand, hT1, hT2, hT3, hT4]
  simp only [add_zero]
  exact hsum

/-- **Existence of an intertwining co-isometry, with explicit witness.** For `B` positive
semidefinite with `A · Aᴴ = B · B` there is a `Y` with `A · Y = B` and `Y · Yᴴ = 1`; the witness is
`gramPolarCompletion A B`, with the spectral gauge described above. -/
theorem exists_coisometry_of_gram_eq (A B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.PosSemidef) (hGram : A * Aᴴ = B * B) :
    ∃ Y : Matrix (Fin m) (Fin m) ℂ, Y = gramPolarCompletion A B ∧ A * Y = B ∧ Y * Yᴴ = 1 :=
  ⟨gramPolarCompletion A B, rfl, gramPolarCompletion_transfer A B hB hGram,
    gramPolarCompletion_mul_conjTranspose A B hB hGram⟩

end Matrix

end -- noncomputable section
