import QCryptLean.Math.SpectralTheory.Matrix

/-! # Diagonal forms of orthogonal projections -/

noncomputable section
namespace Matrix

/-- An orthogonal projection is unitarily conjugate to the diagonal indicator of a
finite set of basis vectors. -/
theorem IsHermitian.exists_unitary_diagonal_indicator {X : Type*} [Fintype X]
    [DecidableEq X] (P : Matrix X X ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) :
    ∃ (U : Matrix.unitaryGroup (X) ℂ) (s : Finset (X)),
      P = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) *
        (U : Matrix X X ℂ)ᴴ := by
  classical
  let U := hP.eigenvectorUnitary
  let D : Matrix X X ℂ := Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
  have hspec : P = (U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ := by
    exact hP.spectral_theorem
  have hU : (U : Matrix X X ℂ)ᴴ * (U : Matrix X X ℂ) = 1 := Unitary.coe_star_mul_self U
  have hU' : (U : Matrix X X ℂ) * (U : Matrix X X ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hD : (U : Matrix X X ℂ)ᴴ * P * (U : Matrix X X ℂ) = D := by
    conv_lhs => rw [hspec]
    simp only [mul_assoc, hU, mul_one]
    rw [← mul_assoc, hU, one_mul]
  have hDD : D * D = D := by
    rw [← hD]
    calc (U : Matrix X X ℂ)ᴴ * P * (U : Matrix X X ℂ) *
        ((U : Matrix X X ℂ)ᴴ * P * (U : Matrix X X ℂ))
        = (U : Matrix X X ℂ)ᴴ *
          (P * ((U : Matrix X X ℂ) * (U : Matrix X X ℂ)ᴴ) * P) * (U : Matrix X X ℂ) := by
            simp only [mul_assoc]
      _ = (U : Matrix X X ℂ)ᴴ * P * (U : Matrix X X ℂ) := by
        rw [hU', mul_one, hPP]
  have hentry : ∀ i, (hP.eigenvalues i : ℂ) = 0 ∨ (hP.eigenvalues i : ℂ) = 1 := by
    intro i
    have hi := congr_fun₂ hDD i i
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal] at hi
    have hz : (hP.eigenvalues i : ℂ) * ((hP.eigenvalues i : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, hi, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  refine ⟨U, Finset.univ.filter (fun i => (hP.eigenvalues i : ℂ) = 1), ?_⟩
  refine hspec.trans ?_
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hentry i with hi | hi <;> simp [hi]

end Matrix
