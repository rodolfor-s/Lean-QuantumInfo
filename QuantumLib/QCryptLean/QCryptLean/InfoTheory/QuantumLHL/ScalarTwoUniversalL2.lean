import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor

/-! # Scalar Two Universal L2 -/


noncomputable section

namespace InfoTheory.QuantumLHL


/-- The centered 2-universal collision coefficient is non-positive away from
the diagonal. -/
lemma quantumHash_offdiag_coeff_nonpos
    {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : HashFamily S X Z) (hH : H.IsTwoUniversal)
    {x x' : X} (hxx' : x ≠ x') :
    (1 / (Fintype.card S : ℝ)) *
        ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) -
      1 / (Fintype.card Z : ℝ) ≤ 0 := by
  have : Nonempty S := H.seedNonempty
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have h_inv_nonneg : 0 ≤ 1 / (Fintype.card S : ℝ) := by positivity
  have hle := mul_le_mul_of_nonneg_left (hH x x' hxx') h_inv_nonneg
  have hcollapse :
      (1 / (Fintype.card S : ℝ)) *
          ((Fintype.card S : ℝ) / (Fintype.card Z : ℝ))
        = 1 / (Fintype.card Z : ℝ) := by
    field_simp [hS_ne]
  have hcoeff_le :
      (1 / (Fintype.card S : ℝ)) *
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
        ≤ 1 / (Fintype.card Z : ℝ) :=
    hcollapse ▸ hle
  linarith

end InfoTheory.QuantumLHL

end -- noncomputable section
