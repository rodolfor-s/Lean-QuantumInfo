import QCryptLean.InfoTheory.BellDiagonal.AliceZ
import QCryptLean.InfoTheory.BellDiagonal.AliceZEntropy
import QCryptLean.InfoTheory.BellDiagonal.AliceZRelativeEntropy
import QCryptLean.InfoTheory.BellDiagonal.Entropy
import QCryptLean.InfoTheory.RelativeEntropy.Measurement
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.KLDivergence
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Bell-pinching monotonicity of Alice's entropy production -/

namespace InfoTheory.BellDiagonal

open Quantum.Operators InfoTheory.VonNeumannEntropy
  Quantum.Symmetry Matrix Math.ClassicalEntropy
  InfoTheory.RelativeEntropy

/-- Alice pinching turns a Bell mixture into a diagonal with paired probabilities. -/
theorem aliceZDephase_bellDephasing_toOp_diagonal (σ : DensityOp (Fin 2 × Fin 2)) :
    (aliceZDephase (bellDephasingDensity σ)).toOp =
      diagonal (fun p => ((if p.1 = p.2 then
        (bellProbability σ (0, 0) + bellProbability σ (1, 0)) / 2
        else (bellProbability σ (0, 1) + bellProbability σ (1, 1)) / 2 : ℝ) : ℂ)) := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hp (v : Ket (Bool × Bool)) (x y : Bool × Bool) :
      v.projector x y = v.vec x * star (v.vec y) := rfl
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [aliceZDephase_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [bellDephasingDensity, bellDephasingOp, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.sum_apply, Matrix.smul_apply, DensityOp.reindex, bellDensity,
      NormKet.toDensityOp, bellNormKet, hp, bellLabelKet, bellKet,
      qubitEquiv, finTwoEquiv, Matrix.diagonal_apply, Complex.star_def, finProdFinEquiv] <;>
    field_simp <;> simp [pow_two, hs] <;> ring


/-- Alice pinching a Bell-diagonal state has one uniform bit plus the bit-error entropy. -/
theorem vonNeumannEntropy_aliceZDephase_bellDephasingDensity
    (σ : DensityOp (Fin 2 × Fin 2)) :
    vonNeumannEntropy (aliceZDephase (bellDephasingDensity σ)) =
      Real.log 2 + Math.ClassicalEntropy.binaryEntropy
        (bellProbability σ (0, 1) + bellProbability σ (1, 1)) := by
  let a := bellProbability σ (0, 0) + bellProbability σ (1, 0)
  let b := bellProbability σ (0, 1) + bellProbability σ (1, 1)
  have hab : a + b = 1 := by
    have h := sum_bellProbability σ
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, a, b, add_assoc, add_left_comm] using h
  rw [vonNeumannEntropy_eq_sum_entropyTerm_of_diagonal _ _
    (aliceZDephase_bellDephasing_toOp_diagonal σ)]
  change (∑ p : Fin 2 × Fin 2, entropyTerm (if p.1 = p.2 then a / 2 else b / 2)) = _
  have key (x : ℝ) : 2 * entropyTerm (x / 2) = entropyTerm x + x * Real.log 2 := by
    have h := Real.negMulLog_mul x (1 / 2)
    simp only [Real.negMulLog_eq_neg] at h
    rw [entropyTerm_eq_neg_mul_log, entropyTerm_eq_neg_mul_log]
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one] at h
    convert congrArg (2 * ·) h using 1 <;> ring_nf
  have h1b : 1 - b = a := by linarith
  norm_num only [Fintype.sum_prod_type, Fin.sum_univ_two, Prod.fst, Prod.snd]
  simp only [Fin.zero_ne_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  change _ = Real.log 2 + binaryEntropy b
  rw [binaryEntropy, h1b]
  have hsum : a * Real.log 2 + b * Real.log 2 = Real.log 2 := by
    rw [← add_mul, hab, one_mul]
  linarith [key a, key b]
/-- Alice dephasing averages the phase label at each fixed bit label. -/
lemma bellProbability_aliceZDephase (ρ : DensityOp (Fin 2 × Fin 2))
    (b : Fin 2 × Fin 2) :
    bellProbability (aliceZDephase ρ) b =
      (bellProbability ρ (0, b.2) + bellProbability ρ (1, b.2)) / 2 := by
  simp only [bellProbability_eq_bellBasis_diagonal]
  have he : (bellBasisᴴ * (aliceZDephase ρ).toOp * bellBasis) b b =
      ((bellBasisᴴ * ρ.toOp * bellBasis) (0,b.2) (0,b.2) +
        (bellBasisᴴ * ρ.toOp * bellBasis) (1,b.2) (1,b.2)) / 2 := by
    obtain ⟨a,b⟩ := b
    fin_cases a <;> fin_cases b <;>
      norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        conjTranspose_apply, bellBasis, bellLabelKet, bellKet, finProdFinEquiv,
        finTwoEquiv, aliceZDephase_apply, Complex.star_def] <;>
      field_simp <;> ring
  rw [he]
  simp [Complex.add_re]

/-- The Bell measurement divergence is precisely the dephased Bell entropy gain. -/
lemma classicalKLDiv_bellProbability_aliceZDephase (ρ : DensityOp (Fin 2 × Fin 2)) :
    classicalKLDiv (bellProbability ρ) (bellProbability (aliceZDephase ρ)) =
      vonNeumannEntropy (aliceZDephase (bellDephasingDensity ρ)) -
        vonNeumannEntropy (bellDephasingDensity ρ) := by
  let p := bellProbability ρ
  let a := (p (0,0) + p (1,0)) / 2
  let b := (p (0,1) + p (1,1)) / 2
  have hn (i : Fin 2 × Fin 2) : 0 ≤ p i := sq_nonneg _
  have hsplit (i : Fin 2 × Fin 2) :
      (if p i = 0 then 0 else p i * Real.log (p i / ((p (0,i.2) + p (1,i.2))/2))) =
        p i * Real.log (p i) - p i * Real.log ((p (0,i.2) + p (1,i.2))/2) := by
    split_ifs with hi
    · simp [hi]
    · have hpos : 0 < (p (0,i.2) + p (1,i.2))/2 := by
        have hpi := lt_of_le_of_ne (hn i) (Ne.symm hi)
        obtain ⟨i,j⟩ := i
        fin_cases i
        · change 0 < p (0,j) at hpi
          dsimp only [Prod.snd]
          linarith [hn (1,j)]
        · change 0 < p (1,j) at hpi
          dsimp only [Prod.snd]
          linarith [hn (0,j)]
      rw [Real.log_div hi hpos.ne']
      ring
  rw [vonNeumannEntropy_eq_sum_entropyTerm_of_diagonal _ _
    (aliceZDephase_bellDephasing_toOp_diagonal ρ), vonNeumannEntropy_bellDephasingDensity]
  simp only [classicalKLDiv, bellProbability_aliceZDephase]
  change (∑ i, if p i = 0 then 0 else p i * Real.log (p i / ((p (0,i.2) + p (1,i.2))/2))) = _
  simp_rw [hsplit, entropyTerm_eq_neg_mul_log]
  norm_num only [Fintype.sum_prod_type, Fin.sum_univ_two, Prod.fst, Prod.snd]
  simp only [Fin.zero_ne_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  change _ = -(a * Real.log a) + -(b * Real.log b) +
    (-(b * Real.log b) + -(a * Real.log a)) - _
  change _ = _ - (-(p (0,0) * Real.log (p (0,0))) + -(p (0,1) * Real.log (p (0,1))) +
    (-(p (1,0) * Real.log (p (1,0))) + -(p (1,1) * Real.log (p (1,1)))))
  dsimp only [a, b]
  ring

/-- Bell dephasing does not increase Alice's single-round entropy-production rate. -/
theorem vonNeumannEntropy_aliceZDephase_bellDephasingDensity_sub_le
    (σ : DensityOp (Fin 2 × Fin 2)) :
    vonNeumannEntropy (aliceZDephase (bellDephasingDensity σ)) -
      vonNeumannEntropy (bellDephasingDensity σ) ≤
        vonNeumannEntropy (aliceZDephase σ) - vonNeumannEntropy σ := by
  have h := classicalKLDiv_diagonal_conjugate_le σ (aliceZDephase σ) bellBasis
    bellBasis_conjTranspose_mul (ker_aliceZDephase_sub σ)
  simp only [← bellProbability_eq_bellBasis_diagonal,
    classicalKLDiv_bellProbability_aliceZDephase, relativeEntropyReal_aliceZDephase] at h
  exact h

end InfoTheory.BellDiagonal
