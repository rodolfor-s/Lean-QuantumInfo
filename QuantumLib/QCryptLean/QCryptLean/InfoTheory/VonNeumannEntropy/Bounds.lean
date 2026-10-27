import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.ContinuityBounds.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Math.SpectralTheory.Weyl
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Spectral
import QCryptLean.Quantum.Operators.Spectrum
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.TensorAlgebra

/-! # Bounds -/


noncomputable section

namespace InfoTheory.VonNeumannEntropy

open Quantum.Operators Math.ClassicalEntropy

variable {Q R : Type*} [Fintype Q] [Fintype R] {n m : ℕ}

/-- Entropy is at most the natural logarithm of the register cardinality. -/
theorem vonNeumannEntropy_le_log_dim (ρ : DensityOp Q) :
    vonNeumannEntropy ρ ≤ Real.log (Fintype.card Q) := by
  classical
  let : Nonempty Q := ρ.nonempty
  let e := Fintype.equivFin Q
  have h := shannonEntropy_le_log (fun i => ρ.eigenvalues (e.symm i))
    (fun i => ρ.eigenvalues_nonneg _) (by
      rw [Equiv.sum_comp e.symm ρ.eigenvalues]
      exact ρ.sum_eigenvalues)
  change (∑ i, entropyTerm (ρ.eigenvalues (e.symm i))) ≤ _ at h
  rw [Equiv.sum_comp e.symm (fun i => entropyTerm (ρ.eigenvalues i))] at h
  exact h

/-- Tensor additivity on product registers. -/
theorem vonNeumannEntropy_tensor_additive (ρ : DensityOp Q) (σ : DensityOp R) :
    vonNeumannEntropy (ρ.kronecker σ) = vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  classical
  have hs := congrArg (fun s : Multiset ℝ => (s.map entropyTerm).sum)
    (ρ.isHermitian.eigenvalueMultiset_kronecker σ.isHermitian)
  have hs' : vonNeumannEntropy (ρ.kronecker σ) =
      ∑ p : Q × R, entropyTerm (ρ.eigenvalues p.1 * σ.eigenvalues p.2) := by
    simp only [Matrix.IsHermitian.eigenvalueMultiset, Multiset.map_map,
      ← Finset.sum_eq_multiset_sum] at hs
    convert hs using 1
    · unfold vonNeumannEntropy DensityOp.eigenvalues
      congr 1
    · rfl
  rw [hs', Fintype.sum_prod_type]
  have hm (x y : ℝ) : entropyTerm (x * y) =
      entropyTerm x * y + x * entropyTerm y := by
    simpa only [Real.negMulLog_eq_neg, entropyTerm_eq_neg_mul_log, mul_comm y]
      using Real.negMulLog_mul x y
  simp_rw [hm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ρ.sum_eigenvalues, σ.sum_eigenvalues, mul_one, one_mul]
  rfl

/-- Entropy of a function-indexed IID state. -/
theorem vonNeumannEntropy_tensorPow (ρ : DensityOp Q) (k : ℕ) :
    vonNeumannEntropy (ρ.tensorPow k) = k * vonNeumannEntropy ρ := by
  classical
  induction k with
  | zero =>
    have h := vonNeumannEntropy_le_log_dim (ρ.tensorPow 0)
    simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one, Real.log_one] at h
    simpa only [Nat.cast_zero, zero_mul] using
      le_antisymm h (vonNeumannEntropy_nonneg (ρ.tensorPow 0))
  | succ k ih =>
    let e := Fin.consEquiv (fun _ : Fin (k + 1) => Q)
    have he : ρ.tensorPow (k + 1) = (ρ.kronecker (ρ.tensorPow k)).reindex e := by
      apply DensityOp.ext
      ext x y
      change (∏ i : Fin (k + 1), ρ.toOp (x i) (y i)) =
        ρ.toOp (x 0) (y 0) * ∏ i : Fin k, ρ.toOp (x i.succ) (y i.succ)
      exact Fin.prod_univ_succ _
    rw [he, vonNeumannEntropy_reindex, vonNeumannEntropy_tensor_additive, ih,
      Nat.cast_add, Nat.cast_one]
    ring

/-- Sharp entropy continuity in the small-distance regime. -/
theorem abs_vonNeumannEntropy_sub_le_mul_add_binaryEntropy
    (hQ : 2 ≤ Fintype.card Q) (ρ σ : DensityOp Q) (T : ℝ)
    (hT : T = Quantum.Metrics.traceDistance ρ.toOp σ.toOp)
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hTb : T ≤ 1 - 1 / (Fintype.card Q : ℝ)) :
    |vonNeumannEntropy ρ - vonNeumannEntropy σ| ≤
      T * Real.log (Fintype.card Q - 1) + binaryEntropy T := by
  classical
  by_cases hdomain : 0 ≤ T ∧ T < 1
  swap
  · exact False.elim (hdomain ⟨hT0, hT1⟩)
  let e := Fintype.equivFin Q
  let ρ' := ρ.reindex e
  let σ' := σ.reindex e
  let : NeZero (Fintype.card Q) := ⟨by omega⟩
  have hm := Math.SpectralTheory.sum_abs_sub_eigenvalues_le ρ'.toOp σ'.toOp
    ρ'.isHermitian σ'.isHermitian (ρ'.isHermitian.sub σ'.isHermitian)
  have hn : (∑ i, |(ρ'.isHermitian.sub σ'.isHermitian).eigenvalues i|) =
      2 * Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp := by
    rw [Quantum.Metrics.traceDistance,
      Quantum.Metrics.traceNorm_eq_traceNormHermitian _
        (ρ'.isHermitian.sub σ'.isHermitian)]
    unfold Quantum.Metrics.traceNormHermitian
    ring_nf
    congr 3
  rw [hn] at hm
  have hd : Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp = T := by
    rw [hT]
    exact Quantum.Metrics.traceDistance_reindex e ρ.toOp σ.toOp
  rw [hd] at hm
  have h := Math.ClassicalEntropy.abs_sub_sum_entropyTerm_le_mul_log_add_binaryEntropy
    (by omega : 1 ≤ Fintype.card Q) ρ'.eigenvalues σ'.eigenvalues
    ρ'.eigenvalues_nonneg ρ'.sum_eigenvalues σ'.eigenvalues_nonneg σ'.sum_eigenvalues T hTb hm
  change |vonNeumannEntropy ρ' - vonNeumannEntropy σ'| ≤ _ at h
  simpa only [ρ', σ', vonNeumannEntropy_reindex] using h

/-- Total entropy continuity, with the original dimension-dependent branch. -/
theorem abs_vonNeumannEntropy_sub_le_ite (hQ : 2 ≤ Fintype.card Q) (ρ σ : DensityOp Q)
    (T : ℝ) (hT : T = Quantum.Metrics.traceDistance ρ.toOp σ.toOp) (hT0 : 0 ≤ T) :
    |vonNeumannEntropy ρ - vonNeumannEntropy σ| ≤
      if T ≤ 1 - 1 / (Fintype.card Q : ℝ)
      then T * Real.log (Fintype.card Q - 1) + binaryEntropy T else Real.log (Fintype.card Q) := by
  split_ifs with hb
  · have hc : (0 : ℝ) < Fintype.card Q := by exact_mod_cast (by omega : 0 < Fintype.card Q)
    exact abs_vonNeumannEntropy_sub_le_mul_add_binaryEntropy hQ ρ σ T hT hT0
      (by have := one_div_pos.mpr hc; linarith) hb
  · exact abs_le.mpr ⟨by linarith [vonNeumannEntropy_nonneg ρ,
        vonNeumannEntropy_le_log_dim σ],
      by linarith [vonNeumannEntropy_nonneg σ, vonNeumannEntropy_le_log_dim ρ]⟩

end InfoTheory.VonNeumannEntropy
