import QCryptLean.Math.Analysis.FubiniStudy
import QCryptLean.Math.Analysis.Trig
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Math.Probability.Bhattacharyya
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.FidelityLower
import QCryptLean.Quantum.Metrics.Pure
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Metrics.Uhlmann
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Extension
import QCryptLean.Quantum.Operators.ExtensionMetrics
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations

/-! # Purified -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped MatrixOrder ComplexOrder

variable {X : Type*} [Fintype X]

/-- Symmetry of unsquared fidelity. The proof uses spectral and fidelity estimates. -/
theorem fidelity_comm (A B : PosSemidefOp X) :
    fidelity A B = fidelity B A := by
  classical
  let P := sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A
  let Q := sqrtPosSemidefOp B * A.val * sqrtPosSemidefOp B
  have hP : P.PosSemidef := by
    simpa only [(isHermitian_sqrtPosSemidefOp A).eq] using
      B.property.mul_mul_conjTranspose_same (sqrtPosSemidefOp A)
  have hQ : Q.PosSemidef := by
    simpa only [(isHermitian_sqrtPosSemidefOp B).eq] using
      A.property.mul_mul_conjTranspose_same (sqrtPosSemidefOp B)
  have hc : P.charpoly = Q.charpoly := by
    dsimp [P, Q]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, sqrtPosSemidefOp_mul_self,
      Matrix.charpoly_mul_comm (sqrtPosSemidefOp B * A.val), ← Matrix.mul_assoc,
      sqrtPosSemidefOp_mul_self, Matrix.charpoly_mul_comm A.val B.val]
  have he : hP.isHermitian.eigenvalueMultiset = hQ.isHermitian.eigenvalueMultiset := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Matrix.IsHermitian.map_eigenvalueMultiset, Matrix.IsHermitian.map_eigenvalueMultiset, hc]
  have ht (M : Op X) (hM : M.PosSemidef) :
      (CFC.sqrt M).trace.re = (hM.isHermitian.eigenvalueMultiset.map Real.sqrt).sum := by
    rw [CFC.sqrt_eq_real_sqrt M hM.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero),
      hM.isHermitian.trace_cfc]
    simp [Matrix.IsHermitian.eigenvalueMultiset, Multiset.map_map, Complex.re_sum]
  exact (ht P hP).trans ((congrArg (fun s : Multiset ℝ => (s.map Real.sqrt).sum) he).trans
    (ht Q hQ).symm)

/-- Squared fidelity against a pure state is its Born probability, for any positive input. -/
theorem fidelitySq_pure_right (A : PosSemidefOp X) (v : NormKet X) :
    fidelitySq A v.toDensityOp.toPosSemidefOp = (v.toKet.projector * A.val).trace.re := by
  classical
  let P := v.toKet.projector
  let c := (P * A.val).trace
  have hP : P.PosSemidef := v.toDensityOp.posSemidef
  have hc : 0 ≤ c := v.toDensityOp.posSemidef.trace_mul_nonneg A.property
  have hre : (c.re : ℂ) = c := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hc).2
  have hs : CFC.sqrt P = P :=
    CFC.sqrt_unique v.isPure_toDensityOp v.toDensityOp.posSemidef.nonneg
  have hp : P * A.val * P = c • P := by
    change vecMulVec v.vec (star v.vec) * A.val * vecMulVec v.vec (star v.vec) =
      (vecMulVec v.vec (star v.vec) * A.val).trace • vecMulVec v.vec (star v.vec)
    rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, trace_vecMulVec, vecMulVec_smul,
      dotProduct_comm]
  have hf : fidelity v.toDensityOp.toPosSemidefOp A = Real.sqrt c.re := by
    unfold fidelity sqrtPosSemidefOp
    change (CFC.sqrt (CFC.sqrt P * A.val * CFC.sqrt P)).trace.re = _
    rw [hs, hp, ← hre, hP.sqrt_ofReal_smul
      (Complex.nonneg_iff.mp hc).1, hs, Matrix.trace_smul]
    change (((Real.sqrt c.re : ℝ) : ℂ) * v.toDensityOp.toOp.trace).re = _
    simp only [v.toDensityOp.trace_one, mul_one, Complex.ofReal_re]
  rw [fidelitySq, fidelity_comm, hf, Real.sq_sqrt (Complex.nonneg_iff.mp hc).1]


/-- The trace bound for positive-operator fidelity. The proof uses spectral and fidelity
estimates. -/
theorem fidelity_le_sqrt_trace_mul_trace (A B : PosSemidefOp X) :
    fidelity A B ≤ Real.sqrt (A.val.trace.re * B.val.trace.re) := by
  obtain ⟨v, hv, ho⟩ := exists_purification_overlap_re_eq_fidelity A B
  let u : EuclideanSpace ℂ (X × X) := WithLp.toLp 2 A.purificationKet.vec
  let w : EuclideanSpace ℂ (X × X) := WithLp.toLp 2 v.vec
  have hi : inner ℂ u w = (A.purificationKet.dag * v : ℂ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hu : ‖u‖ = Real.sqrt A.val.trace.re := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change Real.sqrt (A.purificationKet.dag * A.purificationKet : ℂ).re = _
    rw [← Ket.trace_projector, A.trace_purificationKet]
  have hw : ‖w‖ = Real.sqrt B.val.trace.re := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change Real.sqrt (v.dag * v : ℂ).re = _
    rw [← Ket.trace_projector, ← Matrix.trace_partialTraceRight v.projector, hv]
  calc
    fidelity A B = (inner ℂ u w).re := by rw [hi, ho]
    _ ≤ ‖u‖ * ‖w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ = _ := by rw [hu, hw, ← Real.sqrt_mul
      ((Complex.nonneg_iff.mp A.property.trace_nonneg).1)]

/-- Generalized fidelity squared is at most one. The proof uses spectral and fidelity
estimates. -/
theorem fidelityGen_sq_le_one (ρ σ : SubDensityOp X) :
    fidelityGen ρ σ ^ 2 ≤ 1 := by
  have hF := fidelity_le_sqrt_trace_mul_trace ρ.toPosSemidefOp σ.toPosSemidefOp
  have hcs := Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one
    (show ρ.trace ∈ Set.Icc (0 : ℝ) 1 from ⟨ρ.trace_nonneg, ρ.trace_le_one⟩)
    (show σ.trace ∈ Set.Icc (0 : ℝ) 1 from ⟨σ.trace_nonneg, σ.trace_le_one⟩)
  change fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤ Real.sqrt (ρ.trace * σ.trace) at hF
  have hle : fidelityGen ρ σ ≤ 1 := by unfold fidelityGen; linarith
  nlinarith [fidelityGen_nonneg ρ σ]

/-- The Bures-angle triangle inequality for subnormalized states. -/
theorem arccos_fidelityGen_triangle [Nonempty X] (ρ σ τ : SubDensityOp X) :
    Real.arccos (fidelityGen ρ τ) ≤ Real.arccos (fidelityGen ρ σ) +
      Real.arccos (fidelityGen σ τ) := by
  classical
  let A := ρ.toDensityOpExtend
  let B := σ.toDensityOpExtend
  let C := τ.toDensityOpExtend
  obtain ⟨v, hv, ho⟩ := exists_purification_overlap_re_eq_fidelity B.toPosSemidefOp A.toPosSemidefOp
  obtain ⟨w, hw, hp⟩ := exists_purification_overlap_re_eq_fidelity B.toPosSemidefOp C.toPosSemidefOp
  let b := B.purificationKet.toKet
  have hn (D : DensityOp (X ⊕ Unit)) (v : Ket ((X ⊕ Unit) × (X ⊕ Unit)))
      (h : partialTraceRight v.projector = D.toOp) : (v.dag * v : ℂ) = 1 := by
    rw [← Ket.trace_projector, ← Matrix.trace_partialTraceRight, h, D.trace_one]
  let e (v : Ket ((X ⊕ Unit) × (X ⊕ Unit))) :
      EuclideanSpace ℂ ((X ⊕ Unit) × (X ⊕ Unit)) := WithLp.toLp 2 v.vec
  have hi (u v : Ket ((X ⊕ Unit) × (X ⊕ Unit))) :
      inner ℂ (e u) (e v) = (u.dag * v : ℂ) := by
    simp only [e, EuclideanSpace.inner_toLp_toLp]
    change v.vec ⬝ᵥ star u.vec = star u.vec ⬝ᵥ v.vec
    exact dotProduct_comm _ _
  have he (u : Ket ((X ⊕ Unit) × (X ⊕ Unit))) (h : (u.dag * u : ℂ) = 1) :
      ‖e u‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hi, h]
    norm_num
  have htri := InnerProductSpace.arccos_norm_inner_le (e v) (e b) (e w)
    (he v (hn A v hv)) (he b B.purificationKet.normalized) (he w (hn C w hw))
  simp only [hi] at htri
  have htop := norm_overlap_le_fidelity_of_partialTraceRight_eq A C v w hv hw
  have hflip : ‖(v.dag * b : ℂ)‖ = ‖(b.dag * v : ℂ)‖ := by
    rw [← hi, ← hi, norm_inner_symm]
  have hl : fidelity A.toPosSemidefOp B.toPosSemidefOp ≤ ‖(v.dag * b : ℂ)‖ := by
    rw [hflip, fidelity_comm, ← ho]
    exact Complex.re_le_norm _
  have hr : fidelity B.toPosSemidefOp C.toPosSemidefOp ≤ ‖(b.dag * w : ℂ)‖ := by
    rw [← hp]
    exact Complex.re_le_norm _
  have h := (Real.arccos_le_arccos htop).trans
    (htri.trans (add_le_add (Real.arccos_le_arccos hl) (Real.arccos_le_arccos hr)))
  change Real.arccos (fidelity ρ.toDensityOpExtend.toPosSemidefOp
    τ.toDensityOpExtend.toPosSemidefOp) ≤
    Real.arccos (fidelity ρ.toDensityOpExtend.toPosSemidefOp σ.toDensityOpExtend.toPosSemidefOp) +
      Real.arccos (fidelity σ.toDensityOpExtend.toPosSemidefOp
        τ.toDensityOpExtend.toPosSemidefOp) at h
  simpa only [SubDensityOp.toDensityOpExtend_fidelity] using h

/-- The triangle inequality for purified distance. The proof uses spectral and fidelity
estimates. -/
theorem purifiedDistance_triangle [Nonempty X] (ρ σ τ : SubDensityOp X) :
    purifiedDistance ρ τ ≤ purifiedDistance ρ σ + purifiedDistance σ τ := by
  have hangle := arccos_fidelityGen_triangle ρ σ τ
  have hs := Real.sin_le_sin_add_sin_of_le_add
    (show Real.arccos (fidelityGen ρ σ) ∈ Set.Icc 0 (Real.pi / 2) from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (fidelityGen_nonneg ρ σ)⟩)
    (show Real.arccos (fidelityGen σ τ) ∈ Set.Icc 0 (Real.pi / 2) from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (fidelityGen_nonneg σ τ)⟩)
    (show Real.arccos (fidelityGen ρ τ) ∈ Set.Icc 0 (Real.pi / 2) from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (fidelityGen_nonneg ρ τ)⟩) hangle
  simpa only [Real.sin_arccos, purifiedDistance] using hs

/-- Generalized trace distance is bounded by purified distance. -/
theorem traceDistanceGen_le_purifiedDistance [Nonempty X] (ρ σ : SubDensityOp X) :
    traceDistanceGen ρ.toOp σ.toOp ≤ purifiedDistance ρ σ := by
  classical
  let A := ρ.toDensityOpExtend
  let B := σ.toDensityOpExtend
  obtain ⟨w, hw, ho⟩ := exists_purification_overlap_re_eq_fidelity A.toPosSemidefOp B.toPosSemidefOp
  have hwNorm : w.IsNormalized := by
    rw [Ket.IsNormalized, ← Ket.trace_projector, ← Matrix.trace_partialTraceRight, hw]
    exact B.trace_one
  let W : NormKet ((X ⊕ Unit) × (X ⊕ Unit)) := ⟨w, hwNorm⟩
  have hv : partialTraceRight A.purificationKet.toKet.projector = A.toOp :=
    A.toPosSemidefOp.partialTraceRight_purificationKet
  have hbound := norm_overlap_le_fidelity_of_partialTraceRight_eq A B
    A.purificationKet.toKet w hv hw
  have he : ‖(A.purificationKet.toKet.dag * w : ℂ)‖ =
      fidelity A.toPosSemidefOp B.toPosSemidefOp := by
    apply le_antisymm hbound
    rw [← ho]
    exact Complex.re_le_norm _
  have hc := traceNorm_apply_le_of_isHermitian
    (partialTraceRightLinearMap (S := ℂ) : Op ((X ⊕ Unit) × (X ⊕ Unit)) →ₗ[ℂ] Op (X ⊕ Unit))
    (fun C hC => hC.partialTraceRight)
    (fun C _ => le_of_eq (congrArg Complex.re (Matrix.trace_partialTraceRight C)))
    (A.purification.toOp - W.toDensityOp.toOp)
    (A.purification.isHermitian.sub W.toDensityOp.isHermitian)
  change traceNorm (partialTraceRight (A.purificationKet.toKet.projector - w.projector)) ≤ _ at hc
  rw [partialTraceRight_sub, hv, hw] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change traceDistance A.toOp B.toOp ≤
    traceDistance A.purificationKet.toDensityOp.toOp W.toDensityOp.toOp at hc'
  rw [traceDistance_pure] at hc'
  change traceDistance A.toOp B.toOp ≤
    Real.sqrt (1 - ‖(A.purificationKet.toKet.dag * w : ℂ)‖ ^ 2) at hc'
  rw [he] at hc'
  change traceDistance ρ.extendOp σ.extendOp ≤
    Real.sqrt (1 - fidelity ρ.toDensityOpExtend.toPosSemidefOp
      σ.toDensityOpExtend.toPosSemidefOp ^ 2) at hc'
  rw [ρ.toDensityOpExtend_traceDistance σ, ρ.toDensityOpExtend_fidelity σ] at hc'
  exact hc'

/-- The subnormalized lower Fuchs--van de Graaf bound. -/
theorem one_sub_fidelityGen_le_traceDistanceGen [Nonempty X] (ρ σ : SubDensityOp X) :
    1 - fidelityGen ρ σ ≤ traceDistanceGen ρ.toOp σ.toOp := by
  have h := half_trace_add_sub_fidelity_le_traceDistance
    ρ.toDensityOpExtend.toPosSemidefOp σ.toDensityOpExtend.toPosSemidefOp
  change (ρ.toDensityOpExtend.toOp.trace.re + σ.toDensityOpExtend.toOp.trace.re) / 2 -
    fidelity ρ.toDensityOpExtend.toPosSemidefOp σ.toDensityOpExtend.toPosSemidefOp ≤
      traceDistance ρ.toDensityOpExtend.toOp σ.toDensityOpExtend.toOp at h
  rw [ρ.toDensityOpExtend.trace_one, σ.toDensityOpExtend.trace_one,
    Complex.one_re, SubDensityOp.toDensityOpExtend_fidelity] at h
  change (1 + 1) / 2 - fidelityGen ρ σ ≤ traceDistance ρ.extendOp σ.extendOp at h
  rw [SubDensityOp.toDensityOpExtend_traceDistance] at h
  norm_num at h
  linarith

/-- Symmetry of generalized fidelity follows from symmetry of fidelity. -/
theorem fidelityGen_comm (ρ σ : SubDensityOp X) :
    fidelityGen ρ σ = fidelityGen σ ρ := by
  rw [fidelityGen, fidelityGen, fidelity_comm, mul_comm]

/-- Purified distance is symmetric. -/
theorem purifiedDistance_comm (ρ σ : SubDensityOp X) :
    purifiedDistance ρ σ = purifiedDistance σ ρ := by
  rw [purifiedDistance, purifiedDistance, fidelityGen_comm]

/-- Generalized fidelity lies below one. -/
theorem fidelityGen_le_one (ρ σ : SubDensityOp X) : fidelityGen ρ σ ≤ 1 := by
  nlinarith [fidelityGen_sq_le_one ρ σ]

/-- Squaring purified distance recovers its defining radicand. -/
theorem purifiedDistance_sq (ρ σ : SubDensityOp X) :
    purifiedDistance ρ σ ^ 2 = 1 - fidelityGen ρ σ ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (fidelityGen_sq_le_one ρ σ))

/-- The upper subnormalized Fuchs--van de Graaf bound. -/
theorem purifiedDistance_le_sqrt_two_mul_traceDistanceGen [Nonempty X]
    (ρ σ : SubDensityOp X) :
    purifiedDistance ρ σ ≤ Real.sqrt (2 * traceDistanceGen ρ.toOp σ.toOp) := by
  apply Real.sqrt_le_sqrt
  nlinarith [one_sub_fidelityGen_le_traceDistanceGen ρ σ, sq_nonneg (fidelityGen ρ σ - 1)]

end Quantum.Metrics
