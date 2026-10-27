import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FiniteDecomposition
import QCryptLean.InfoTheory.SmoothMinEntropy.FiniteMixture
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Metrics.PurifiedOrder
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Accepted Mixture -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics MeasureTheory
open scoped ComplexOrder MatrixOrder ENNReal
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
variable {A C Q : Type*} [Fintype A] [Fintype C] [Fintype Q]
  [DecidableEq C] [Nonempty C] [Nonempty Q]

omit [DecidableEq C] [Nonempty C] [Nonempty Q] in
/-- A continuous mixture contains a finite good-branch mixture with the prescribed trace gap. -/
theorem CQState.exists_subconvexMixture_of_integral
    (μ : Quantum.DeFinetti.DensityMeasure A)
    (ρ : CQState C Q) (f : DensityOp A → CQState C Q)
    (hρ : ∀ c i j, (ρ.stateMap c).toOp i j = ∫ τ, ((f τ).stateMap c).toOp i j ∂μ.measure)
    (hf : ∀ c, Continuous (fun τ : DensityOp A => ((f τ).stateMap c).toOp))
    (S P : Set (DensityOp A)) (hS : IsClosed S) (hP : IsClosed P)
    (hμ : ∀ᵐ τ ∂μ.measure, τ ∈ P) {ε : ℝ}
    (hbad : ∑ c, (Matrix.of fun i j => ∫ τ in Sᶜ,
      ((f τ).stateMap c).toOp i j ∂μ.measure).trace.re ≤ ε) :
    ∃ (N : ℕ) (p : Fin N → ℝ) (ψ : Fin N → DensityOp A)
      (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1),
      (∀ i, ψ i ∈ S) ∧ (∀ i, ψ i ∈ P) ∧
      (∀ c, OpLe ((CQState.subconvexMixture p hp hs (fun i => f (ψ i))).stateMap c).toOp
        (ρ.stateMap c).toOp) ∧
      (∑ c, (ρ.stateMap c).trace) -
        (∑ c, ((CQState.subconvexMixture p hp hs (fun i => f (ψ i))).stateMap c).trace) ≤ ε := by
  classical
  let := μ.isProbability
  have hint (c : C) (i j : Q) : Integrable
      (fun τ : DensityOp A => ((f τ).stateMap c).toOp i j) μ.measure :=
    (((continuous_apply j).comp (continuous_apply i)).comp (hf c)).integrable_of_compactSpace
  obtain ⟨N, p, ψ, hp, hs, hψS, hψP, he⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ f S hS.measurableSet hS hf P hP hμ
  let τ := CQState.subconvexMixture p hp hs (fun i => f (ψ i))
  have hτ (c : C) : (τ.stateMap c).toOp = Matrix.of
      (fun i j => ∫ υ in S, ((f υ).stateMap c).toOp i j ∂μ.measure) := by
    ext i j
    simpa only [τ, CQState.subconvexMixture, CQState.ofBlocks, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.of_apply] using (he c i j).symm
  let B (c : C) : Op Q := Matrix.of fun i j => ∫ υ in Sᶜ,
    ((f υ).stateMap c).toOp i j ∂μ.measure
  have hB (c : C) : (B c).PosSemidef :=
    Matrix.posSemidef_entryIntegral (fun υ => ((f υ).stateMap c).posSemidef)
      (fun i j => (hint c i j).restrict)
  have hsplit (c : C) : (ρ.stateMap c).toOp - (τ.stateMap c).toOp = B c := by
    ext i j
    rw [Matrix.sub_apply, hρ, hτ]
    exact sub_eq_iff_eq_add.mpr (by
      simpa only [B, Matrix.of_apply, add_comm] using
        (integral_add_compl hS.measurableSet (hint c i j)).symm)
  refine ⟨N, p, ψ, hp, hs, hψS, hψP, ?_, ?_⟩
  · intro c
    apply opLe_of_posSemidef_sub
    change ((ρ.stateMap c).toOp - (τ.stateMap c).toOp).PosSemidef
    rw [hsplit]
    exact hB c
  · change (∑ c, (ρ.stateMap c).trace) - (∑ c, (τ.stateMap c).trace) ≤ ε
    rw [← Finset.sum_sub_distrib]
    have ht (c : C) : (ρ.stateMap c).trace - (τ.stateMap c).trace = (B c).trace.re := by
      rw [← hsplit, Matrix.trace_sub, Complex.sub_re]
      rfl
    simpa only [ht] using hbad


/-- Component floors pass to a continuous accepted mixture with the exact bad-branch penalty. -/
theorem smoothMinEntropy_acceptedMixture_floor
    (μ : Quantum.DeFinetti.DensityMeasure A)
    (ρ : CQState C Q) (f : DensityOp A → CQState C Q) (σ : SubDensityOp Q)
    (hρ : ∀ c i j, (ρ.stateMap c).toOp i j = ∫ τ, ((f τ).stateMap c).toOp i j ∂μ.measure)
    (hf : ∀ c, Continuous (fun τ : DensityOp A => ((f τ).stateMap c).toOp))
    (S P : Set (DensityOp A)) (hS : IsClosed S) (hP : IsClosed P)
    (hμ : ∀ᵐ τ ∂μ.measure, τ ∈ P) {ε η : ℝ} (hη : 0 ≤ η)
    (hbad : ∑ c, (Matrix.of fun i j => ∫ τ in Sᶜ,
      ((f τ).stateMap c).toOp i j ∂μ.measure).trace.re ≤ ε)
    {K : ENNReal} (hK : ∀ τ ∈ S, τ ∈ P → K ≤ smoothMinEntropy η (f τ) σ) :
    K ≤ smoothMinEntropy (η + Real.sqrt (2 * ε)) ρ σ := by
  classical
  obtain ⟨N, p, ψ, hp, hs, hψS, hψP, hle, hgap⟩ :=
    ρ.exists_subconvexMixture_of_integral μ f hρ hf S P hS hP hμ hbad
  let τ := CQState.subconvexMixture p hp hs (fun i => f (ψ i))
  have ho : OpLe τ.toJointDensity.toOp ρ.toJointDensity.toOp := by
    apply opLe_of_posSemidef_sub
    change (Matrix.blockDiagonal (fun c => (ρ.stateMap c).toOp) -
      Matrix.blockDiagonal (fun c => (τ.stateMap c).toOp)).PosSemidef
    rw [← Matrix.blockDiagonal_sub]
    apply Matrix.posSemidef_blockDiagonal
    intro c
    change ((ρ.stateMap c).toOp - (τ.stateMap c).toOp).PosSemidef
    exact (opLe_iff_posSemidef_sub (τ.stateMap c).isHermitian
      (ρ.stateMap c).isHermitian).mp (hle c)
  have hgap' : ρ.toJointDensity.trace - τ.toJointDensity.trace ≤ ε := by
    simpa only [CQState.toJointDensity_trace] using hgap
  have hd : ρ.purifiedDistance τ ≤ Real.sqrt (2 * ε) :=
    ρ.toJointDensity.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_opLe
      τ.toJointDensity ho hgap'
  have hfloor : K ≤ smoothMinEntropy η τ σ :=
    smoothMinEntropy_subconvexMixture_floor p hp hs (fun i => f (ψ i)) τ
      (fun _ => rfl) (fun _ => σ) σ (by
        intro v
        simp only [← Finset.sum_smul, quadraticForm, Matrix.smul_mulVec, dotProduct_smul,
          smul_eq_mul, ← Complex.ofReal_sum, Complex.re_ofReal_mul]
        exact (mul_le_mul_of_nonneg_right hs
          (Complex.nonneg_iff.mp (σ.posSemidef.dotProduct_mulVec_nonneg v)).1).trans_eq
          (one_mul _)) hη (fun i => hK (ψ i) (hψS i) (hψP i))
  apply hfloor.trans
  have h := smoothMinEntropy_le_add_of_feasible_transport τ σ ρ σ η
    (η + Real.sqrt (2 * ε)) 0 le_rfl ?_
  · simpa only [ENNReal.ofReal_zero, add_zero] using h
  intro υ hυ
  refine ⟨υ, ?_, fun t ht => by simpa only [Real.rpow_zero, one_mul] using ht⟩
  exact (purifiedDistance_triangle ρ.toJointDensity τ.toJointDensity υ.toJointDensity).trans
    (by simpa only [CQState.purifiedDistance, add_comm] using add_le_add hd hυ)

end InfoTheory.SmoothMinEntropy
