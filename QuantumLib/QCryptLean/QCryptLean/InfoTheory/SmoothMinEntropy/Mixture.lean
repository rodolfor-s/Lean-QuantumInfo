import QCryptLean.InfoTheory.SmoothMinEntropy.AcceptedMixture
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FiniteMixture
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Metrics.PurifiedOrder
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Mixture -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Matrix Quantum.Operators Quantum.DeFinetti
  Quantum.Metrics MeasureTheory
open scoped ComplexOrder MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- A heavy-component floor survives coarsening and mixing with the exact
`εBar + sqrt (2 ε)` radius. The good branch has a finite supported mixture with varying marginal
references; the omitted positive branch costs its trace-gap distance. -/
theorem Mixture.le_smoothMinEntropy_coarsen_of_heavy_marginal
    {A Q C D : Type*} [Fintype A] [Fintype Q] [Nonempty Q]
    [Fintype C] [Fintype D] [DecidableEq D] [Nonempty D]
    (g : C → D) (μ : DensityMeasure A) (ρ : CQState C Q)
    (f : DensityOp A → CQState C Q)
    (hlin : ∀ c i j, (ρ.stateMap c).toOp i j =
      ∫ τ, ((f τ).stateMap c).toOp i j ∂μ.measure)
    (hcont : ∀ c, Continuous (fun τ => ((f τ).stateMap c).toOp))
    (good : Set (DensityOp A)) (hgood : IsClosed good)
    (P : Set (DensityOp A)) (hP : IsClosed P) (hPae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar : 0 ≤ εBar)
    (hbad : ∑ c, (Matrix.of fun i j : Q =>
      ∫ τ in goodᶜ, ((f τ).stateMap c).toOp i j ∂μ.measure).trace.re ≤ ε)
    (hfloor : ∀ τ ∈ good, τ ∈ P → εBar ^ 2 < ∑ c, ((f τ).stateMap c).trace →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar ((f τ).coarsen g) (f τ).quantumMarginal) :
    ENNReal.ofReal k ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε))
      (ρ.coarsen g) ρ.quantumMarginal := by
  classical
  obtain ⟨N, p, ψ, hp, hs, hgoodψ, hPψ, hle, hgap⟩ :=
    ρ.exists_subconvexMixture_of_integral μ f hlin hcont good P hgood hP hPae hbad
  let τ := CQState.subconvexMixture p hp hs (fun i => f (ψ i))
  have hm (υ : CQState C Q) : ∑ d, ((υ.coarsen g).stateMap d).trace =
      ∑ c, (υ.stateMap c).trace := by
    simpa only [CQState.quantumMarginal_trace] using
      congrArg SubDensityOp.trace (υ.quantumMarginal_coarsen g)
  have href : OpLe (∑ i, (p i : ℂ) • (f (ψ i)).quantumMarginal.toOp)
      ρ.quantumMarginal.toOp := by
    have he : (∑ i, (p i : ℂ) • (f (ψ i)).quantumMarginal.toOp) = τ.quantumMarginal.toOp := by
      change (∑ i, (p i : ℂ) • ∑ c, ((f (ψ i)).stateMap c).toOp) =
        ∑ c, ∑ i, (p i : ℂ) • ((f (ψ i)).stateMap c).toOp
      simp_rw [Finset.smul_sum]
      exact Finset.sum_comm
    rw [he]
    apply opLe_of_posSemidef_sub
    change ((∑ c, (ρ.stateMap c).toOp) - ∑ c, (τ.stateMap c).toOp).PosSemidef
    rw [← Finset.sum_sub_distrib]
    exact Matrix.posSemidef_sum _ fun c _ =>
      (opLe_iff_posSemidef_sub (τ.stateMap c).isHermitian (ρ.stateMap c).isHermitian).mp (hle c)
  have hf : ENNReal.ofReal k ≤ smoothMinEntropy εBar (τ.coarsen g) ρ.quantumMarginal := by
    have he := CQState.coarsen_subconvexMixture g p hp hs (fun i => f (ψ i))
    apply smoothMinEntropy_subconvexMixture_floor p hp hs (fun i => (f (ψ i)).coarsen g)
      (τ.coarsen g) (fun d => congrArg (fun υ : CQState D Q => (υ.stateMap d).toOp) he)
      (fun i => (f (ψ i)).quantumMarginal) ρ.quantumMarginal href hεBar
    intro i
    by_cases hh : εBar ^ 2 < ∑ c, ((f (ψ i)).stateMap c).trace
    · exact hfloor (ψ i) (hgoodψ i) (hPψ i) hh
    · rw [smoothMinEntropy_eq_top_of_weight_le_eps_sq hεBar _ _
        (by rw [hm]; exact le_of_not_gt hh)]
      exact le_top
  have ho : OpLe (τ.coarsen g).toJointDensity.toOp (ρ.coarsen g).toJointDensity.toOp := by
    apply opLe_of_posSemidef_sub
    change (blockDiagonal (fun d => ((ρ.coarsen g).stateMap d).toOp) -
      blockDiagonal (fun d => ((τ.coarsen g).stateMap d).toOp)).PosSemidef
    rw [← blockDiagonal_sub]
    apply posSemidef_blockDiagonal
    intro d
    change ((∑ c, if g c = d then (ρ.stateMap c).toOp else 0) -
      ∑ c, if g c = d then (τ.stateMap c).toOp else 0).PosSemidef
    rw [← Finset.sum_sub_distrib]
    apply Matrix.posSemidef_sum
    intro c _
    split_ifs
    · exact (opLe_iff_posSemidef_sub (τ.stateMap c).isHermitian
        (ρ.stateMap c).isHermitian).mp (hle c)
    · simpa only [sub_self] using (PosSemidef.zero : (0 : Op Q).PosSemidef)
  have hd : (ρ.coarsen g).purifiedDistance (τ.coarsen g) ≤ Real.sqrt (2 * ε) := by
    apply SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_opLe _ _ ho
    simpa only [CQState.toJointDensity_trace, hm] using hgap
  apply hf.trans
  have hh := smoothMinEntropy_le_add_of_feasible_transport (τ.coarsen g) ρ.quantumMarginal
    (ρ.coarsen g) ρ.quantumMarginal εBar (εBar + Real.sqrt (2 * ε)) 0 le_rfl ?_
  · simpa only [ENNReal.ofReal_zero, add_zero] using hh
  intro υ hυ
  refine ⟨υ, ?_, fun t ht => by simpa only [Real.rpow_zero, one_mul] using ht⟩
  exact (purifiedDistance_triangle (ρ.coarsen g).toJointDensity
    (τ.coarsen g).toJointDensity υ.toJointDensity).trans
    (by simpa only [CQState.purifiedDistance, add_comm] using add_le_add hd hυ)

end InfoTheory.SmoothMinEntropy
