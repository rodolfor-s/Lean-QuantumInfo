import QCryptLean.InfoTheory.SmoothMinEntropy.CQExtensionFiber
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveEntries
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.SubDensityMonotonicity
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations

/-! # Monotonicity of smooth min-entropy under blockwise operator order -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [Nonempty C] [Nonempty Q]

/-- Decreasing each positive block cannot decrease extended smooth min-entropy. -/
theorem smoothMinEntropy_mono_state (ε : ℝ) (ρ τ : CQState C Q) (σ : SubDensityOp Q)
    (h : ∀ c, (τ.stateMap c).toOp ≤ (ρ.stateMap c).toOp) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε τ σ := by
  classical
  let B (c : C) (b : Bool) : Op Q := if b then
    (τ.stateMap c).toOp else (ρ.stateMap c).toOp - (τ.stateMap c).toOp
  have hB (c : C) (b : Bool) : (B c b).PosSemidef := by
    cases b
    · exact Matrix.le_iff.mp (h c)
    · exact (τ.stateMap c).posSemidef
  let ξ : CQState C (Q × Bool) := CQState.ofBlocks (fun c => blockDiagonal (B c))
    (fun c => posSemidef_blockDiagonal (hB c)) (by
      simpa only [trace_blockDiagonal, Fintype.sum_bool, B, Bool.false_eq_true,
        Bool.true_eq, ↓reduceIte, trace_sub, add_sub_cancel, SubDensityOp.trace]
        using ρ.weight_le_one)
  have hm : ξ.partialTraceRight = ρ := by
    ext c i j
    change (∑ b : Bool, blockDiagonal (B c) (i,b) (j,b)) = _
    simp [B, blockDiagonal_apply]
  let select : CQState C (Q × Bool) → CQState C Q := fun υ =>
    CQState.ofBlocks (fun c => ((υ.stateMap c).toOp.submatrix (fun q => (q,true))
      (fun q => (q,true)))) (fun c => (υ.stateMap c).posSemidef.submatrix _)
      ((Finset.sum_le_sum fun c _ => (υ.stateMap c).posSemidef.re_trace_submatrix_le
        (fun q => (q,true)) (fun _ _ he => (Prod.mk.inj he).1)).trans υ.weight_le_one)
  have hs : select ξ = τ := by
    ext c i j
    change blockDiagonal (B c) (i,true) (j,true) = _
    simp [B]
  have hd (υ ω : CQState C (Q × Bool)) :
      (select υ).purifiedDistance (select ω) ≤ υ.purifiedDistance ω := by
    let f : Q × C → (Q × Bool) × C := fun p => ((p.1,true),p.2)
    have hf : Function.Injective f := fun _ _ he =>
      Prod.ext (congrArg (fun p => p.1.1) he)
        (congrArg (fun p : (Q × Bool) × C => p.2) he)
    have he (v : CQState C (Q × Bool)) :
        (select v).toJointDensity = v.toJointDensity.submatrix f hf := by
      ext p q
      change (if p.2 = q.2 then (v.stateMap p.2).toOp (p.1,true) (q.1,true) else 0) = _
      rfl
    simpa only [CQState.purifiedDistance, he] using
      purifiedDistance_submatrix_le υ.toJointDensity ω.toJointDensity f hf
  have hh := smoothMinEntropy_le_add_of_feasible_transport ρ σ τ σ ε ε 0 le_rfl ?_
  · simpa only [ENNReal.ofReal_zero, add_zero] using hh
  intro υ hv
  obtain ⟨ω, hw, hdw⟩ := ξ.exists_extension_of_partialTraceRight_purifiedDistance_eq υ
  refine ⟨select ω, ?_, ?_⟩
  · rw [← hs]
    rw [hm] at hdw
    exact (hd ξ ω).trans (hdw.le.trans hv)
  intro t ht
  simp only [Real.rpow_zero, one_mul]
  refine ⟨ht.1, fun c => (opLe_of_posSemidef_sub ?_).trans (ht.2 c)⟩
  have he : (υ.stateMap c).toOp = partialTraceRight (ω.stateMap c).toOp :=
    congrArg (fun v : CQState C Q => (v.stateMap c).toOp) hw.symm
  rw [he]
  change (partialTraceRight (ω.stateMap c).toOp -
    (ω.stateMap c).toOp.submatrix (fun q => (q,true)) (fun q => (q,true))).PosSemidef
  rw [partialTraceRight_eq_sum, Fintype.sum_bool, add_sub_cancel_left]
  exact (ω.stateMap c).posSemidef.submatrix _
end InfoTheory.SmoothMinEntropy
