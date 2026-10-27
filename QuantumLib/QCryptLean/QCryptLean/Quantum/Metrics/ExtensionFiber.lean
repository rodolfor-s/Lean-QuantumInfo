import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Quantum.Channels.PartialTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.FidelityMonotone
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Metrics.SubDensityUhlmann
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations

/-! # Extension Fiber -/


noncomputable section

namespace Quantum.Operators

open Quantum.Metrics
open scoped ComplexOrder

variable {X R : Type*} [Fintype X] [Fintype R] [Nonempty X] [Nonempty R]

omit [Nonempty R] in
/-- Generalized fidelity increases under a right partial trace.
This follows from fidelity data processing and trace preservation. -/
theorem SubDensityOp.fidelityGen_le_fidelityGen_partialTraceRight
    (ρ σ : SubDensityOp (X × R)) :
    fidelityGen ρ σ ≤ fidelityGen ρ.partialTraceRight σ.partialTraceRight := by
  have hf := Quantum.Metrics.fidelity_le_apply
    (Matrix.partialTraceRightLinearMap (S := ℂ))
    Quantum.Channels.isChannel_partialTraceRight
    ρ.toPosSemidefOp σ.toPosSemidefOp
    ρ.partialTraceRight.toPosSemidefOp σ.partialTraceRight.toPosSemidefOp rfl rfl
  have ht (τ : SubDensityOp (X × R)) : τ.partialTraceRight.trace = τ.trace :=
    congrArg Complex.re (Matrix.trace_partialTraceRight τ.toOp)
  unfold fidelityGen
  rw [ht, ht]
  exact add_le_add hf le_rfl

omit [Nonempty R] in
/-- Purified distance contracts under a right partial trace. -/
theorem SubDensityOp.purifiedDistance_partialTraceRight_le (ρ σ : SubDensityOp (X × R)) :
    purifiedDistance ρ.partialTraceRight σ.partialTraceRight ≤ purifiedDistance ρ σ :=
  purifiedDistance_le_of_le_fidelityGen _ _ _ _
    (ρ.fidelityGen_le_fidelityGen_partialTraceRight σ)

/-- An arbitrary target marginal admits an extension attaining the marginal fidelity.
The proof uses native prerequisites. -/
theorem SubDensityOp.exists_extension_of_partialTraceRight_fidelityGen_eq
    (ρ : SubDensityOp (X × R)) (σ : SubDensityOp X) :
    ∃ τ : SubDensityOp (X × R), τ.partialTraceRight = σ ∧
      fidelityGen ρ τ = fidelityGen ρ.partialTraceRight σ := by
  classical
  let v := ρ.toPosSemidefOp.purificationKet
  let e := Equiv.prodAssoc X R (X × R)
  have hreg (u : Ket ((X × R) × (X × R))) :
      Matrix.partialTraceRight (u.reindex e).projector =
        Matrix.partialTraceRight (Matrix.partialTraceRight u.projector) := by
    ext i j
    exact Fintype.sum_prod_type _
  have hv : Matrix.partialTraceRight (v.reindex e).projector = ρ.partialTraceRight.toOp := by
    rw [hreg, ρ.toPosSemidefOp.partialTraceRight_purificationKet]
    rfl
  have hd : Fintype.card X ≤ Fintype.card (R × (X × R)) :=
    Fintype.card_le_of_injective (fun i : X =>
      (Classical.arbitrary R, (i, Classical.arbitrary R)))
      (fun _ _ h => congrArg (fun p => p.2.1) h)
  obtain ⟨w, hw, ho⟩ :=
    ρ.partialTraceRight.exists_livePurification_overlap_eq_fidelity_fixed_source σ
      (v.reindex e) hv hd
  let u := w.reindex e.symm
  have hu : u.reindex e = w := by ext p; rfl
  have hm : Matrix.partialTraceRight (Matrix.partialTraceRight u.projector) = σ.toOp := by
    rw [← hreg, hu, hw]
  have ht : (Matrix.partialTraceRight u.projector).trace.re = σ.trace := by
    rw [← Matrix.trace_partialTraceRight, hm]
    rfl
  let τ : SubDensityOp (X × R) :=
    { toOp := Matrix.partialTraceRight u.projector
      posSemidef := u.posSemidef_projector.partialTraceRight
      trace_le_one := ht.trans_le σ.trace_le_one }
  have hm' : τ.partialTraceRight = σ := SubDensityOp.ext hm
  have hf : fidelity ρ.toPosSemidefOp τ.toPosSemidefOp =
      fidelity ρ.partialTraceRight.toPosSemidefOp σ.toPosSemidefOp := by
    apply le_antisymm
    · change fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ≤
        fidelity ρ.toPosSemidefOp.partialTraceRight σ.toPosSemidefOp
      have he : τ.toPosSemidefOp.partialTraceRight = σ.toPosSemidefOp := Subtype.ext hm
      simpa only [he] using fidelity_le_partialTraceRight ρ.toPosSemidefOp τ.toPosSemidefOp
    · have hi : (v.dag * u : ℂ) = ((v.reindex e).dag * w : ℂ) := by
        change (∑ p : (X × R) × (X × R), star (v.vec p) * w.vec (e p)) = _
        change _ = ∑ p : X × (R × (X × R)), star (v.vec (e.symm p)) * w.vec p
        exact Fintype.sum_equiv e _ _ (fun _ => by simp)
      rw [← ho, ← hi]
      exact (Complex.re_le_norm _).trans
        (ρ.livePurificationOverlap_norm_le_fidelity τ v u
          ρ.toPosSemidefOp.partialTraceRight_purificationKet rfl)
  refine ⟨τ, hm', ?_⟩
  unfold fidelityGen
  rw [hf]
  have hρ : ρ.partialTraceRight.trace = ρ.trace :=
    congrArg Complex.re (Matrix.trace_partialTraceRight ρ.toOp)
  change _ + Real.sqrt ((1 - ρ.trace) * (1 - (Matrix.partialTraceRight u.projector).trace.re)) = _
  rw [ht, hρ]

/-- The same extension attains the distance of the two marginals. -/
theorem SubDensityOp.exists_extension_of_partialTraceRight_purifiedDistance_eq
    (ρ : SubDensityOp (X × R)) (σ : SubDensityOp X) :
    ∃ τ : SubDensityOp (X × R), τ.partialTraceRight = σ ∧
      purifiedDistance ρ τ = purifiedDistance ρ.partialTraceRight σ := by
  obtain ⟨τ, ht, hf⟩ := ρ.exists_extension_of_partialTraceRight_fidelityGen_eq σ
  exact ⟨τ, ht, by simp only [purifiedDistance, hf]⟩

end Quantum.Operators
