import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Metrics.SubDensityMonotonicity
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Quantum channels on classical–quantum states -/

noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Quantum.Operators Quantum.Channels Quantum.Metrics Matrix
open scoped ComplexOrder
variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R]

/-- Apply a channel independently to each quantum block, keeping the classical register. -/
def CQState.applyChannel (ρ : CQState C Q) {Φ : Operation Q R} (hΦ : IsChannel Φ) :
    CQState C R where
  stateMap c := hΦ.applySubDensity (ρ.stateMap c)
  weight_le_one := by
    change (∑ c, (Φ (ρ.stateMap c).toOp).trace.re) ≤ 1
    have ht (c : C) : (Φ (ρ.stateMap c).toOp).trace = (ρ.stateMap c).toOp.trace :=
      hΦ.2 _
    simp_rw [ht]
    exact ρ.weight_le_one

/-- Blockwise channel action is the amplification on the joint CQ state. -/
theorem CQState.toJointDensity_applyChannel [DecidableEq C] (ρ : CQState C Q)
    {Φ : Operation Q R} (hΦ : IsChannel Φ) :
    (ρ.applyChannel hΦ).toJointDensity = hΦ.mapTensorId.applySubDensity ρ.toJointDensity := by
  apply SubDensityOp.ext
  ext p q
  change (if p.2 = q.2 then Φ (ρ.stateMap p.2).toOp p.1 q.1 else 0) =
    Φ (fun i j => if p.2 = q.2 then (ρ.stateMap p.2).toOp i j else 0) p.1 q.1
  by_cases h : p.2 = q.2
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    exact (congrFun (congrFun (map_zero Φ) p.1) q.1).symm

/-- A common channel contracts the distance of complete CQ states. -/
theorem CQState.purifiedDistance_applyChannel_le [DecidableEq C]
    [Nonempty C] [Nonempty Q] [Nonempty R]
    (ρ τ : CQState C Q) {Φ : Operation Q R} (hΦ : IsChannel Φ) :
    (ρ.applyChannel hΦ).purifiedDistance (τ.applyChannel hΦ) ≤ ρ.purifiedDistance τ := by
  unfold CQState.purifiedDistance
  rw [CQState.toJointDensity_applyChannel, CQState.toJointDensity_applyChannel]
  exact purifiedDistance_apply_le _ hΦ.mapTensorId _ _

/-- Processing the quantum register and the reference preserves every smooth entropy floor. -/
theorem smoothMinEntropy_applyChannel_le [DecidableEq C]
    [Nonempty C] [Nonempty Q] [Nonempty R]
    (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q)
    {Φ : Operation Q R} (hΦ : IsChannel Φ) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.applyChannel hΦ) (hΦ.applySubDensity σ) := by
  have h := smoothMinEntropy_le_add_of_feasible_transport ρ σ
    (ρ.applyChannel hΦ) (hΦ.applySubDensity σ) ε ε 0 le_rfl
  simp only [ENNReal.ofReal_zero, add_zero] at h
  apply h
  intro τ hd
  refine ⟨τ.applyChannel hΦ, (ρ.purifiedDistance_applyChannel_le τ hΦ).trans hd, fun t ht => ?_⟩
  simp only [Real.rpow_zero, one_mul]
  refine ⟨ht.1, fun c => opLe_of_posSemidef_sub ?_⟩
  have hs := (opLe_iff_posSemidef_sub (τ.stateMap c).isHermitian
    (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c)
  change (((t : ℂ) • Φ σ.toOp) - Φ (τ.stateMap c).toOp).PosSemidef
  have hp := hΦ.1.posSemidef hs
  simpa only [map_sub, map_smul] using hp
end InfoTheory.SmoothMinEntropy
