import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # CQOperations -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped ComplexOrder

variable {C D Q : Type*} [Fintype C] [Fintype D] [Fintype Q]

/-- Construct a CQ state directly from positive blocks and a total trace bound. -/
def CQState.ofBlocks (B : C → Op Q) (hB : ∀ c, (B c).PosSemidef)
    (hw : ∑ c, (B c).trace.re ≤ 1) : CQState C Q where
  stateMap c :=
    { toOp := B c
      posSemidef := hB c
      trace_le_one := (Finset.single_le_sum (fun d _ =>
        (Complex.nonneg_iff.mp (hB d).trace_nonneg).1) (Finset.mem_univ c)).trans hw }
  weight_le_one := hw

/-- Push classical outcomes forward along an arbitrary function. -/
def CQState.coarsen [DecidableEq D] (f : C → D) (ρ : CQState C Q) : CQState D Q :=
  CQState.ofBlocks (fun d => ∑ c, if f c = d then (ρ.stateMap c).toOp else 0)
    (fun d => Matrix.posSemidef_sum _ fun c _ => by
      split_ifs
      · exact (ρ.stateMap c).posSemidef
      · exact Matrix.PosSemidef.zero)
    (by
      simp only [Matrix.trace_sum, Complex.re_sum]
      rw [Finset.sum_comm]
      simpa only [apply_ite Matrix.trace, Matrix.trace_zero, apply_ite Complex.re,
        Complex.zero_re, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        SubDensityOp.trace] using ρ.weight_le_one)

/-- Classical coarsening preserves the quantum marginal. -/
theorem CQState.quantumMarginal_coarsen [DecidableEq D] (f : C → D) (ρ : CQState C Q) :
    (ρ.coarsen f).quantumMarginal = ρ.quantumMarginal := by
  apply SubDensityOp.ext
  change (∑ d, ∑ c, if f c = d then (ρ.stateMap c).toOp else 0) = _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- A uniform classical register independent of a subnormalized quantum state. -/
def uniformCQState [Nonempty C] (σ : SubDensityOp Q) : CQState C Q :=
  CQState.ofBlocks (fun _ => (↑((Fintype.card C : ℝ)⁻¹) : ℂ) • σ.toOp)
    (fun _ => σ.posSemidef.smul (Complex.nonneg_iff.mpr
      ⟨inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card C)), rfl⟩))
    (by
      simp only [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
      exact σ.trace_le_one)

/-- The uniform classical extension has the original quantum marginal. -/
theorem uniformCQState_quantumMarginal [Nonempty C] (σ : SubDensityOp Q) :
    (uniformCQState (C := C) σ).quantumMarginal = σ := by
  apply SubDensityOp.ext
  change (∑ _ : C, (↑((Fintype.card C : ℝ)⁻¹) : ℂ) • σ.toOp) = σ.toOp
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Fintype.card_ne_zero]

end InfoTheory.SmoothMinEntropy
