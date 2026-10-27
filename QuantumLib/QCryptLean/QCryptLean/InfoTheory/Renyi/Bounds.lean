import Batteries.Tactic.OpenPrivate
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Bounds
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Continuity
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.Renyi.CQReference
import QCryptLean.InfoTheory.Renyi.Continuity
import QCryptLean.InfoTheory.Renyi.Reindex
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.TraceFormula
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.BlockCFC
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Theorem -/


noncomputable section

namespace InfoTheory.Renyi

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private petzTrace_bound
  from QCryptLean.InfoTheory.Renyi.PetzConditional
open private mulVec_eq_zero_of_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference

open Quantum.Operators InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open private one_le_sum_mul_exp_of_sum_mul_eq_zero
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
open private nsW
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsL
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsD
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsW_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_sum_one
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_Y_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_M_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsW_exp_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsW_exp_neg_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_divVar_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

open private klein_scaled
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.ClassicalMoments
open private nsW_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsRef_sum
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsOverlap
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private nsOverlap_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_eigenvalues_nonneg
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_support
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private ns_relEnt_eq
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights


variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q] {n : ℕ}

/-- Normalized CQ Petz DOWN entropy is nonnegative on `(1, 2]`. -/
theorem condPetzRenyiDown_nonneg (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    0 ≤ condPetzRenyiDown α ρ := by
  classical
  have hν0 : 0 < α - 1 := by linarith
  have hν1 : α - 1 ≤ 1 := by linarith
  have hb := petzTrace_bound hν0 hν1 ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))
    ρ.toJointDensity.posSemidef.nonneg ρ.toJointOp_le_reference
  rw [show (1 : ℝ) + (α - 1) = α by ring,
    show -(α - 1) = 1 - α by ring] at hb
  have ht : ρ.toJointOp.trace.re = 1 := by
    change ρ.toJointDensity.trace = 1
    rw [ρ.toJointDensity_trace, hρ]
  have hl := Real.logb_nonpos one_lt_two hb.1 (hb.2.trans ht.le)
  change 0 ≤ -(1 / (α - 1) * Real.logb 2 _)
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hl)

/-- A normalized CQ state's conditional entropy is bounded by its classical alphabet size.
This is the scaled Klein inequality on the shared finite spectral weights. -/
theorem _root_.InfoTheory.SmoothMinEntropy.CQState.condVonNeumannBits_le_logb_card
    (ρ : CQState C Q) (hnorm : ∑ x : C, (ρ.stateMap x).trace = 1) :
    CQState.condVonNeumannBits ρ ≤ Real.logb 2 (Fintype.card C) := by
  have hR0 : (0 : Matrix (Q × C) (Q × C) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointDensity.posSemidef
  have hS0 := (Matrix.posSemidef_blockDiagonal
    (fun _ : C => ρ.quantumMarginal.posSemidef)).nonneg
  have hRh : ρ.toJointOp.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
  have hSh : (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hRtr : ρ.toJointOp.trace.re = 1 := by
    change ρ.toJointDensity.trace = 1
    rw [ρ.toJointDensity_trace, hnorm]
  have hStr : (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)).trace.re =
      (Fintype.card C : ℝ) := by
    rw [Matrix.trace_blockDiagonal, Complex.re_sum]
    change (∑ _ : C, ρ.quantumMarginal.trace) = _
    rw [ρ.quantumMarginal_trace, hnorm]
    simp
  have hcard : (0 : ℝ) < (Fintype.card C : ℝ) := by
    have hn : Nonempty C := by
      by_contra h
      have : IsEmpty C := not_nonempty_iff.mp h
      simp at hnorm
    exact_mod_cast Fintype.card_pos_iff.mpr hn
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : ∑ p : (Q × C) × (Q × C),
      hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2 = 1 := by
    rw [show (fun p : (Q × C) × (Q × C) =>
        hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2) = nsW hRh hSh from rfl,
      nsW_sum hRh hSh, hRtr]
  have hB : ∑ p : (Q × C) × (Q × C),
      hSh.eigenvalues p.2 * nsOverlap hRh hSh p.1 p.2 = (Fintype.card C : ℝ) := by
    rw [nsRef_sum hRh hSh, hStr]
  have hklein := klein_scaled (fun p : (Q × C) × (Q × C) => hRh.eigenvalues p.1)
    (fun p => hSh.eigenvalues p.2) (fun p => nsOverlap hRh hSh p.1 p.2)
    (fun p => ns_eigenvalues_nonneg hRh hR0 p.1) (fun p => ns_eigenvalues_nonneg hSh hS0 p.2)
    (fun p => nsOverlap_nonneg hRh hSh p.1 p.2)
    hA (by rw [hB]; exact hcard)
    (fun p hp => ns_support hRh hSh hR0
      (fun v => mulVec_eq_zero_of_le hR0 ρ.toJointOp_le_reference (v := v)) hp p.1)
  rw [hB] at hklein
  have hnsD : ∑ p : (Q × C) × (Q × C), hRh.eigenvalues p.1
      * (Real.log (hRh.eigenvalues p.1) - Real.log (hSh.eigenvalues p.2))
      * nsOverlap hRh hSh p.1 p.2 = nsD hRh hSh := by
    rw [nsD]
    exact Finset.sum_congr rfl fun p _ => by simp only [nsW, nsL]; ring
  rw [hnsD] at hklein
  rw [CQState.condVonNeumannBits, ns_relEnt_eq hRh hSh hRtr, Real.logb, ← neg_div,
    div_le_div_iff_of_pos_right hl2]
  linarith

/-- The classical-register variance cap retains both square roots. -/
theorem condVariance_le_logb_sq (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    condVariance ρ ≤
      Real.logb 2 (Real.sqrt (Fintype.card C) + Real.sqrt ((Fintype.card C : ℝ) - 1)) ^ 2 := by
  -- the cq-state bookkeeping: hermiticity, traces, support, `card C > 0`
  have hR0 : (0 : Matrix (Q × C) (Q × C) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointDensity.posSemidef
  have hS0 := (Matrix.posSemidef_blockDiagonal (fun _ : C => ρ.quantumMarginal.posSemidef)).nonneg
  have hRh : ρ.toJointOp.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
  have hSh : (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hRtr : ρ.toJointOp.trace.re = 1 := by
    change ρ.toJointDensity.trace = 1
    rw [ρ.toJointDensity_trace, hρ]
  have hStr : (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)).trace.re =
      (Fintype.card C : ℝ) := by
    rw [Matrix.trace_blockDiagonal, Complex.re_sum]
    change (∑ _ : C, ρ.quantumMarginal.trace) = _
    rw [ρ.quantumMarginal_trace, hρ]
    simp
  have hsupp (v : Q × C → ℂ) :=
    mulVec_eq_zero_of_le hR0 ρ.toJointOp_le_reference (v := v)
  -- `(M+)`: `∑ w e^ℓ = petzTrace 2 ≤ 1`, via `condPetzRenyiDown_nonneg` at `α = 2`.
  have hM1ge : (1 : ℝ) ≤ ∑ p : (Q × C) × (Q × C), nsW hRh hSh p
      * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh)) :=
    one_le_sum_mul_exp_of_sum_mul_eq_zero (nsW hRh hSh) (fun p => nsL hRh hSh p - nsD hRh hSh)
      (fun p => nsW_nonneg hRh hSh hR0 p) (ns_sum_one hRh hSh hRtr)
      (ns_Y_sum hRh hSh hRtr) 1
  have hM1eq : (∑ p : (Q × C) × (Q × C), nsW hRh hSh p
        * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh)))
      = Real.exp (-(1 * nsD hRh hSh))
        * petzTrace (1 + 1) ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) :=
    ns_M_eq hRh hSh hR0 hS0 hsupp (s := 1) (by norm_num)
  have hpt2pos : (0 : ℝ) < petzTrace (1 + 1) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) := by
    by_contra hcon
    push Not at hcon
    have hle : (∑ p : (Q × C) × (Q × C), nsW hRh hSh p
        * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh))) ≤ 0 := by
      rw [hM1eq]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcon
    linarith
  have hpt2le : petzTrace (1 + 1) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) ≤ 1 := by
    have hnn := condPetzRenyiDown_nonneg 2 (by norm_num) (by norm_num) ρ hρ
    rw [condPetzRenyiDown, petzRenyiDivergence, neg_nonneg] at hnn
    have hlogb : Real.logb 2 (petzTrace 2 ρ.toJointOp
        (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))) ≤ 0 := by
      nlinarith [hnn]
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2] at hpt2pos ⊢
    calc petzTrace 2 ρ.toJointOp (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))
        = (2 : ℝ) ^ (Real.logb 2 (petzTrace 2 ρ.toJointOp
            (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)))) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpt2pos).symm
      _ ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hlogb
      _ = 1 := Real.rpow_zero 2
  have hMp : ∑ p : (Q × C) × (Q × C), nsW hRh hSh p * Real.exp (nsL hRh hSh p) ≤ 1 := by
    have h := nsW_exp_sum hRh hSh hR0 hS0 hsupp (a := 2) (by norm_num)
    simp only [show (2 : ℝ) - 1 = 1 from by norm_num, one_mul] at h
    rw [h, show (2 : ℝ) = 1 + 1 from by norm_num]
    exact hpt2le
  -- `(M−)`: `∑ w e^{−ℓ} ≤ Tr σ = card C`.
  have hMm : ∑ p : (Q × C) × (Q × C), nsW hRh hSh p
      * Real.exp (-(nsL hRh hSh p)) ≤ (Fintype.card C : ℝ) := by
    have h := nsW_exp_neg_le hRh hSh hR0 hS0 hsupp
    rw [hStr] at h
    exact h
  rw [condVariance, ns_divVar_eq hRh hSh hRtr,
    div_le_iff₀ (by positivity : (0 : ℝ) < Real.log 2 ^ 2)]
  refine (classical_var_le_log_sqrt_budget (nsW hRh hSh) (nsL hRh hSh)
    (fun p => nsW_nonneg hRh hSh hR0 p) (ns_sum_one hRh hSh hRtr) hMp hMm).trans ?_
  rw [one_mul, Real.logb, div_pow, div_mul_cancel₀ _
    (ne_of_gt (by positivity : (0 : ℝ) < Real.log 2 ^ 2))]

/-- Dupuis–Fawzi continuity for the original Petz DOWN specialization. -/
theorem sub_sub_le_condPetzRenyiDown (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    ρ.condVonNeumannBits - ((α - 1) * Real.log 2 / 2) * condVariance ρ
      - (α - 1) ^ 2 * secondOrderK α ρ ≤ condPetzRenyiDown α ρ := by
  have ht : ρ.toJointOp.trace.re = 1 := by
    change ρ.toJointDensity.trace = 1
    rw [ρ.toJointDensity_trace, hρ]
  have hs := Matrix.posSemidef_blockDiagonal (fun _ : C => ρ.quantumMarginal.posSemidef)
  have hsup (v : Q × C → ℂ) := mulVec_eq_zero_of_le ρ.toJointDensity.posSemidef.nonneg
    ρ.toJointOp_le_reference (v := v)
  have hb := petzRenyiDivergence_le_relEntropy_add α (2 - α) hα1 (by linarith)
    ρ.toJointOp (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))
    ρ.toJointDensity.posSemidef.nonneg hs.nonneg ht (fun v hv => hsup v hv)
  have hk : secondOrderK α ρ = petzContinuityK α (2 - α) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp)) := by
    have h2 : α + (2 - α) = 2 := by ring
    simp only [secondOrderK, continuityRemainderScale, condPetzEntropyGap,
      petzContinuityK, petzDivergenceGap, CQState.condVonNeumannBits,
      condPetzRenyiDown, h2]
    congr 3 <;> ring_nf
  rw [← hk] at hb
  simp only [CQState.condVonNeumannBits, condVariance, condPetzRenyiDown]
  linarith

/-- Normalized conditional entropy in bits is the joint-minus-marginal entropy in nats
converted by `log 2`. The trace-one hypothesis is essential. -/
theorem condVonNeumannBits_eq_vonNeumannEntropy_sub_div_log_two (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    ρ.condVonNeumannBits =
      (vonNeumannEntropy (ρ.toJointDensityOp hρ) -
        vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)) / Real.log 2 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  cases Subsingleton.elim (inferInstance : DecidableEq C) (Classical.decEq C)
  classical
  have ht : ρ.toJointOp.trace.re = 1 := by
    change ρ.toJointDensity.trace = 1
    rw [ρ.toJointDensity_trace, hρ]
  have hc : (ρ.toJointOp * CFC.log
      (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))).trace =
        (ρ.quantumMarginal.toOp * CFC.log ρ.quantumMarginal.toOp).trace := by
    change Matrix.trace (Matrix.blockDiagonal (fun c => (ρ.stateMap c).toOp) *
      cfc Real.log (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))) = _
    rw [Matrix.cfc_blockDiagonal _ (fun _ => ρ.quantumMarginal.isHermitian),
      ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]
    change (∑ c, ((ρ.stateMap c).toOp * CFC.log ρ.quantumMarginal.toOp).trace) = _
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
    rfl
  rw [InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_neg_trace_mul_log,
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_neg_trace_mul_log]
  change -(relativeEntropyBits ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))) = _
  rw [relativeEntropyBits, ht, one_mul, Matrix.mul_sub, Matrix.trace_sub, hc, Complex.sub_re]
  change -(((ρ.toJointOp * CFC.log ρ.toJointOp).trace.re -
    (ρ.quantumMarginal.toOp * CFC.log ρ.quantumMarginal.toOp).trace.re) / Real.log 2) =
      (-((ρ.toJointOp * CFC.log ρ.toJointOp).trace.re) -
        -((ρ.quantumMarginal.toOp * CFC.log ρ.quantumMarginal.toOp).trace.re)) / Real.log 2
  ring

end InfoTheory.Renyi
