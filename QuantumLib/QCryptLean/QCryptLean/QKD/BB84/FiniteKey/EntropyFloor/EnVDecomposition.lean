import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRotationFactorization
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.SiftedRoundFactorization
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.TensorPartition

/-! # Key/test factorization of a paired IID component

The reference register is split by the same structural round partition as the
classical outcome string. Every key round is measured in the computational basis;
the acceptance predicate belongs entirely to the test factor.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement Matrix
open scoped Kronecker

/-- At the trivial attack, the accepted reference blocks factor over physical round positions. -/
theorem sifted_unitRegisterEmbed_stateMap_eq_tensorFamily {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (Signal × Signal)) (ω : Signals n) :
    (pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ ψ).stateMap ω =
      if siftedLocalPETestPassed peSel xSel δ Q ω then
        (SubDensityOp.tensorFamily fun a => xTestRoundRefBlock ψ (peSel a) (xSel a) (ω a)).reindex
          (Equiv.uniqueProd (Signals n) Unit).symm
      else SubDensityOp.zero := by
  simp only [pairedHaarPerSigmaFamily, postMeasurementCQSiftedLocalPEPassFilter,
    CQState.filterKeep]
  split_ifs
  · exact siftedUnitRegisterEmbed_tauConditioned_eq_tensorFamily peSel xSel ψ ω
  · rfl

/-- Splitting the reference places the key blocks and test blocks in their respective factors. -/
lemma sifted_unitRegisterEmbed_reindexBlock {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hcount : KeyCount n m peSel)
    (ψ : DensityOp (Signal × Signal)) (ω : Signals n) :
    ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ ψ).stateMap ω).reindex
        ((Equiv.uniqueProd (Signals n) Unit).trans (partEquiv (m := m) peSel)) =
      if siftedLocalPETestPassed peSel xSel δ Q ω then
        (SubDensityOp.tensorFamily fun i =>
          siftedRoundRefBlock ψ false (ω (keyRoundIdx peSel i))).kronecker
            (SubDensityOp.tensorFamily fun j =>
              xTestRoundRefBlock ψ true (xSel (peRoundIdx peSel j)) (ω (peRoundIdx peSel j)))
      else SubDensityOp.zero := by
  rw [sifted_unitRegisterEmbed_stateMap_eq_tensorFamily]
  split_ifs
  · have hp := SubDensityOp.tensorFamily_partition (roundEquiv (m := m) peSel).symm
      (fun a => xTestRoundRefBlock ψ (peSel a) (xSel a) (ω a))
    simp only [Equiv.symm_symm, roundEquiv_inl, roundEquiv_inr] at hp
    have hk (i : Fin (keyRounds n m)) :
        xTestRoundRefBlock ψ (peSel (keyRoundIdx peSel i)) (xSel (keyRoundIdx peSel i))
          (ω (keyRoundIdx peSel i)) = siftedRoundRefBlock ψ false (ω (keyRoundIdx peSel i)) :=
      xTestRoundRefBlock_eq_of_not_xTest ψ _ _ (by rw [peSel_keyRoundIdx peSel hcount]; rfl) _
    simp_rw [hk, peSel_peRoundIdx peSel hcount] at hp
    convert hp using 1
    apply SubDensityOp.ext
    rfl
  · apply SubDensityOp.ext
    rfl

/-- Retain the sorted Alice key and disclosed test outcomes, together with their split reference. -/
def coarsenKey {n m : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ψ : DensityOp (Signal × Signal)) :
    CQState (Bits (keyRounds n m) × Signals (min n m))
      (Signals (keyRounds n m) × Signals (min n m)) :=
  ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
    peSel xSel Q δ ψ).reindex
      ((Equiv.uniqueProd (Signals n) Unit).trans (partEquiv (m := m) peSel))).coarsen
        (fun ω => (fun i => ((partEquiv (m := m) peSel ω).1 i).1,
          (partEquiv (m := m) peSel ω).2))

/-- The sorted key and test factors are independent before the component mixture is taken. -/
theorem sifted_unitRegisterEmbed_coarsenKey_eq {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hcount : KeyCount n m peSel)
    (ψ : DensityOp (Signal × Signal)) :
    coarsenKey (m := m) peSel xSel Q δ ψ =
      ((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).tensor
        (siftedPERoundProd (m := m) peSel xSel δ Q ψ) := by
  apply CQState.ext
  funext zp
  obtain ⟨z, p⟩ := zp
  apply SubDensityOp.ext
  ext i j
  have hk (a b : Signals (keyRounds n m)) :
      (((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).stateMap z).toOp a b =
        ∑ k : Signals (keyRounds n m), if (fun t => (k t).1) = z then
          (SubDensityOp.tensorFamily fun t => siftedRoundRefBlock ψ false (k t)).toOp a b
        else 0 := by
    rw [aliceZCQState, CQState.coarsen_tensorPower]
    simp only [CQState.coarsen, CQState.ofBlocks, CQState.tensorPower, Matrix.sum_apply,
      Matrix.ite_apply, Matrix.zero_apply, SubDensityOp.tensorFamily, piTensorProduct_apply]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · apply Finset.prod_congr rfl
      intro t _
      exact (siftedRoundRefBlock_false_toOp_apply ψ (k t) (a t) (b t)).symm
    · rfl
  simp only [coarsenKey, CQState.coarsen, CQState.ofBlocks, CQState.reindex,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  simp_rw [sifted_unitRegisterEmbed_reindexBlock peSel xSel Q δ hcount ψ,
    siftedLocalPETestPassed_eq_pePass peSel xSel δ Q hcount]
  rw [← Equiv.sum_comp (partEquiv (X := Signal) (m := m) peSel).symm,
    Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, partEquiv_symm_apply_keyIdx, partEquiv_symm_apply_peIdx]
  have he (k : Signals (keyRounds n m)) :
      (∑ q : Signals (min n m),
        if (fun t => (k t).1, q) = (z, p) then
          (if siftedPEPass (m := m) peSel xSel δ Q q then
            (SubDensityOp.tensorFamily fun t => siftedRoundRefBlock ψ false (k t)).kronecker
              (SubDensityOp.tensorFamily fun t =>
                xTestRoundRefBlock ψ true (xSel (peRoundIdx peSel t)) (q t))
            else SubDensityOp.zero).toOp i j else 0) =
        if (fun t => (k t).1) = z then
          (if siftedPEPass (m := m) peSel xSel δ Q p then
            (SubDensityOp.tensorFamily fun t => siftedRoundRefBlock ψ false (k t)).kronecker
              (SubDensityOp.tensorFamily fun t =>
                xTestRoundRefBlock ψ true (xSel (peRoundIdx peSel t)) (p t))
            else SubDensityOp.zero).toOp i j else 0 := by
    rw [Finset.sum_eq_single p]
    · simp only [Prod.mk.injEq, and_true]
    · intro q _ hq
      exact ite_eq_right (fun h => hq (congrArg Prod.snd h))
    · intro h
      exact (h (Finset.mem_univ p)).elim
  simp_rw [he]
  cases h : siftedPEPass (m := m) peSel xSel δ Q p
  · simp [CQState.tensor, siftedPERoundProd, CQState.filterKeep, h,
      SubDensityOp.kronecker, SubDensityOp.zero]
  · simp only [h, ite_true, CQState.tensor, siftedPERoundProd, CQState.filterKeep,
      SubDensityOp.kronecker, kroneckerMap_apply]
    rw [hk]
    simp only [Finset.sum_mul, ite_mul, zero_mul]

end QKD.BB84.FiniteKey
