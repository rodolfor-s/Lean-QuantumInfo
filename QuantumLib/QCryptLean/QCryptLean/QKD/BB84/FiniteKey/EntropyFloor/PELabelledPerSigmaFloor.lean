import QCryptLean.InfoTheory.Renyi.PetzTensor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Isometry
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelInterchange
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Penalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Reindex
import QCryptLean.InfoTheory.SmoothMinEntropy.Relabel
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.EnVDecomposition
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.IsometricInvariance
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.SiftedRoundFactorization
import QCryptLean.QKD.BB84.FiniteKey.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Own-marginal floors for test-labelled IID components

The key/test split is a structural equivalence. The announced test factor is an
independent subnormalized ancilla, referenced to itself, so it has zero entropy
charge. The reference always moves with the full CQ state.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Matrix
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement

/-- The product reference in the frame with the announced test string first. -/
def peLabelledProductRefSplit {n m : ℕ}
    (peSel xSel : Fin n → Bool) (δ Q : ℝ) (ψ : DensityOp (Signal × Signal)) :
    SubDensityOp (Signals (min n m) ×
      (Signals (keyRounds n m) × Signals (min n m))) :=
  ((((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).quantumMarginal).kronecker
    (((siftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
      (fun q => (stdNormKet q).toDensityOp.toSubDensityOp)).quantumMarginal)).reindex
        (rotateAnnouncement _ _ _).symm

/-- The sorted, test-labelled state's own marginal is the product reference. -/
theorem peLabelledSorted_quantumMarginal_eq_productRef {n m : ℕ}
    (peSel xSel : Fin n → Bool) (δ Q : ℝ) (ψ : DensityOp (Signal × Signal)) :
    (((((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).tensor
      (siftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
        (fun zq => (stdNormKet zq.2).toDensityOp.toSubDensityOp)).coarsen
          Prod.fst).quantumMarginal = peLabelledProductRefSplit peSel xSel δ Q ψ := by
  have h := congrArg CQState.quantumMarginal (reindex_coarsen_tensorLeftKernel_tensor
    ((aliceZCQState Signal ψ).tensorPower (keyRounds n m))
    (siftedPERoundProd (m := m) peSel xSel δ Q ψ)
    (fun q => (stdNormKet q).toDensityOp.toSubDensityOp))
  rw [CQState.quantumMarginal_reindex] at h
  apply SubDensityOp.ext
  ext i j
  have he := congrArg (fun σ => σ.toOp (rotateAnnouncement _ _ _ i)
    (rotateAnnouncement _ _ _ j)) h
  simpa only [peLabelledProductRefSplit, CQState.quantumMarginal, CQState.tensorRightKernel,
    SubDensityOp.kronecker, SubDensityOp.reindex, reindex_apply, submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_symm, kroneckerMap_apply, Matrix.sum_apply,
    Finset.sum_mul] using he

/-- Purification freedom transfers the component AEP to the physical key-round tensor power. -/
theorem le_smoothMinEntropy_keyTensorPower {n m : ℕ} (εTensor : ℝ)
    (ψ : DensityOp (Signal × Signal)) (hψPure : ψ.IsPure) :
    smoothMinEntropy εTensor
      ((componentAliceZCQState ψ.partialTraceRight).tensorPower (keyRounds n m))
      (((componentAliceZCQState ψ.partialTraceRight).quantumMarginalDensityOp
        (aliceZCQState_weight_eq_one Signal
          ψ.partialTraceRight.purification)).toSubDensityOp.tensorPow
          (keyRounds n m)) ≤
      smoothMinEntropy εTensor ((aliceZCQState Signal ψ).tensorPower (keyRounds n m))
        (((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).quantumMarginal) := by
  obtain ⟨W, hWblock, hWmarg⟩ := exists_unitary_componentAliceZ_eq_siftedKeyRound_conj ψ hψPure
  have hW : W.val * W.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp W.property
  have hm : ((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).quantumMarginal =
      SubDensityOp.tensorFamily (fun _ : Fin (keyRounds n m) =>
        (aliceZCQState Signal ψ).quantumMarginal) :=
    SubDensityOp.ext (CQState.tensorPower_quantumMarginal _ _)
  rw [hm]
  apply smoothMinEntropy_tensorPower_conj_le (keyRounds n m) W.val (mul_eq_one_comm.mp hW)
    (componentAliceZCQState ψ.partialTraceRight) (aliceZCQState Signal ψ)
  · intro z
    rw [hWblock z]
    simp only [← mul_assoc, hW, one_mul]
    rw [mul_assoc, hW, mul_one]
  · change (aliceZCQState Signal ψ).quantumMarginal.toOp =
      W.val * (componentAliceZCQState ψ.partialTraceRight).quantumMarginal.toOp * W.valᴴ
    rw [hWmarg]
    simp only [← mul_assoc, hW, one_mul]
    rw [mul_assoc, hW, mul_one]

/-- The complete disclosed test factor is a decoupled ancilla and incurs no entropy penalty. -/
theorem smoothMinEntropy_tensorPower_le_peLabelled {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ εTensor : ℝ) (ψ : DensityOp (Signal × Signal)) :
    smoothMinEntropy εTensor ((aliceZCQState Signal ψ).tensorPower (keyRounds n m))
      (((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).quantumMarginal) ≤
      smoothMinEntropy εTensor
        ((((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).tensor
          (siftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
            (fun zq => (stdNormKet zq.2).toDensityOp.toSubDensityOp) |>.coarsen Prod.fst)
        (peLabelledProductRefSplit peSel xSel δ Q ψ) := by
  conv_rhs => rw [← smoothMinEntropy_reindex (rotateAnnouncement _ _ _) εTensor]
  rw [reindex_coarsen_tensorLeftKernel_tensor
    ((aliceZCQState Signal ψ).tensorPower (keyRounds n m))
    (siftedPERoundProd (m := m) peSel xSel δ Q ψ)
    (fun q => (stdNormKet q).toDensityOp.toSubDensityOp)]
  have hr : (peLabelledProductRefSplit peSel xSel δ Q ψ).reindex
      (rotateAnnouncement _ _ _) =
      (((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).quantumMarginal).kronecker
        (((siftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
          (fun q => (stdNormKet q).toDensityOp.toSubDensityOp)).quantumMarginal) := by
    apply SubDensityOp.ext
    ext i j
    simp [peLabelledProductRefSplit, SubDensityOp.reindex]
  rw [hr]
  exact smoothMinEntropy_le_condTensor_decoupled_ancilla _ _ _ _ _ (fun _ => rfl)

/-- The physical Alice key has exactly the own-marginal entropy of the sorted product frame. -/
theorem smoothMinEntropy_coarsen_key_eq_sortedSplit {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ εTensor : ℝ) (ψ : DensityOp (Signal × Signal)) :
    let ρ := (peLabelledPairedHaarPerSigmaFamily (m := m) Unit
      (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ).coarsen
        (aliceKeyString peSel)
    smoothMinEntropy εTensor ρ ρ.quantumMarginal =
      smoothMinEntropy εTensor
        ((((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).tensor
          (siftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
            (fun zq => (stdNormKet zq.2).toDensityOp.toSubDensityOp) |>.coarsen Prod.fst)
        (peLabelledProductRefSplit peSel xSel δ Q ψ) := by
  let ρ := pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
    (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ
  let f := fun ω : Signals n =>
    (fun i => ((partEquiv (m := m) peSel ω).1 i).1, (partEquiv (m := m) peSel ω).2)
  let K := fun zq : Bits (keyRounds n m) × Signals (min n m) =>
    (stdNormKet zq.2).toDensityOp.toSubDensityOp
  let e := (Equiv.uniqueProd (Signals n) Unit).trans (partEquiv (m := m) peSel)
  have hco : (ρ.tensorLeftKernel (K ∘ f)).coarsen (aliceKeyString peSel) =
      (((ρ.coarsen f).tensorLeftKernel K).coarsen Prod.fst).relabel
        (sortedKeyBitEquiv peSel hcount).symm := by
    rw [CQState.coarsen_eq_relabel_coarsen (sortedKeyBitEquiv peSel hcount)
      (aliceKeyString peSel) (Prod.fst ∘ f)
      (fun ω => sortedKeyBitEquiv_aliceKeyString peSel hcount ω)]
    congr 1
    rw [← CQState.coarsen_coarsen, CQState.coarsen_tensorLeftKernel_factor]
  have hs : ((ρ.coarsen f).reindex e) =
      ((aliceZCQState Signal ψ).tensorPower (keyRounds n m)).tensor
        (siftedPERoundProd (m := m) peSel xSel δ Q ψ) := by
    rw [← CQState.coarsen_reindex]
    exact sifted_unitRegisterEmbed_coarsenKey_eq peSel xSel Q δ hcount ψ
  change smoothMinEntropy εTensor ((ρ.tensorLeftKernel (K ∘ f)).coarsen
    (aliceKeyString peSel)) ((ρ.tensorLeftKernel (K ∘ f)).coarsen
      (aliceKeyString peSel)).quantumMarginal = _
  rw [hco, CQState.quantumMarginal_relabel, smoothMinEntropy_relabel]
  rw [← smoothMinEntropy_reindex ((Equiv.refl _).prodCongr e) εTensor,
    ← CQState.quantumMarginal_reindex, ← CQState.coarsen_reindex,
    CQState.reindex_tensorRightCongr_tensorLeftKernel, hs]
  rw [peLabelledSorted_quantumMarginal_eq_productRef]

end QKD.BB84.FiniteKey
