import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.KroneckerSandwich
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Input
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations

/-! # Agree-block real and ideal hashing outputs

Both pass outputs are the same channel applied to the real or uniform public-seed
hashing state. Every public announcement remains in the conditioning register.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Matrix
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open QKD.BB84.Model QKD.BB84.Measurement
open scoped Kronecker

variable (E : Type*) [Fintype E] [DecidableEq E]
variable {R : Type*} [Fintype R]

/-- The amplified sifted pre-channel is the operator used to extract the CQ blocks. -/
private theorem siftedPreOutput_toOp {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (τ : DensityOp (Signals n × R)) :
    mapTensorId (siftedConjAfterPre E pre peSel xSel) R τ.toOp =
      (siftedTauPreOutputDensity E pre hpre peSel xSel τ).toOp := by
  classical
  rw [siftedConjAfterPre, mapTensorId_comp]
  simp only [LinearMap.comp_apply, siftedConjChannel, mapTensorId_conjLinearMap]
  simp only [siftedTauPreOutputDensity, UnitaryOp.evolve, tauOutputDensity,
    IsChannel.applyDensity, Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 2 <;> ext i j <;> simp [kroneckerMap_apply, Matrix.one_apply]

/-- The syndrome and verification kernel reads only its actual announced values. -/
private theorem announceKernel_apply {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel)
    (p q : Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) :
    (announceKernel ℓEV peSel ec x).toOp p q =
      if p = q ∧ p.1 = ec.syndrome x ∧ p.2.2 = verificationTag n ℓEV peSel p.2.1 x
      then (Fintype.card (KeyHashSeed n ℓEV peSel) : ℂ)⁻¹ else 0 := by
  classical
  change (↑((Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ)⁻¹) •
    seedGraphProj (fun t => (ec.syndrome x, verificationTag n ℓEV peSel t x)))
      (p.2.1, (p.1, p.2.2)) (q.2.1, (q.1, q.2.2)) = _
  rw [seedGraphProj_eq_diagonal]
  by_cases hpq : p = q
  · subst q
    simp [Matrix.smul_apply, Prod.ext_iff]
  · have hne : (p.2.1, (p.1, p.2.2)) ≠ (q.2.1, (q.1, q.2.2)) := by
      intro h
      apply hpq
      rcases Prod.mk.inj h with ⟨hs, hat⟩
      rcases Prod.mk.inj hat with ⟨ha, ht⟩
      exact Prod.ext ha (Prod.ext hs ht)
    simp [Matrix.smul_apply, hpq, hne]

omit [DecidableEq E] in
/-- Copying and structurally relabelling a CQ state preserves all its conditioning entries. -/
private theorem postprocess_joint_apply {n m ℓ ℓEV leakEC : ℕ} (peSel : Fin n → Bool)
    (ρ : CQState (KeyHashSeed n ℓ peSel × Bits ℓ)
      ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R))))
    (p q : (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :
    peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel ρ.toJointDensity.toOp p q =
      ∑ sz : KeyHashSeed n ℓ peSel × Bits ℓ,
        if ((sz.2, sz.2), (true, sz.1)) =
            ((peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm p).1 ∧
          ((sz.2, sz.2), (true, sz.1)) =
            ((peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm q).1
        then (ρ.stateMap sz).toOp
          ((peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm p).2
          ((peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm q).2
        else 0 := by
  classical
  let p' := (peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm p
  let q' := (peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel).symm q
  change (classicalMap (fun sz : KeyHashSeed n ℓ peSel × Bits ℓ =>
    ((sz.2, sz.2), (true, sz.1)))
      (fun i j => ρ.toJointOp (p'.2, i) (q'.2, j)) p'.1 q'.1) = _
  simp [classicalMap, krausMap, CQState.toJointOp, blockDiagonal_apply,
    Matrix.sum_apply, Matrix.single_apply, p', q']

/-- The LHL input exposes the exact accepted outcome blocks and announcement factors. -/
private theorem agreeInput_apply {n m : ℕ} (ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) (x : KeyBitString n peSel)
    (p q : (Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
      (Signals (min n m) × (E × R))) :
    ((peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ).stateMap x).toOp
      p q = (announceKernel ℓEV peSel ec x).toOp p.1 q.1 *
        ∑ ω : Signals n, if aliceKeyString peSel ω = x ∧
            (partEquiv (m := m) peSel ω).2 = p.2.1 ∧
            (partEquiv (m := m) peSel ω).2 = q.2.1 ∧
            siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
          then (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).toOp p.2.2 q.2.2
          else 0 := by
  classical
  change (announceKernel ℓEV peSel ec x).toOp p.1 q.1 *
    (∑ ω, if aliceKeyString peSel ω = x then
      (stdNormKet ((partEquiv (m := m) peSel ω).2)).projector ⊗ₖ
        ((siftedAgreeAcceptCQState E pre hpre peSel xSel ec Q δ τ).stateMap ω).toOp
      else 0) p.2 q.2 = _
  congr 1
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  have hp (t : Signals (min n m)) :
      (stdNormKet t).projector = Matrix.single t t 1 := by
    ext i j
    change ((Pi.single t 1 : Signals (min n m) → ℂ) i) *
      star ((Pi.single t 1 : Signals (min n m) → ℂ) j) = _
    by_cases hi : t = i <;> by_cases hj : t = j <;>
      simp [Pi.single_apply, Matrix.single_apply, hi, hj, eq_comm]
  by_cases hx : aliceKeyString peSel ω = x
  · simp only [ite_eq_left hx, hp, siftedAgreeAcceptCQState, CQState.filterKeep,
      siftedTauPostMeasurementNormalizedCQState]
    by_cases ht : siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true <;>
      simp [ht, hx, kroneckerMap_apply, Matrix.single_apply, SubDensityOp.zero]
  · simp [hx]

omit [Fintype E] in
open scoped Classical in
/-- Agreement makes both real key slots equal and removes the seed-dependent gate. -/
private theorem agreePassKraus_eq {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    (if siftedKeyStringsDiffer peSel ec ω then 0
      else Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (st, ω)) =
      if siftedAgreeAcceptKeep peSel xSel ec δ Q ω then
        Matrix.single (Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
          (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω)) st ω) ω 1 ⊗ₖ (1 : Op E)
      else 0 := by
  classical
  by_cases hd : siftedKeyStringsDiffer peSel ec ω = true
  · simp [hd, siftedAgreeAcceptKeep]
  · have hd' : siftedKeyStringsDiffer peSel ec ω = false := Bool.eq_false_iff.mpr hd
    have hk : aliceKeyString peSel ω = ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω)) := by
      by_contra hn
      exact hd ((siftedKeyStringsDiffer_eq_true_iff peSel ec ω).mpr hn)
    simp only [Announced.passKraus,
      siftedLocalPEAndEVPassed.eq_siftedLocalPETestPassed_of_not_differ
        peSel xSel ec δ Q st.2 ω hd',
      siftedAgreeAcceptKeep, hd', Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true,
      Announced.passOutputIndex,
      Announced.idealPassOutputIndex, ← hk]
    split_ifs <;> ext i j <;>
      simp [kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]

omit [Fintype E] in
open scoped Classical in
/-- The ideal gate has the same seed-free form on agreeing outcomes. -/
private theorem agreeIdealPassKraus_eq {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (ω : Signals n) (z : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (if siftedKeyStringsDiffer peSel ec ω then 0
      else Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (ω, z, st)) =
      if siftedAgreeAcceptKeep peSel xSel ec δ Q ω then
        Matrix.single (Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec z st ω)
          ω 1 ⊗ₖ
          (1 : Op E)
      else 0 := by
  classical
  by_cases hd : siftedKeyStringsDiffer peSel ec ω = true
  · simp [hd, siftedAgreeAcceptKeep]
  · have hd' : siftedKeyStringsDiffer peSel ec ω = false := Bool.eq_false_iff.mpr hd
    simp only [Announced.idealPassKraus,
      siftedLocalPEAndEVPassed.eq_siftedLocalPETestPassed_of_not_differ
        peSel xSel ec δ Q st.2 ω hd',
      siftedAgreeAcceptKeep, hd', Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true]
    split_ifs <;> ext i j <;>
      simp [kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]

open scoped Classical in
/-- The real agreed pass branch reads exactly the conditioned measurement entries. -/
private theorem realAgree_apply {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R))
    (p q : (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :
    mapTensorId
      (((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.2 then 0
          else Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) R τ.toOp p q =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ *
        ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel, ∑ ω : Signals n,
          if siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true ∧
              Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
                (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω)) st ω = p.1.1 ∧
              Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
                (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω)) st ω = q.1.1
          then (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).toOp
            (p.1.2, p.2) (q.1.2, q.2) else 0 := by
  classical
  rw [mapTensorId_comp, mapTensorId_comp]
  simp only [LinearMap.comp_apply, siftedPreOutput_toOp E pre hpre]
  simp only [mapTensorId_apply, LinearMap.smul_apply, krausMap, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul, one_div, Matrix.sum_apply]
  congr 1
  conv_lhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro st _
  apply Finset.sum_congr rfl
  intro ω _
  rw [agreePassKraus_eq]
  by_cases hg : siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
  · simp only [hg, ite_true, true_and]
    by_cases hp : Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
        (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω)) st ω = p.1.1 <;>
      by_cases hq : Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
        (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω)) st ω = q.1.1 <;>
      simp_all [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply,
      mapTensorId_apply, classicalMap, krausMap, siftedTauEveRefConditioned,
      SubDensityOp.submatrix, DensityOp.toSubDensityOp, tauOutcomeEveRefEmbedding,
      ite_and, apply_ite]
  · simp [hg]

open scoped Classical in
/-- The real agreed pass output is the postprocessed public-seed hashing state. -/
theorem realAgreePass_mapTensorId_eq_lhlPostprocess_seedKeyOutput {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) :
    mapTensorId
      (((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.2 then 0
          else Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) R τ.toOp =
      peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel
        (SeedKey.output (aliceKeyHashFamily n ℓ peSel)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ
            τ)).toJointDensity.toOp := by
  classical
  ext p q
  rw [realAgree_apply E ℓ ℓEV pre hpre, postprocess_joint_apply]
  simp only [SeedKey.output, CQState.ofBlocks, SeedKey.weightedOp, Matrix.smul_apply,
    Matrix.sum_apply, Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_natCast,
    Matrix.ite_apply, Matrix.zero_apply, agreeInput_apply, announceKernel_apply,
    peAnnounceAgreeLHLPostprocessEquiv, Equiv.coe_fn_symm_mk]
  simp only [Finset.mul_sum, Finset.ite_sum_zero]
  conv_rhs =>
    arg 2
    ext sz
    rw [Finset.sum_comm]
    arg 2
    ext ω
    rw [Finset.sum_eq_single (aliceKeyString peSel ω)
      (by intro x _ hx; simp [Ne.symm hx, ite_and]) (by simp)]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (p.1.1.2.2.1.1.1.2)
    (by
      intro t _ ht
      simp [Announced.idealPassOutputIndex, Announced.pePassOutIndex, Prod.ext_iff,
        ht]) (by simp)]
  conv_rhs =>
    rw [Finset.sum_eq_single ((aliceKeyHashFamily n ℓ peSel).hash s (aliceKeyString peSel ω))
      (by intro z _ hz; simp [Ne.symm hz]) (by simp)]
  simp only [Announced.idealPassOutputIndex, Announced.pePassOutIndex, Prod.ext_iff,
    KeyHashSeedPairEV, Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev, mul_ite, mul_zero,
    true_and, and_true, eq_self]
  simp only [aliceKeyHashFamily, keyHash, mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and,
    mul_assoc]
  congr 1
  · apply propext
    constructor <;> intro h <;> aesop
  · ring

open scoped Classical in
/-- The ideal agreed branch reads the same conditioned measurement entries. -/
private theorem idealAgree_apply {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R))
    (p q : (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :
    mapTensorId
      (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.1 then 0
          else Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) R τ.toOp p q =
      ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))⁻¹ *
        ∑ ω : Signals n, ∑ z : Bits ℓ, ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel,
          if siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true ∧
              Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
                z st ω = p.1.1 ∧
              Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
                z st ω = q.1.1
          then (siftedTauEveRefConditioned E pre hpre peSel xSel τ ω).toOp
            (p.1.2, p.2) (q.1.2, q.2) else 0 := by
  classical
  rw [mapTensorId_comp, mapTensorId_comp]
  simp only [LinearMap.comp_apply, siftedPreOutput_toOp E pre hpre]
  simp only [mapTensorId_apply, LinearMap.smul_apply, krausMap, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul, one_div, Matrix.sum_apply]
  congr 1
  conv_lhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  conv_lhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro st _
  rw [agreeIdealPassKraus_eq]
  by_cases hg : siftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
  · simp only [hg, ite_true, true_and]
    by_cases hp : Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
        z st ω = p.1.1 <;>
      by_cases hq : Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec
        z st ω = q.1.1 <;>
      simp_all [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply,
      mapTensorId_apply, classicalMap, krausMap, siftedTauEveRefConditioned,
      SubDensityOp.submatrix, DensityOp.toSubDensityOp, tauOutcomeEveRefEmbedding,
      ite_and, apply_ite]
  · simp [hg]

open scoped Classical in
/-- The ideal agreed pass output is the postprocessed uniform public-seed state. -/
theorem mapTensorId_idealAgree_eq_postprocess_uniformOutput {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) :
    mapTensorId
      (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.1 then 0
          else Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) R τ.toOp =
      peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel
        (uniformCQState (C := KeyHashSeed n ℓ peSel × Bits ℓ)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ).quantumMarginal
          ).toJointDensity.toOp := by
  classical
  ext p q
  rw [idealAgree_apply E ℓ ℓEV pre hpre, postprocess_joint_apply]
  simp only [uniformCQState, CQState.ofBlocks, CQState.quantumMarginal, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    agreeInput_apply, announceKernel_apply,
    peAnnounceAgreeLHLPostprocessEquiv, Equiv.coe_fn_symm_mk]
  simp only [Finset.mul_sum, Finset.ite_sum_zero]
  conv_rhs =>
    arg 2
    ext sz
    rw [Finset.sum_comm]
    arg 2
    ext ω
    rw [Finset.sum_eq_single (aliceKeyString peSel ω)
      (by intro x _ hx; simp [Ne.symm hx, ite_and]) (by simp)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  conv_rhs =>
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  conv_lhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (p.1.1.2.2.1.1.1.2)
    (by
      intro t _ ht
      simp [Announced.idealPassOutputIndex, Announced.pePassOutIndex, Prod.ext_iff, ht])
    (by simp)]
  simp only [Announced.idealPassOutputIndex, Announced.pePassOutIndex, Prod.ext_iff,
    KeyHashSeedPairEV, Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev, mul_ite, mul_zero,
    true_and, and_true, eq_self]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and, mul_assoc]
  congr 1
  · apply propext
    constructor <;> intro h <;> aesop
  · simp [Bits]
    ring

end QKD.BB84.FiniteKey
