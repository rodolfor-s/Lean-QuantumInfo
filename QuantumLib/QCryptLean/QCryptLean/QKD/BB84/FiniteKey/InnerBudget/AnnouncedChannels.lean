import QCryptLean.InfoTheory.Postselection.ErrorVerificationCorrectness
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Average
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # Normalization and joint correctness of the announced BB84 channels

All retained references are finite types. Correctness bounds the joint mass of
acceptance and disagreement, with the same inverse verification-key-space charge.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry Matrix
open QKD.BB84.Model QKD.BB84.Measurement
open scoped Kronecker ComplexOrder

/-- Recording the sampled permutation preserves the complete input operator. -/
theorem isChannel_siftedPEAnnounceLinear (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    IsChannel (siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm) := by
  classical
  let X := KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)
  let : DecidableEq X := Classical.decEq _
  let K : Matrix (X × Equiv.Perm (Fin n)) X ℂ :=
    fun p x => if p.1 = x ∧ p.2 = perm then 1 else 0
  have hk : IsChannel (Matrix.conjLinearMap K) := by
    apply (isChannel_conjLinearMap_iff _).mpr
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply]
    by_cases hij : i = j <;>
      simp [K, Fintype.sum_prod_type, ite_and, hij, apply_ite, eq_comm]
  have he : siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm =
      (Matrix.reindexLinearEquiv ℂ ℂ (KeyedOutput.prodEquiv ℓ _ _) (KeyedOutput.prodEquiv ℓ _ _)
        ).toLinearMap.comp (Matrix.conjLinearMap K) := by
    apply LinearMap.ext
    intro A
    change Matrix.reindex (KeyedOutput.prodEquiv ℓ _ _) (KeyedOutput.prodEquiv ℓ _ _)
      (A ⊗ₖ permAnnounceProjector n perm) = Matrix.reindex _ _ (K * A * Kᴴ)
    apply congrArg (Matrix.reindex (KeyedOutput.prodEquiv ℓ _ _) (KeyedOutput.prodEquiv ℓ _ _))
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kroneckerMap_apply]
    by_cases hp : p.2 = perm <;> by_cases hq : q.2 = perm <;>
      simp_all [K, permAnnounceProjector, Matrix.single_apply, ite_and, apply_ite, eq_comm]
  rw [he]
  exact (isChannel_reindex _).comp hk

variable (E : Type*) [Fintype E]

/-- Permutation recording remains a channel with an arbitrary retained Eve register. -/
theorem isChannel_siftedPEAnnounceLinearEveVisible (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    IsChannel (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC perm) :=
  (isChannel_siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm).mapTensorId

open scoped Classical in
/-- A normalized base experiment stays normalized under announced permutation averaging. -/
private theorem isChannel_announce_average (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (base : Operation (Signals n × E)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E))
    (hbase : IsChannel base) (pre : Operation (Signals n) (Signals n × E))
    (hpre : IsChannel pre) :
    IsChannel ((n.factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n),
      (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π).comp
        (base.comp ((siftedConjAfterPre E pre peSel xSel).comp (permConjLin π)))) := by
  have h := IsChannel.uniformAverage _ (fun π : Equiv.Perm (Fin n) =>
    (isChannel_siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π).comp
      (hbase.comp ((isChannel_siftedConjAfterPre E pre hpre peSel xSel).comp
        (isChannel_permConjLin π))))
  simpa only [Fintype.card_perm, Fintype.card_fin] using h

/-- The real symmetrized model is a channel, including zero rounds. -/
theorem isChannel_symReal (n m ℓ ℓEV : ℕ) (Q δ : ℝ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    IsChannel (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec) := by
  classical
  exact isChannel_announce_average Unit n m ℓ ℓEV peSel xSel leakEC _
    ((Announced.isChannel_real Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp
      (isChannel_classicalMap id).mapTensorId) _ (isChannel_unitRegisterEmbed n)

/-- The ideal symmetrized model is a channel, including zero rounds. -/
theorem isChannel_symIdeal (n m ℓ ℓEV : ℕ) (Q δ : ℝ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    IsChannel (symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) := by
  classical
  exact isChannel_announce_average Unit n m ℓ ℓEV peSel xSel leakEC _
    ((Announced.isChannel_ideal Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp
      (isChannel_classicalMap id).mapTensorId) _ (isChannel_unitRegisterEmbed n)

/-- The real-minus-ideal model preserves adjoints. -/
theorem symReal_sub_symIdeal_conjTranspose (n m ℓ ℓEV : ℕ) (Q δ : ℝ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (A : Op (Signals n)) :
    (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
      symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) Aᴴ =
      ((symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) A)ᴴ :=
  (isChannel_symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec).1.sub_conjTranspose
    (isChannel_symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec).1 A

variable [DecidableEq E]

/-- The measured outcome projector reads the corresponding diagonal block before measurement. -/
lemma trace_outcomeProjector_mul_measurementChannel (n : ℕ)
    (M : Op (Signals n × E)) (ω : Signals n) :
    ((Matrix.single ω ω (1 : ℂ) ⊗ₖ (1 : Op E)) *
      mapTensorId (classicalMap (id : Signals n → Signals n)) E M).trace =
      ∑ r : E, M (ω, r) (ω, r) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.single_apply, Fintype.sum_prod_type, mapTensorId_apply, classicalMap,
    krausMap, Matrix.sum_apply, ite_and]

/-- Sifting after the pre-channel gives the rotated retained-register state. -/
lemma siftedConjAfterPre_apply_densityOp {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) :
    siftedConjAfterPre E pre peSel xSel ρ.toOp =
      (siftedRotatedPreOutput E pre hpre peSel xSel ρ).toOp := by
  classical
  simp only [siftedConjAfterPre, LinearMap.comp_apply, siftedConjChannel,
    Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, siftedRotatedPreOutput,
    UnitaryOp.evolve, IsChannel.applyDensity]
  congr 2 <;> ext i j <;> simp [kroneckerMap_apply, Matrix.one_apply]

omit [DecidableEq E] in
/-- Measuring the sifted output of a channel is completely positive. -/
theorem isCompletelyPositive_measurement_comp_siftedConjAfterPre {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) :
    IsCompletelyPositive ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel)) :=
  ((isChannel_classicalMap id).mapTensorId.comp
    (isChannel_siftedConjAfterPre E pre hpre peSel xSel)).1

/-- A pass Kraus family with outcome-projector adjoint products has the exact gated trace. -/
lemma trace_passOutput_eq_sum_ite {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool)
    {Y I : Type*} [Fintype Y] [Fintype I]
    (K : I → Matrix Y (Signals n × E) ℂ)
    (c : ℂ) (gate : I → Bool) (ωof : I → Signals n)
    (hKK : ∀ k, (K k)ᴴ * K k =
      if gate k then Matrix.single (ωof k) (ωof k) 1 ⊗ₖ (1 : Op E) else 0)
    {R : Type*} [Fintype R] (τ : DensityOp (Signals n × R)) :
    (mapTensorId ((c • krausMap K).comp
      ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
        (siftedConjAfterPre E pre peSel xSel))) R τ.toOp).trace =
      c * ∑ k, if gate k then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight (ωof k)).trace : ℂ)
        else 0 := by
  classical
  rw [← Matrix.trace_partialTraceRight, partialTraceRight_mapTensorId]
  change (((c • krausMap K).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))) τ.partialTraceRight.toOp).trace = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    siftedConjAfterPre_apply_densityOp E pre hpre, LinearMap.smul_apply,
    Matrix.trace_smul, smul_eq_mul, trace_krausMap]
  congr 1
  simp only [hKK, Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : gate k = true
  · rw [ite_eq_left hg, ite_eq_left hg, trace_outcomeProjector_mul_measurementChannel]
    have he : (siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight (ωof k)).toOp.trace =
        ∑ r : E, (siftedRotatedPreOutput E pre hpre peSel xSel τ.partialTraceRight).toOp
          (ωof k, r) (ωof k, r) := rfl
    rw [← he]
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp
        (siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight (ωof k)
          ).posSemidef.trace_nonneg).2.symm
  · simp [hg]

/-- The reference-side PE accept weight is the accepted weight of its signal marginal. -/
theorem siftedEveVisiblePEPassWeight_eq_sum_marginal {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    {R : Type*} [Fintype R] (τ : DensityOp (Signals n × R)) :
    siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ =
      ∑ ω : Signals n, if siftedLocalPETestPassed peSel xSel δ Q ω then
        (siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace else 0 := by
  unfold siftedEveVisiblePEPassWeight
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hg : siftedLocalPETestPassed peSel xSel δ Q ω = true
  · change (if siftedLocalPETestPassed peSel xSel δ Q ω then
      siftedTauEveRefConditioned E pre hpre peSel xSel τ ω else SubDensityOp.zero).trace = _
    rw [ite_eq_left hg, ite_eq_left hg]
    unfold SubDensityOp.trace
    rw [← Matrix.trace_partialTraceRight, partialTraceRight_conditioned_eq]
  · simp [postMeasurementCQSiftedLocalPEPassFilter, hg, SubDensityOp.zero, SubDensityOp.trace]

/-- **Termwise accept-test shrinkage.**  Each accept-gated block weight is at most the corresponding
    PE-gated one, because accepting implies PE-passing
    (`siftedLocalPETestPassed_of_siftedLocalPEAndEVPassed`) and the blocks are positive. -/
lemma ite_peAndEVPassed_le_ite_pePassed {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (ℓEV : ℕ) (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ) (ρ : DensityOp (Signals n))
    (t : KeyHashSeed n ℓEV peSel) (ω : Signals n) :
    (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
        (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace else 0) ≤
      (if siftedLocalPETestPassed peSel xSel δ Q ω then
        (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace else 0) := by
  by_cases h : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true
  · rw [ite_eq_left h,
      ite_eq_left (siftedLocalPETestPassed_of_siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω h)]
  · rw [ite_eq_right h]
    split_ifs
    · exact (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace_nonneg
    · exact le_refl 0

/-!
### The correctness leg: the joint differ-and-accept mass
-/

/-- **The differ-and-accept weight**: the total Born mass, averaged uniformly over the announced
    error-verification seed, of the event

      "Alice's key string differs from Bob's reconciled key string AND the protocol accepts".

    This is the explicit protocol-level realization of the composable *correctness* event
    `Pr[S_A ≠ S_B ∧ accept]` of Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C.
    The per-outcome weight is the trace of the outcome-conditioned Eve block
    `siftedEveConditioned` — the Born weight of the round-outcome string `ω` after the LOCC
    sift and the attack — and the accept predicate is the channels' own test
    `siftedLocalPEAndEVPassed`.

    Only the error-verification seed is averaged: the differ event and the accept test are both
    independent of the privacy-amplification seed, so averaging over the full announced pair
    `KeyHashSeedPairEV` would give the same number.

    **Stated jointly, never conditionally.**  The conditional form `Pr[differ | accept]` is NOT
    bounded by `2^(−ℓEV)` —
    `InfoTheory.Postselection.ErrorVerification.conditional_correctness_fails` proves an instance
    where it equals `1` — so this charge must enter a security budget additively, not
    conditionally. -/
noncomputable def siftedEveVisibleDifferAcceptWeight {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre) (ℓEV : ℕ)
        (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) (ρ : DensityOp (Signals n)) : ℝ :=
  (1 / (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ)) *
    ∑ t : KeyHashSeed n ℓEV peSel, ∑ ω : Signals n,
      (if aliceKeyString peSel ω ≠
            ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) ∧
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true
        then (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace
        else 0)

open InfoTheory.Postselection.ErrorVerification in
/-- **The error-verification correctness bound**: for every attack, every input state and every
    error-correction scheme, the joint mass of "the key strings differ and the protocol accepts" is
    at most `2^(−ℓEV)`.  Nothing here constrains `ec`: the bound holds for an arbitrary decoder,
    because the accept test compares Alice's announced `ℓEV`-bit tag with the tag of whatever
    string Bob's decoder produced.

    The proof:
    1.  On the differ event, `evVerified ℓEV peSel ec t ω = true` is exactly the tag-collision
        event of the pair `(aliceKeyString ω, ec.decode (bobKeyString ω) (ec.syndrome …))`, and the
        PE conjunct is seed-free; so the accept test factors as
        `siftedLocalPETestPassed … ω && decide (hash t a =
        hash t b)` definitionally.
    2.  The seed average of the collision indicator against any sub-normalised outcome weight is
`errorVerification_outcome_joint_correctness_of_universal`,
        the outcome-indexed form of `errorVerification_joint_correctness_indexed` (it groups the
        outcomes into key pairs and applies that lemma at the induced pair law, whose sub-normalised
        hypotheses `(hp_nonneg) (hp_total : ∑ p ≤ 1)` the accept-branch weight supplies — its
        deficit is the abort mass).
    3.  Its universality hypothesis is discharged verbatim by
        `isTwoUniversal_aliceKeyHashFamily n ℓEV peSel` (`KeyHashEC.lean`), which is an EXACT
        per-row halving, so `δ = 1/|Fin (2^ℓEV)| = 2^(−ℓEV)` is attained rather than merely bounded.
    4.  Sub-normalisation of the ω-weights is
        `siftedPostMeasurementCQState_weight_eq_one` (they sum to `1`), and nonnegativity is
        `SubDensityOp.trace_nonneg`.

    **Scope: this is the scalar (mass) leg; the operator lift is**
    `ckrTraceNorm_announcedEveDiffer_sub_le_two_mul_pow_neg`
    (`InnerBudgetCorrectness.lean`), which charges the mass to the trace norm of the
    differ-and-accept block of the real/ideal channel difference.  Because this scalar statement
    quantifies over an arbitrary input density operator, the lift instantiates it at the attacked
    CKR marginal `τ.partialTraceB`; no τ-side (reference-carrying) twin of it is needed. -/
theorem siftedEveVisibleDifferAcceptWeight_le_two_rpow_neg {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre) (ℓEV : ℕ)
        (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) (ρ : DensityOp (Signals n)) :
    siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ ρ ≤
      (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  have hkey :=
    errorVerification_outcome_joint_correctness_of_universal
      (S := KeyBitString n peSel) (T := (Fin ℓEV → Fin 2))
      (Sd := KeyHashSeed n ℓEV peSel) (Ω := Signals n)
      (aliceKeyHashFamily n ℓEV peSel).hash
      (isTwoUniversal_aliceKeyHashFamily n ℓEV peSel)
      (fun ω => aliceKeyString peSel ω)
      (fun ω => ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω)))
      (fun ω => siftedLocalPETestPassed peSel xSel δ Q ω)
      (fun ω => (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace)
      (fun ω => SubDensityOp.trace_nonneg _)
      (siftedPostMeasurementCQState_weight_eq_one E pre hpre peSel xSel ρ).le
  have hcard : (1 : ℝ) / (Fintype.card ((Fin ℓEV → Fin 2)) : ℝ) = (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    push_cast
    ring
  rw [hcard] at hkey
  simp only [siftedEveVisibleDifferAcceptWeight, siftedLocalPEAndEVPassed,
    evVerified, verificationTag]
  exact hkey


/-- The `Bool` differ-and-accept test agrees with the `Prop` conjunction the scalar weight
    functional uses. -/
lemma ite_differAndAccept_eq {n : ℕ} (ℓEV : ℕ) (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (t : KeyHashSeed n ℓEV peSel)
    (ω : Signals n) (x : ℝ) :
    (if siftedKeyStringsDiffer peSel ec ω &&
        siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then x else 0) =
      (if aliceKeyString peSel ω ≠
            ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) ∧
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true then x else 0) :=
  if_congr (by simp [siftedKeyStringsDiffer]) rfl rfl

/-- The error-verification-seed sum of the differ-and-accept gated block weights is the seed
    cardinality times the differ-and-accept weight (of which it is the uniform average). -/
lemma sum_ite_differAndAccept_eq {n : ℕ} (ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (ρ : DensityOp (Signals n)) :
    ∑ t : KeyHashSeed n ℓEV peSel, ∑ ω : Signals n,
        (if siftedKeyStringsDiffer peSel ec ω &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
          ((siftedEveConditioned E pre hpre peSel xSel ρ ω).trace : ℝ) else 0) =
      (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ) *
        siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ ρ := by
  have hT : (0 : ℝ) < (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [siftedEveVisibleDifferAcceptWeight]
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl
    (fun ω _ => ite_differAndAccept_eq ℓEV peSel xSel ec δ Q t ω _))]
  field_simp

/-- The seed-PAIR sum of the differ-and-accept gated block weights is the seed-pair cardinality
    times the differ-and-accept weight: the privacy-amplification seed is a spectator. -/
lemma sum_sum_ite_differAndAccept_eq {n : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (ρ : DensityOp (Signals n)) :
    ∑ _s : KeyHashSeed n ℓ peSel, ∑ t : KeyHashSeed n ℓEV peSel,
        ∑ ω : Signals n,
        (if siftedKeyStringsDiffer peSel ec ω &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
          ((siftedEveConditioned E pre hpre peSel xSel ρ ω).trace : ℝ) else 0) =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ) *
        siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ ρ := by
  rw [Finset.sum_congr rfl (fun _ _ => sum_ite_differAndAccept_eq E ℓEV pre hpre peSel xSel ec
    Q δ ρ),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod]
  push_cast
  ring

end QKD.BB84.FiniteKey
