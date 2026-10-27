import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AnnouncedChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.InnerBudgetCorrectness
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CKRConsequences
import QCryptLean.Quantum.Channels.CKRReference
import QCryptLean.Quantum.Channels.CKRReferenceBound
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondAlgebra
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.PostselectionBound
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Metrics.TraceNormSum
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-!
# The agree and differ parts of the BB84 real-ideal difference

Each block restricts the Kraus outcomes according to equality of the reconciled strings.
`passBlockDelta` is the base difference, and `symPassBlockDelta` averages it over
announced input permutations. The sum of the two averaged blocks equals the full real-ideal
difference exactly; their output supports need not be disjoint.

The agree block has CKR trace norm at most twice the local PE acceptance weight. The differ
block has diamond norm at most `2 * 2^(-ℓEV)` without postselection or reference symmetry.
Both announced blocks are permutation covariant and preserve conjugate transpose.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics QKD.BB84.Model QKD.BB84.Measurement
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

variable (E : Type*) [Fintype E]

/-- The real-ideal pass difference on agreeing or differing reconciled strings. -/
noncomputable def passBlockDelta
    (differ : Bool)
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  if differ then
    announcedEveRealDiffer E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ -
      announcedEveIdealDiffer E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ
  else
    announcedEveRealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ -
      announcedEveIdealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ

/-- The general-`m` real agree pass channel is completely positive (a nonnegatively-scaled Kraus
map after a CP map — zeroing part of a Kraus family leaves a Kraus family). -/
theorem isCompletelyPositive_announcedEveRealAgree
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveRealAgree E (m := m) ℓ ℓEV pre peSel
          xSel leakEC
        ec Q δ)) := by
  classical
  classical
  unfold announcedEveRealAgree
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

/-- The general-`m` ideal agree pass channel is completely positive. -/
theorem isCompletelyPositive_announcedEveIdealAgree
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveIdealAgree E (m := m) ℓ ℓEV pre peSel
          xSel leakEC
        ec Q δ)) := by
  classical
  classical
  unfold announcedEveIdealAgree
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

/-- The announced average of one pass-block difference over input round permutations. -/
noncomputable def symPassBlockDelta
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    Operation (Signals n)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit) :=
  (n.factorial : ℂ)⁻¹ •
    ∑ π : Equiv.Perm (Fin n),
      (siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC π).comp
        ((passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ).comp (permConjLin π))

/-- The symmetrized real-ideal difference is exactly the sum of its two pass blocks. -/
theorem symReal_sub_symIdeal_eq_add_passBlocks
    (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec +
        symPassBlockDelta true n m ℓ ℓEV Q δ peSel xSel leakEC ec := by
  classical
  have hbase := QKD.BB84.Model.Announced.WithEve.real_sub_ideal_eq_pass_sub
    Unit (m := m) ℓ ℓEV (unitRegisterEmbed n) peSel xSel leakEC ec Q δ
  rw [announcedEveRealPass_eq_agree_add_differ,
    announcedEveIdealPass_eq_agree_add_differ] at hbase
  have hsplit :
      (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
          Q δ).realProtocolMap (E := Unit) -
        (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
          Q δ).idealProtocolMap (E := Unit)).comp
        (siftedConjAfterPre Unit (unitRegisterEmbed n) peSel xSel)) =
      passBlockDelta Unit false (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ +
        passBlockDelta Unit true (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ := by
    rw [hbase]
    simp only [passBlockDelta, Bool.false_eq_true, ite_false, ite_true]
    abel
  unfold symReal symIdeal symRealEveVisible symIdealEveVisible symPassBlockDelta
  rw [← smul_sub, ← Finset.sum_sub_distrib, ← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
  simp only [← LinearMap.comp_add, ← LinearMap.add_comp]
  rw [← hsplit]
  let A := siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC π
  let R := (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
    Q δ).realProtocolMap (E := Unit)
  let I := (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
    Q δ).idealProtocolMap (E := Unit)
  let T := (siftedConjAfterPre Unit (unitRegisterEmbed n) peSel xSel).comp
    (permConjLin π)
  change A.comp (R.comp T) - A.comp (I.comp T) = A.comp ((R - I).comp T)
  exact (LinearMap.comp_sub (I.comp T) (R.comp T) A).symm.trans
    (congrArg A.comp (LinearMap.sub_comp T R I).symm)

/-- Paired reference permutation invariance transfers a base pass-block bound to its average. -/
theorem ckrTraceNorm_symPassBlockDelta_le
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (τ : DensityOp (Signals n × Signals n))
    (hτ : IsPairedPermInvariant τ) :
    ckrTraceNorm
        (symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) τ ≤
      ckrTraceNorm
        (passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ) τ := by
  classical
  exact ckrTraceNorm_symAverage_le_of_baseScheme_bound
    _ _ (fun π => isChannel_siftedPEAnnounceLinearEveVisible Unit
      n m ℓ ℓEV peSel leakEC π) _ τ hτ rfl le_rfl

/-- Each announced pass-block difference is permutation covariant. -/
theorem permutationCovariant_symPassBlockDelta
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    PermutationCovariant
      (symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) :=
  permutationCovariant_symAnnouncedMap Unit n m ℓ ℓEV peSel leakEC _

/-- Each announced pass-block difference preserves conjugate transpose. -/
theorem symPassBlockDelta_conjTranspose
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    ∀ M : Op (Signals n),
      symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec M.conjTranspose =
        (symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec M).conjTranspose := by
  classical
  have hbase : ∀ M : Op (Signals n),
      passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ Mᴴ =
        (passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
          peSel xSel leakEC ec Q δ M)ᴴ := by
    cases differ
    · exact IsCompletelyPositive.sub_conjTranspose
        (isCompletelyPositive_announcedEveRealAgree Unit
          ℓ ℓEV _ (isChannel_unitRegisterEmbed n) peSel xSel leakEC ec Q δ)
        (isCompletelyPositive_announcedEveIdealAgree Unit
          ℓ ℓEV _ (isChannel_unitRegisterEmbed n) peSel xSel leakEC ec Q δ)
    · exact IsCompletelyPositive.sub_conjTranspose
        (isCompletelyPositive_announcedEveRealDiffer Unit
          ℓ ℓEV _ (isChannel_unitRegisterEmbed n) peSel xSel leakEC ec Q δ)
        (isCompletelyPositive_announcedEveIdealDiffer Unit
          ℓ ℓEV _ (isChannel_unitRegisterEmbed n) peSel xSel leakEC ec Q δ)
  intro M
  simp only [symPassBlockDelta, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    star_inv₀, star_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  rw [(isChannel_permConjLin π).1.conjTranspose_apply, hbase,
    (isChannel_siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV
      peSel leakEC π).1.conjTranspose_apply]

/-- The agree-block trace norm is at most twice the local PE acceptance weight. -/
theorem ckrTraceNorm_agreeBlock_le_two_mul_tauWeight [DecidableEq E]
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R₀ : Type*} [Fintype R₀]
    (τ : DensityOp (Signals n × R₀)) :
    ckrTraceNorm
        (passBlockDelta E false (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ) τ ≤
      2 * siftedEveVisiblePEPassWeight
        E pre hpre peSel xSel Q δ τ := by
  classical
  let R := announcedEveRealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ
  let I := announcedEveIdealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ
  have hR := (isCompletelyPositive_announcedEveRealAgree E (m := m)
    ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ).mapTensorId (Z := R₀) |>.posSemidef τ.posSemidef
  have hI := (isCompletelyPositive_announcedEveIdealAgree E (m := m)
    ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ).mapTensorId (Z := R₀) |>.posSemidef τ.posSemidef
  have htrace (Φ Ψ : Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E))
      (hΨ : IsCompletelyPositive Ψ) :
      (mapTensorId Φ R₀ τ.toOp).trace.re ≤ (mapTensorId (Φ + Ψ) R₀ τ.toOp).trace.re := by
    rw [mapTensorId_add, LinearMap.add_apply, Matrix.trace_add, Complex.add_re]
    exact le_add_of_nonneg_right (Complex.nonneg_iff.mp
      (hΨ.mapTensorId.posSemidef τ.posSemidef).trace_nonneg).1
  have hRle : (mapTensorId R R₀ τ.toOp).trace.re ≤
      siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ := by
    apply le_trans _ (realPassOutput_trace_re_le_tauLocalPEAcceptedWeight E (m := m)
      ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ τ)
    unfold siftedPEAnnounceEveVisibleRealPassOutput
    rw [announcedEveRealPass_eq_agree_add_differ]
    exact htrace R _
      (isCompletelyPositive_announcedEveRealDiffer E ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ)
  have hIle : (mapTensorId I R₀ τ.toOp).trace.re ≤
      siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ := by
    apply le_trans _ (idealPassOutput_trace_re_le_tauLocalPEAcceptedWeight E (m := m)
      ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ τ)
    unfold siftedPEAnnounceEveVisibleIdealPassOutput
    rw [announcedEveIdealPass_eq_agree_add_differ]
    exact htrace I _
      (isCompletelyPositive_announcedEveIdealDiffer E ℓ ℓEV pre hpre peSel xSel leakEC ec Q δ)
  change traceNorm (mapTensorId (R - I) R₀ τ.toOp) ≤ _
  rw [mapTensorId_sub, LinearMap.sub_apply]
  calc
    traceNorm (mapTensorId R R₀ τ.toOp - mapTensorId I R₀ τ.toOp) ≤
        traceNorm (mapTensorId R R₀ τ.toOp) + traceNorm (mapTensorId I R₀ τ.toOp) :=
      traceNorm_sub_le _ _
    _ = (mapTensorId R R₀ τ.toOp).trace.re + (mapTensorId I R₀ τ.toOp).trace.re := by
      rw [traceNorm_of_posSemidef _ hR, traceNorm_of_posSemidef _ hI]
    _ ≤ _ := by linarith only [hRle, hIle]

/-- The differ block costs twice the verification collision probability without postselection. -/
theorem diamondNorm_symDiffer_le_two_mul_pow_neg
    (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    diamondNorm (symPassBlockDelta true n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  classical
  apply diamondNorm_le_of_density_bound _
    (symPassBlockDelta_conjTranspose
      true n m ℓ ℓEV Q δ peSel xSel leakEC ec) _ (by positivity)
  intro τ
  let B := 2 * (2 : ℝ) ^ (-(ℓEV : ℝ))
  let base := passBlockDelta Unit true (m := m) ℓ ℓEV (unitRegisterEmbed n) peSel xSel leakEC ec Q δ
  let announce := siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC
  have hsummand : ∀ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId ((announce π).comp (base.comp (permConjLin π)))
        (Signals n) τ.toOp) ≤ B := by
    intro π
    have hpre := (isChannel_unitRegisterEmbed n).comp (isChannel_permConjLin (X := Signal) π)
    have hbound :=
      ckrTraceNorm_announcedEveDiffer_sub_le_two_mul_pow_neg Unit (m := m) ℓ ℓEV
        ((unitRegisterEmbed n).comp (permConjLin π))
        hpre peSel xSel leakEC ec Q δ τ
    have hbase : ckrTraceNorm (base.comp (permConjLin π)) τ ≤ B := by
      simpa only [base, passBlockDelta, ite_true,
        announcedEveRealDiffer,
        announcedEveIdealDiffer, siftedConjAfterPre,
        LinearMap.sub_comp, LinearMap.comp_assoc] using hbound
    exact (ckrTraceNorm_comp_le_of_isChannel (announce π)
      (isChannel_siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC π)
      (base.comp (permConjLin π)) τ).trans hbase
  change traceNorm (mapTensorId ((n.factorial : ℂ)⁻¹ •
    ∑ π : Equiv.Perm (Fin n), (announce π).comp (base.comp (permConjLin π)))
      (Signals n) τ.toOp) ≤ B
  rw [mapTensorId_smul, mapTensorId_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    traceNorm_smul]
  have hsum : (∑ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId ((announce π).comp (base.comp (permConjLin π)))
        (Signals n) τ.toOp)) ≤ (n.factorial : ℝ) * B := by
    calc
      _ ≤ ∑ _π : Equiv.Perm (Fin n), B := Finset.sum_le_sum (fun π _ => hsummand π)
      _ = _ := by simp [Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ ‖(n.factorial : ℂ)⁻¹‖ * ((n.factorial : ℝ) * B) :=
      mul_le_mul_of_nonneg_left ((traceNorm_sum_le Finset.univ _).trans hsum) (norm_nonneg _)
    _ = B := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp

/-- A negative-width or negative-upper-edge acceptance interval rejects every outcome, so the
real and ideal channels coincide. -/
theorem symReal_eq_symIdeal_of_empty_acceptance
    (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (hempty : δ < 0 ∨ Q + δ < 0) :
    symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec := by
  classical
  have hpass (t : KeyHashSeed n ℓEV peSel) (ω : Signals n) :
      siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = false := by
    have habs (a : ℝ) (ha : 0 ≤ a) : ¬ |a - Q| ≤ δ := by
      intro h
      rcases hempty with hδ | hQ
      · linarith [abs_nonneg (a - Q)]
      · linarith [(le_abs_self (a - Q)).trans h]
    have hZ : ¬ |(siftedZTestErrorCount peSel xSel ω : ℝ) /
        siftedZTestSampleSize peSel xSel - Q| ≤ δ := habs _ (by positivity)
    simp [siftedLocalPEAndEVPassed, siftedLocalPETestPassed, hZ]
  have hmaps :
      (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
        Q δ).realProtocolMap (E := Unit) =
      (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
        Q δ).idealProtocolMap (E := Unit) := by
    dsimp only [siftedPEAnnounceEveVisibleProtocol]
    rw [Announced.real_eq_krausMap, Announced.ideal_eq_krausMap]
    congr 1
    ext A i j
    simp [krausMap,
      Announced.passKraus,
      Announced.idealPassKraus,
     hpass]
  simp only [symReal, symIdeal, symRealEveVisible, symIdealEveVisible, hmaps]

/-- Correctness is charged directly, while CKR postselection lifts the agree-block trace distance.
The full real/ideal distance uses the distinguishing-advantage convention. -/
theorem half_mul_diamondNorm_sub_le_correctness_add
    (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    (1 / 2) * diamondNorm
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      (2 : ℝ) ^ (-(ℓEV : ℝ)) +
        (Nat.choose (n + 4 ^ 2 - 1) (4 ^ 2 - 1) : ℝ) *
          ((1 / 2) * ckrTraceNorm
            (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
            (ckrDeFinettiCanonicalPurification Signal n)) := by
  classical
  have hagree := diamondNorm_le_symDim_mul_ckrTraceNorm (X := Signal)
    (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (permutationCovariant_symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (symPassBlockDelta_conjTranspose
      false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (ckrDeFinettiCanonicalPurification Signal n)
    (isCKRDeFinettiPurification_canonical Signal n)
  simp only [Signal, Bit, Fintype.card_prod, Fintype.card_fin] at hagree
  norm_num only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hagree ⊢
  rw [Nat.add_sub_assoc (by omega : 1 ≤ 16)]
  rw [symReal_sub_symIdeal_eq_add_passBlocks]
  have hsum := add_le_add hagree
    (diamondNorm_symDiffer_le_two_mul_pow_neg n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  have h := (diamondNorm_add_le _ _).trans (hsum.trans_eq (add_comm _ _))
  have hhalf := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hhalf.trans_eq (by ring)

end QKD.BB84.FiniteKey

end
