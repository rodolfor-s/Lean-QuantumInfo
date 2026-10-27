import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.InnerBudgetCorrectness
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabelGeneral
import QCryptLean.QKD.BB84.FiniteKey.Postselection.ProtocolMapCovariance
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RegisterTrick
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RegisterTrickGeneral
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.CovariantBound
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-!
# Bell covariance of the agree and differ
pass blocks

The test selecting equal or different reconciled strings is preserved by Bell relabelling.
Consequently each restricted Kraus family has the same output relabelling as the pass family.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics QKD.BB84.Model QKD.BB84.Measurement
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker

noncomputable section

namespace QKD.BB84.FiniteKey

open scoped Classical in
/-- Bell relabelling preserves whether the reconciled key strings differ. -/
theorem siftedKeyStringsDiffer_bellStringRelabel
    {n leakEC : ℕ}
    (peSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (h : Fin n → Fin 4)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (ω : Signals n) :
    siftedKeyStringsDiffer peSel ec (bellOutcomePerm n h ω) =
      siftedKeyStringsDiffer peSel ec ω := by
  simp only [siftedKeyStringsDiffer, aliceKeyString_bellStringRelabel,
    bobKeyString_bellStringRelabel, hdec, ne_eq, add_left_inj]

open scoped Classical in
/-- The real agree Kraus family intertwines Bell twirling and output relabelling. -/
theorem realPassAgreeKraus_bellTwirl_intertwining
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Signals n)) :
    realPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.2 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          realPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := siftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.2
  have hbase := announcedPassKraus_bellTwirl_intertwining
    E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : siftedKeyStringsDiffer peSel ec idx.2 = true
  · simp [realPassAgreeKraus, peAnnounceOutcomeReindex,
      hgate, hd]
  · simpa [realPassAgreeKraus, peAnnounceOutcomeReindex,
      hgate, hd] using! hbase

open scoped Classical in
/-- The real differ Kraus family intertwines Bell twirling and output relabelling. -/
theorem realPassDifferKraus_bellTwirl_intertwining
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Signals n)) :
    realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.2 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := siftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.2
  have hbase := announcedPassKraus_bellTwirl_intertwining
    E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : siftedKeyStringsDiffer peSel ec idx.2 = true
  · simpa [realPassDifferKraus, peAnnounceOutcomeReindex,
      hgate, hd] using! hbase
  · simp [realPassDifferKraus, peAnnounceOutcomeReindex,
      hgate, hd]

open scoped Classical in
/-- The ideal agree Kraus family intertwines Bell twirling and output relabelling. -/
theorem idealPassAgreeKraus_bellTwirl_intertwining
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : (Signals n) × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    idealPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.1 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          idealPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (peAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := siftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.1
  have hbase := announcedIdealPassKraus_bellTwirl_intertwining
    E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : siftedKeyStringsDiffer peSel ec idx.1 = true
  · simp [idealPassAgreeKraus, peAnnounceIdealReindex, hgate, hd]
  · simpa [idealPassAgreeKraus, peAnnounceIdealReindex, hgate, hd] using hbase

open scoped Classical in
/-- The ideal differ Kraus family intertwines Bell twirling and output relabelling. -/
theorem idealPassDifferKraus_bellTwirl_intertwining
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : (Signals n) × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.1 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (peAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := siftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.1
  have hbase := announcedIdealPassKraus_bellTwirl_intertwining
    E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : siftedKeyStringsDiffer peSel ec idx.1 = true
  · simpa [idealPassDifferKraus, peAnnounceIdealReindex, hgate, hd] using hbase
  · simp [idealPassDifferKraus, peAnnounceIdealReindex, hgate, hd]

open scoped Classical in
/-- Each pass-block difference carries Bell twirling to a unitary output relabelling. -/
theorem passBlockDelta_bellTwirl_covariant
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (g : Fin n → Fin 4) :
    ∃ W : Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit),
      Wᴴ * W = 1 ∧
      ∀ M : Op (Signals n),
        passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
            peSel xSel leakEC ec Q δ
            (signalBellUnitary g * M * (signalBellUnitary g)ᴴ) =
          W * passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
              peSel xSel leakEC ec Q δ M * Wᴴ := by
  let : DecidableEq Unit := Classical.decEq _
  obtain ⟨⟨πsyn, hsyn⟩, hdec⟩ := hec (bellTwirlKeyError peSel g)
  let h := siftedTwirlString peSel xSel g
  have hkey : bellTwirlKeyError peSel h = bellTwirlKeyError peSel g :=
    bellTwirlKeyError_siftedTwirlString peSel xSel g
  have hsyn' : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a) := by
    rw [hkey]
    exact hsyn
  have hdec' : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h := by
    rw [hkey]
    exact hdec
  let U := (signalBellUnitary h ⊗ₖ (1 : Op Unit))
  let W := ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op Unit))
  let KR := if differ then realPassDifferKraus Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q
    else realPassAgreeKraus Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q
  let KI := if differ then idealPassDifferKraus Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q
    else idealPassAgreeKraus Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q
  have hR : ∀ A, krausMap KR (U * A * Uᴴ) = W * krausMap KR A * Wᴴ := by
    intro A
    have hinter : ∀ idx, KR idx * U = bellTwirlSign n h idx.2 •
        (W * KR (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
      intro idx
      cases differ
      · exact realPassAgreeKraus_bellTwirl_intertwining
          Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
      · exact realPassDifferKraus_bellTwirl_intertwining
          Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
    rw [krausMap_conj_of_phased_intertwining KR
      (fun idx => KR (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) U W
      (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      hinter A, krausMap_comp_equiv KR (peAnnounceOutcomeReindex n ℓ ℓEV peSel h)]
  have hI : ∀ A, krausMap KI (U * A * Uᴴ) = W * krausMap KI A * Wᴴ := by
    intro A
    have hinter : ∀ idx, KI idx * U = bellTwirlSign n h idx.1 •
        (W * KI (peAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
      intro idx
      cases differ
      · exact idealPassAgreeKraus_bellTwirl_intertwining
          Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
      · exact idealPassDifferKraus_bellTwirl_intertwining
          Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
    rw [krausMap_conj_of_phased_intertwining KI
      (fun idx => KI (peAnnounceIdealReindex n ℓ ℓEV peSel h idx)) U W
      (fun idx => bellTwirlSign n h idx.1) (fun idx => bellTwirlSign_unit n h idx.1)
      hinter A, krausMap_comp_equiv KI (peAnnounceIdealReindex n ℓ ℓEV peSel h)]
  refine ⟨W, ?_, ?_⟩
  · simp only [W, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      conjTranspose_mul_peAnnounceBellRelabelUnitary, Matrix.one_mul, one_kronecker_one]
    ext i j
    simp [Matrix.one_apply]
  · intro M
    let meas := (mapTensorId (classicalMap (id : Signals n → Signals n)) Unit).comp
      (siftedConjAfterPre Unit (unitRegisterEmbed n) peSel xSel)
    have hmeas : meas (signalBellUnitary g * M * (signalBellUnitary g)ᴴ) =
        U * meas M * Uᴴ := by
      dsimp [meas, siftedConjAfterPre]
      rw [isBellTwirlCovariantPre_unitRegisterEmbed n g M,
        siftedConjChannel_bellTwirl_conj, measurementChannel_bellTwirl_outcomeRelabel]
    have hexpand : ∀ A, passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ A =
          (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
              krausMap KR (meas A) -
            (1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
              krausMap KI (meas A) := by
      intro A
      cases differ <;> rfl
    rw [hexpand, hexpand, hmeas, hR, hI, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

open scoped Classical in
/-- Each announced pass block is Bell invariant with every finite reference retained. -/
theorem traceNorm_passDelta_twirl
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (hec : ec.IsTranslationEquivariant)
    (R : Type*) [Fintype R] (g : Fin n → Fin 4) (M : Op (Signals n × R)) :
    traceNorm (mapTensorId
      (symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) R
      ((signalBellUnitary g ⊗ₖ (1 : Op R)) * M * (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ)) =
      traceNorm (mapTensorId
        (symPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) R M) := by
  classical
  let base := passBlockDelta Unit differ (m := m) ℓ ℓEV (unitRegisterEmbed n)
    peSel xSel leakEC ec Q δ
  let F := fun π => base.comp (permConjLin π)
  let L := siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC
  let U := signalBellUnitary g
  let Mtw := (U ⊗ₖ (1 : Op R)) * M * (U ⊗ₖ (1 : Op R))ᴴ
  have hs (π : Equiv.Perm (Fin n)) :
      traceNorm (mapTensorId (L π) R (mapTensorId (F π) R Mtw)) =
        traceNorm (mapTensorId (L π) R (mapTensorId (F π) R M)) := by
    rw [traceNorm_mapTensorId_siftedPEAnnounceLinearEveVisible,
      traceNorm_mapTensorId_siftedPEAnnounceLinearEveVisible]
    obtain ⟨W, hW, hcov⟩ := passBlockDelta_bellTwirl_covariant
      differ n m ℓ ℓEV Q δ peSel xSel leakEC ec hec (g ∘ π.symm)
    have hi (A : Op (Signals n)) : F π (U * A * Uᴴ) = W * F π A * Wᴴ := by
      have hp : permConjLin π (U * A * Uᴴ) = signalBellUnitary (g ∘ π.symm) *
          permConjLin π A * (signalBellUnitary (g ∘ π.symm))ᴴ := by
        have hg := tensorPermutation_conj_piTensorProduct π (fun i => signalBilateralPauli (g i))
        change tensorPermutation π * U * (tensorPermutation π)ᴴ =
          signalBellUnitary (g ∘ π.symm) at hg
        rw [← hg]
        simp only [permConjLin, LinearMap.coe_mk, AddHom.coe_mk, permutationRepresentation,
          conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
          ← Matrix.mul_assoc (tensorPermutation π)ᴴ (tensorPermutation π),
          (tensorPermutation_unitary π).1, Matrix.one_mul]
      change base (permConjLin π (U * A * Uᴴ)) = _
      rw [hp]
      exact hcov _
    have hc := mapTensorId_conj_eq_of_covariance (F π) (Matrix.conjLinearMap W) U hi M
    rw [hc, mapTensorId_conjLinearMap, Matrix.conjLinearMap_apply]
    apply traceNorm_isometry_conj
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
    ext i j
    simp [Matrix.one_apply]
  change traceNorm (mapTensorId ((n.factorial : ℂ)⁻¹ • ∑ π, (L π).comp (F π)) R Mtw) =
    traceNorm (mapTensorId ((n.factorial : ℂ)⁻¹ • ∑ π, (L π).comp (F π)) R M)
  simp only [mapTensorId_smul, mapTensorId_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    mapTensorId_comp, LinearMap.comp_apply, traceNorm_smul]
  rw [traceNorm_announceEve_sum, traceNorm_announceEve_sum]
  exact congrArg (_ * ·) (Finset.sum_congr rfl fun π _ => hs π)

end QKD.BB84.FiniteKey

end
