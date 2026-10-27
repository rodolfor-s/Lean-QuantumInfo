import QCryptLean.Math.LinearAlgebra.PermutationMatrix
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.ProtocolMapCovariance
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.SiftedAcceptTwirlInvariant
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Operators.Basic

/-!
# Bell relabelling of the complete announced output

The public flag and seed pair control a permutation of the remaining fields. Accepted keys
shift together; abort keys remain fixed. Tags shift using their announced verification seed,
and the syndrome permutation is supplied explicitly by the EC translation hypothesis.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators Quantum.Channels
open Quantum.Metrics QKD.BB84.Model QKD.BB84.Measurement
open QKD.BB84.Model.Announced
open scoped Kronecker ComplexConjugate

/-- The key, tag, syndrome and test fields, excluding the public flag and seed pair. -/
abbrev PEAnnouncePayload (n m ℓ ℓEV leakEC : ℕ) : Type :=
  (Bits ℓ × Bits ℓ) × ((Bits ℓEV × Bits leakEC) × Signals (min n m))

/-- Structural regrouping of the output into its control and payload fields. -/
def peOutDecode (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) ≃
      PEAnnounceControl n ℓ ℓEV peSel × PEAnnouncePayload n m ℓ ℓEV leakEC where
  toFun x := ((x.2.1, x.2.2.1.1.1), (x.1, ((x.2.2.1.1.2, x.2.2.1.2), x.2.2.2)))
  invFun y := (y.2.1, (y.1.1, (((y.1.2, y.2.2.1.1), y.2.2.1.2), y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The test outcomes relabel separately at their selected round indices. -/
def peBlockRelabelPerm {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    Equiv.Perm (Signals (min n m)) :=
  Equiv.piCongrRight fun j => bellKeyOutcomePermEquiv (h (peRoundIdx peSel j))

/-- The test-register action is pointwise. -/
theorem peBlockRelabelPerm_apply {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (u : Signals (min n m)) :
    peBlockRelabelPerm (m := m) peSel h u =
      fun j => bellKeyOutcomePerm (h (peRoundIdx peSel j)) (u j) := rfl

/-- Tag, syndrome and test announcements relabel on both acceptance branches. -/
def peAnnounceAnnouncementPerm {n m : ℕ} (ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (c : PEAnnounceControl n ℓ ℓEV peSel) :
    Equiv.Perm ((Bits ℓEV × Bits leakEC) × Signals (min n m)) :=
  ((keyHashShiftPerm c.2.2 (bellTwirlKeyError peSel h)).prodCongr πsyn).prodCongr
    (peBlockRelabelPerm (m := m) peSel h)

/-- The controlled payload permutation combines key and announcement actions. -/
def peAnnouncePayloadPerm {n m : ℕ} (ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (c : PEAnnounceControl n ℓ ℓEV peSel) :
    Equiv.Perm (PEAnnouncePayload n m ℓ ℓEV leakEC) :=
  (peAnnounceKeyPairPerm ℓ ℓEV peSel h c).prodCongr
    (peAnnounceAnnouncementPerm (m := m) ℓ ℓEV leakEC peSel h πsyn c)

/-- The full output action reads the public control and permutes its payload. -/
def peAnnounceBellRelabel (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC)) :
    Equiv.Perm (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)) :=
  (peOutDecode n m ℓ ℓEV peSel leakEC).symm.permCongr
    (Equiv.prodCongrRight (peAnnouncePayloadPerm ℓ ℓEV leakEC peSel h πsyn))

/-- On acceptance, both keys shift and all public announcements relabel. -/
theorem peAnnounceBellRelabel_passOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (kA kB : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Bits ℓEV)
    (syn : Bits leakEC) (p : Signals (min n m)) :
    peAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (pePassOutIndex n m ℓ ℓEV peSel leakEC kA kB st evTag syn p) =
      pePassOutIndex n m ℓ ℓEV peSel leakEC
        (keyHashShiftPerm st.1 (bellTwirlKeyError peSel h) kA)
        (keyHashShiftPerm st.1 (bellTwirlKeyError peSel h) kB) st
        (keyHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag)
        (πsyn syn) (peBlockRelabelPerm (m := m) peSel h p) := rfl

/-- On abort the key slots stay fixed while the public announcements relabel. -/
theorem peAnnounceBellRelabel_failOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Bits ℓEV)
    (syn : Bits leakEC) (p : Signals (min n m)) :
    peAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (peFailOutIndex n m ℓ ℓEV peSel leakEC st evTag syn p) =
      peFailOutIndex n m ℓ ℓEV peSel leakEC st
        (keyHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag)
        (πsyn syn) (peBlockRelabelPerm (m := m) peSel h p) := rfl

open scoped Classical in
/-- The permutation matrix for the inverse output action, used to pull back a relabelled row. -/
def peAnnounceBellRelabelUnitary (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC)) :
    Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)) :=
  Equiv.Perm.permMatrix ℂ (peAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn)

open scoped Classical in
/-- The output relabelling matrix is unitary. -/
theorem conjTranspose_mul_peAnnounceBellRelabelUnitary (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (h : Fin n → Fin 4)
    (πsyn : Equiv.Perm (Bits leakEC)) :
    (peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)ᴴ *
      peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn = 1 :=
  Equiv.Perm.permMatrix_conjTranspose_mul_self _

/-- The outcome test block follows its pointwise relabelling. -/
theorem peBlock_bellStringRelabel {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Signals n) :
    (partEquiv (m := m) peSel (bellOutcomePerm n h ω)).2 =
      peBlockRelabelPerm (m := m) peSel h (partEquiv (m := m) peSel ω).2 := by
  funext j
  simp only [peBlockRelabelPerm_apply, partEquiv_apply_snd]
  rfl

/-- The real accepted transcript follows the public output action. -/
theorem pePassOutIndex_bellStringRelabel {n m ℓ ℓEV leakEC : ℕ} (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    passOutputIndex n m ℓ ℓEV peSel leakEC ec st (bellOutcomePerm n h ω) =
      peAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) := by
  rw [passOutputIndex, passOutputIndex, peAnnounceBellRelabel_passOutIndex]
  rw [aliceKeyString_bellStringRelabel, bobKeyString_bellStringRelabel,
    hdec, hsyn, peBlock_bellStringRelabel, verificationTag_add_right,
    keyHash_add_right, keyHash_add_right]

/-- The abort transcript keeps its zero keys while the public fields follow their action. -/
theorem peFailOutIndex_bellStringRelabel {n m ℓ ℓEV leakEC : ℕ} (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    failOutputIndex n m ℓ ℓEV peSel leakEC ec st (bellOutcomePerm n h ω) =
      peAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) := by
  rw [failOutputIndex, failOutputIndex, peAnnounceBellRelabel_failOutIndex]
  rw [aliceKeyString_bellStringRelabel, hsyn, peBlock_bellStringRelabel,
    verificationTag_add_right]

open scoped Classical in
/-- **Real pass-branch per-Kraus covariance
at a general test-set size `m`.**
`K^{pass}_{st,ω} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) · K^{pass}_{st, h·ω}`. -/
theorem announcedPassKraus_bellTwirl_intertwining
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
    passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.2 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (idx.1, bellOutcomePerm n h idx.2)) := by
  obtain ⟨st, ω⟩ := idx
  have hguard : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellOutcomePerm n h ω) = siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    siftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · have hp' : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true := by rw [hguard]; exact hp
    simp only [passKraus,
    hp, hp', ite_true]
    rw [← mul_kronecker_mul, Matrix.mul_one, single_mul_bellTwirlUnitary, Matrix.smul_kronecker,
      ← mul_kronecker_mul, Matrix.mul_one, peAnnounceBellRelabelUnitary,
      Equiv.Perm.permMatrix_mul_single,
      pePassOutIndex_bellStringRelabel peSel ec h πsyn hsyn hdec st ω,
      Equiv.symm_apply_apply]
  · have hp' : ¬ (siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true) := by rw [hguard]; exact hp
    simp [passKraus,
     hp, hp']

open scoped Classical in
/-- **Fail-branch per-Kraus covariance at a
general test-set size `m`** (the branch shared by the
real and ideal maps).  `K^{fail}_{st,ω} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) · K^{fail}_{st, h·ω}`.  The
key slots are the zero key on both outcomes; the relabel is the identity on them, and only the
announcements move. -/
theorem announcedFailKraus_bellTwirl_intertwining
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
    failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.2 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (idx.1, bellOutcomePerm n h idx.2)) := by
  obtain ⟨st, ω⟩ := idx
  have hguard : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellOutcomePerm n h ω) = siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    siftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : ¬ (siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true)
  · have hp' : ¬ (siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true) := by rw [hguard]; exact hp
    simp only [failKraus]
    rw [ite_eq_left hp, ite_eq_left hp', ← mul_kronecker_mul, Matrix.mul_one,
      single_mul_bellTwirlUnitary,
      Matrix.smul_kronecker, ← mul_kronecker_mul, Matrix.mul_one,
      peAnnounceBellRelabelUnitary,
      Equiv.Perm.permMatrix_mul_single,
      peFailOutIndex_bellStringRelabel peSel ec h πsyn hsyn st ω, Equiv.symm_apply_apply]
  · have hp' : ¬ ¬ (siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true) := by rw [hguard]; exact hp
    simp [failKraus,
     hp, hp']

open scoped Classical in
/-- **Ideal pass-branch per-Kraus covariance
at a general test-set size `m`.**  The ideal Kraus
writes ONE fresh uniform key in both slots but keeps the same `ω`-dependent announcements as the
real pass, so it too carries the relabel, at the cost of translating the fresh key by the
privacy-amplification-seed shift: `K^{ideal}_{ω,k,st} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) ·
K^{ideal}_{h·ω, σ_{st.1} k, st}`. -/
theorem announcedIdealPassKraus_bellTwirl_intertwining
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
    idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q idx *
        (signalBellUnitary h ⊗ₖ (1 : Op E)) =
      bellTwirlSign n h idx.1 •
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
          idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q
            (bellOutcomePerm n h idx.1,
              keyHashShiftPerm idx.2.2.1 (bellTwirlKeyError peSel h) idx.2.1,
              idx.2.2)) := by
  obtain ⟨ω, k, st⟩ := idx
  have hguard : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellOutcomePerm n h ω) = siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    siftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · have hp' : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true := by rw [hguard]; exact hp
    simp only [idealPassKraus,
    QKD.BB84.Model.Announced.idealPassOutputIndex, hp, hp', ite_true]
    rw [← mul_kronecker_mul, Matrix.mul_one, single_mul_bellTwirlUnitary, Matrix.smul_kronecker,
      ← mul_kronecker_mul, Matrix.mul_one, peAnnounceBellRelabelUnitary,
      Equiv.Perm.permMatrix_mul_single]
    rw [aliceKeyString_bellStringRelabel, hsyn, peBlock_bellStringRelabel,
      verificationTag_add_right]
    have hindex := peAnnounceBellRelabel_passOutIndex n m ℓ ℓEV peSel leakEC h πsyn k k st
      (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
      (ec.syndrome (aliceKeyString peSel ω))
      (partEquiv (m := m) peSel ω).2
    rw [← hindex, Equiv.symm_apply_apply]
  · have hp' : ¬ (siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellOutcomePerm n h ω) = true) := by rw [hguard]; exact hp
    simp [idealPassKraus,
     hp, hp']

/-! ## Channel-level covariance of the
general-`m` base maps

The three per-Kraus intertwinings lift to the two general-`m` base PA/abort maps, hence to their
difference.  The two Kraus-index reindexings `peAnnounceOutcomeReindex` and
`peAnnounceIdealReindex` are `Equiv`s of the (`m`-free) index types and are reused unchanged. -/

open scoped Classical in
/-- **The general-`m` real base PA/abort map is Bell-twirl covariant**, with the general-`m`
announced-PE relabel unitary on the output. -/
theorem announcedReal_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (Signals n × E)) :
    real E n m ℓ ℓEV peSel xSel leakEC
        ec δ Q
        ((signalBellUnitary h ⊗ₖ (1 : Op E)) * M *
          ((signalBellUnitary h ⊗ₖ (1 : Op E)))ᴴ) =
      ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
        real E n m ℓ ℓEV peSel xSel
          leakEC ec δ Q M *
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)))ᴴ := by
  set U := (signalBellUnitary h ⊗ₖ (1 : Op E)) with hU
  set W := ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) with hW
  have hpass : krausMap
      (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMap
        (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMap_conj_of_phased_intertwining
      (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (fun idx => passKraus E n m ℓ ℓEV peSel xSel leakEC
        ec δ Q (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => announcedPassKraus_bellTwirl_intertwining
        E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMap_comp_equiv (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        (peAnnounceOutcomeReindex n ℓ ℓEV peSel h)]
  have hfail : krausMap
      (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMap
        (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMap_conj_of_phased_intertwining
      (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (fun idx => failKraus E n m ℓ ℓEV peSel xSel leakEC
        ec δ Q (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => announcedFailKraus_bellTwirl_intertwining
        E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMap_comp_equiv (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        (peAnnounceOutcomeReindex n ℓ ℓEV peSel h)]
  simp only [real_eq_krausMap, LinearMap.add_apply,
    LinearMap.smul_apply, hpass, hfail]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul]

open scoped Classical in
/-- **The general-`m` ideal base key/abort map is Bell-twirl covariant**, with the same relabel
unitary. -/
theorem announcedIdeal_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (Signals n × E)) :
    ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q
        ((signalBellUnitary h ⊗ₖ (1 : Op E)) * M *
          ((signalBellUnitary h ⊗ₖ (1 : Op E)))ᴴ) =
      ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
        ideal E n m ℓ ℓEV peSel xSel leakEC
          ec δ Q M *
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)))ᴴ := by
  set U := (signalBellUnitary h ⊗ₖ (1 : Op E)) with hU
  set W := ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) with hW
  have hideal : krausMap
      (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMap
        (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMap_conj_of_phased_intertwining
      (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (fun idx => idealPassKraus E n m ℓ ℓEV peSel xSel leakEC
        ec δ Q (peAnnounceIdealReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.1) (fun idx => bellTwirlSign_unit n h idx.1)
      (fun idx => announcedIdealPassKraus_bellTwirl_intertwining
        E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMap_comp_equiv (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        (peAnnounceIdealReindex n ℓ ℓEV peSel h)]
  have hfail : krausMap
      (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMap
        (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMap_conj_of_phased_intertwining
      (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (fun idx => failKraus E n m ℓ ℓEV peSel xSel leakEC
        ec δ Q (peAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => announcedFailKraus_bellTwirl_intertwining
        E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMap_comp_equiv (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
        (peAnnounceOutcomeReindex n ℓ ℓEV peSel h)]
  simp only [ideal_eq_krausMap, LinearMap.add_apply,
    LinearMap.smul_apply, hideal, hfail]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul]

open scoped Classical in
/-- **The general-`m` base real−ideal difference intertwines the Bell twirl with the announced-PE
relabel.**

Nothing is masked: the announced PE block, the announced syndrome and the announced
error-verification tag are all relabelled, and the key slots are relabelled only on the accept
branch. -/
theorem announcedReal_sub_announcedIdeal_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (Signals n × E)) :
    (real E n m ℓ ℓEV peSel xSel
          leakEC ec δ Q -
        ideal E n m ℓ ℓEV peSel xSel leakEC
          ec δ Q)
        ((signalBellUnitary h ⊗ₖ (1 : Op E)) * M *
          ((signalBellUnitary h ⊗ₖ (1 : Op E)))ᴴ) =
      ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
        (real E n m ℓ ℓEV peSel xSel
              leakEC ec δ Q -
            ideal E n m ℓ ℓEV peSel xSel
              leakEC ec δ Q) M *
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)))ᴴ := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply,
    announcedReal_bellTwirl_conj
      E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec M,
    announcedIdeal_bellTwirl_conj
      E n m ℓ ℓEV peSel xSel leakEC ec δ Q h πsyn hsyn hdec M,
    Matrix.mul_sub, Matrix.sub_mul]

/-! ## From the physical twirl to the relabel: sift, then measure

The general-`m` protocol map is `PA/abort ∘ measurementChannel`
(`siftedPEAnnounceEveVisibleProtocol`), and it is fed the output of the sifted attack
channel.  The physical twirl `U_g` therefore reaches the PA/abort map as `U_{g'}` with
`g' = siftedTwirlString peSel xSel g`.  The sift conjugation
`siftedConjChannel_bellTwirl_conj` and the key-round transparency
`bellTwirlKeyError_siftedTwirlString` act on `Op (4^n * eveDim)` and carry no split point, so they
are the `m`-free originals. -/

open scoped Classical in
/-- **The general-`m` protocol-map difference intertwines the twirl reaching the measurement with
the announced-PE relabel.**

The two maps differenced here are the general-`m` real and ideal protocol maps, written out
rather than taken through the `EveVisibleProtocolScheme` projection so that the output
dimension is the syntactic `eveVisiblePEAnnounceBaseOutputDim`, which the `HMul` instance for
the conjugation needs.

The `measurementChannel` between the sift and the PA/abort map lets the monomial twirl through
unchanged (`measurementChannel_bellTwirl_outcomeRelabel`). -/
theorem siftedPEAnnounceEveVisible_measuredDiff_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (Signals n × E)) :
    ((real E n m ℓ ℓEV peSel xSel
            leakEC ec δ Q -
          ideal E n m ℓ ℓEV peSel xSel leakEC
            ec δ Q).comp (mapTensorId (classicalMap (id : Signals n → Signals n)) E))
        ((signalBellUnitary h ⊗ₖ (1 : Op E)) * M *
          ((signalBellUnitary h ⊗ₖ (1 : Op E)))ᴴ) =
      ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)) *
        ((real E n m ℓ ℓEV peSel xSel
                leakEC ec δ Q -
              ideal E n m ℓ ℓEV peSel xSel
                leakEC ec δ Q).comp (mapTensorId (classicalMap (id : Signals n → Signals n)) E)) M *
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) ⊗ₖ (1 : Op E)))ᴴ := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, measurementChannel_bellTwirl_outcomeRelabel,
    announcedReal_sub_announcedIdeal_bellTwirl_conj E n m ℓ ℓEV peSel xSel leakEC ec δ Q h
      πsyn hsyn hdec]

open scoped Classical in
/-- **The end-to-end general-`m` base
covariance: physical twirl in, announced-PE
relabel out.**

`Δ(sift (U_g · M · U_g†)) = (W ⊗ 1) · Δ(sift M) · (W ⊗ 1)†` with
`W = peAnnounceBellRelabelUnitary … (siftedTwirlString peSel xSel g) πsyn`.

The hypotheses on `ec` are stated at the **physical** twirl string `g`, which is legitimate because
the sift is the identity on key rounds (`bellTwirlKeyError_siftedTwirlString`); the announced PE
block, in contrast, is relabelled at the sift-relabelled string `siftedTwirlString peSel xSel
g`, i.e. by `bellHadSwap (g i)` on the X-designated PE rounds. -/
theorem siftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (g : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel g) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel g)
          (ec.syndrome (a + bellTwirlKeyError peSel g)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel g)
    (M : Op (Signals n × E)) :
    ((real E n m ℓ ℓEV peSel xSel
            leakEC ec δ Q -
          ideal E n m ℓ ℓEV peSel xSel leakEC
            ec δ Q).comp (mapTensorId (classicalMap (id : Signals n → Signals n)) E))
        (siftedConjChannel E n peSel xSel
          ((signalBellUnitary g ⊗ₖ (1 : Op E)) * M *
            ((signalBellUnitary g ⊗ₖ (1 : Op E)))ᴴ)) =
      ((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (siftedTwirlString peSel xSel g) πsyn) ⊗ₖ (1 : Op E)) *
        ((real E n m ℓ ℓEV peSel xSel
                leakEC ec δ Q -
              ideal E n m ℓ ℓEV peSel xSel
                leakEC ec δ Q).comp (mapTensorId (classicalMap (id : Signals n → Signals n)) E))
          (siftedConjChannel E n peSel xSel M) *
        (((peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (siftedTwirlString peSel xSel g) πsyn) ⊗ₖ (1 : Op E)))ᴴ := by
  have hkey := bellTwirlKeyError_siftedTwirlString peSel xSel g
  rw [siftedConjChannel_bellTwirl_conj E n peSel xSel g M]
  exact siftedPEAnnounceEveVisible_measuredDiff_bellTwirl_conj E n m ℓ ℓEV peSel xSel
    leakEC ec δ Q (siftedTwirlString peSel xSel g) πsyn (by rw [hkey]; exact hsyn)
    (by rw [hkey]; exact hdec) _


/-- Move the permutation record past Eve into the public transcript. -/
def peAnnounceReferenceEquiv (E : Type*) (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) ×
        Equiv.Perm (Fin n) ≃
      KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E :=
  (Equiv.prodAssoc _ _ _).trans
    (((Equiv.refl _).prodCongr (Equiv.prodComm _ _)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((KeyedOutput.prodEquiv ℓ _ _).prodCongr (Equiv.refl E))))

/-- Announcing a permutation appends its projector and structurally regroups the registers. -/
theorem announceEve_eq_reindex_kronecker {E : Type*}
    {n m ℓ ℓEV : ℕ} (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (A : Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)) :
    siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π A =
      Matrix.reindex (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC)
        (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC)
        (A ⊗ₖ (Matrix.single π π 1 : Op (Equiv.Perm (Fin n)))) := rfl

/-- Retaining Eve while announcing the permutation preserves trace norm. -/
theorem traceNorm_siftedPEAnnounceLinearEveVisible {E : Type*} [Fintype E]
    {n m ℓ ℓEV : ℕ} (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (A : Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)) :
    traceNorm (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π A) =
      traceNorm A := by
  rw [announceEve_eq_reindex_kronecker, traceNorm_reindex, traceNorm_kronecker_single]

/-- The same announcement preserves trace norm with any further reference register. -/
theorem traceNorm_mapTensorId_siftedPEAnnounceLinearEveVisible
    {E R : Type*} [Fintype E] [Fintype R] {n m ℓ ℓEV : ℕ}
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (A : Op ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R)) :
    traceNorm (mapTensorId
      (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π) R A) =
      traceNorm A := by
  rw [siftedPEAnnounceLinearEveVisible, mapTensorId_assoc, traceNorm_reindex,
    ← siftedPEAnnounceLinearEveVisible, traceNorm_siftedPEAnnounceLinearEveVisible,
    traceNorm_reindex]

end QKD.BB84.FiniteKey
