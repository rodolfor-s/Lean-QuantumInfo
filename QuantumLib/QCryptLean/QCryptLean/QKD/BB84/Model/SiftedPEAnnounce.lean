import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Average
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # Sifted measurement with public parameter-estimation announcements

The output retains both keys, the acceptance flag and every announcement on both
branches. Real and ideal maps share the abort branch. The ideal pass branch writes
one uniform key in both key slots. Eve is an arbitrary finite reference register.
-/

open Quantum.Operators Quantum.Channels Matrix
open Quantum.Symmetry QKD.BB84.Measurement QKD.BB84.FiniteKey
open scoped Kronecker BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

open scoped Classical in
/-- The seed pair, verification tag, syndrome and measured test outcomes. -/
abbrev PEAnnouncePublic (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :=
  ((KeyHashSeedPairEV n ℓ ℓEV peSel × Bits ℓEV) × Bits leakEC) ×
    Signals (min n m)

open scoped Classical in
/-- The public data after announcing the sampled round permutation. -/
abbrev SymPEAnnouncePublic (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :=
  PEAnnouncePublic n m ℓ ℓEV peSel leakEC × Equiv.Perm (Fin n)

variable (E : Type*) [Fintype E]

open scoped Classical in
/-- Conjugate by the sifted basis rotation while retaining Eve. -/
def siftedConjChannel (n : ℕ) (peSel xSel : Fin n → Bool) :
    Operation (Signals n × E) (Signals n × E) :=
  Matrix.conjLinearMap (siftedRotation n peSel xSel ⊗ₖ (1 : Op E))

open scoped Classical in
/-- Sifted conjugation preserves all channels' normalization and positivity. -/
theorem isChannel_siftedConjChannel (n : ℕ) (peSel xSel : Fin n → Bool) :
    IsChannel (siftedConjChannel E n peSel xSel) := by
  classical
  apply (isChannel_conjLinearMap_iff _).mpr
  convert conjTranspose_mul_siftedRotation_tensor_one E n peSel xSel using 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open scoped Classical in
/-- Apply a retained-reference pre-channel and then the sifted rotation. -/
def siftedConjAfterPre {n : ℕ} (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) : Operation (Signals n) (Signals n × E) :=
  (siftedConjChannel E n peSel xSel).comp pre

open scoped Classical in
/-- Sifting after a channel is a channel. -/
theorem isChannel_siftedConjAfterPre {n : ℕ} (pre : Operation (Signals n) (Signals n × E))
    (hpre : IsChannel pre) (peSel xSel : Fin n → Bool) :
    IsChannel (siftedConjAfterPre E pre peSel xSel) :=
  (isChannel_siftedConjChannel E n peSel xSel).comp hpre

namespace Announced

open scoped Classical in
/-- Accepted output with both potentially different keys and all public data. -/
def pePassOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (kA kB : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Bits ℓEV)
    (syn : Bits leakEC) (p : Signals (min n m)) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  ((kA, kB), (true, (((st, evTag), syn), p)))

open scoped Classical in
/-- Rejected output: zero both keys and retain every public announcement. -/
def peFailOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Bits ℓEV)
    (syn : Bits leakEC) (p : Signals (min n m)) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  ((0, 0), (false, (((st, evTag), syn), p)))

open scoped Classical in
/-- The real accepted transcript for a seed pair and measurement outcome. -/
def passOutputIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  pePassOutIndex n m ℓ ℓEV peSel leakEC
    (keyHash n ℓ peSel st.1 (aliceKeyString peSel ω))
    (keyHash n ℓ peSel st.1
      (ec.decode (bobKeyString peSel ω) (ec.syndrome (aliceKeyString peSel ω))))
    st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
    (ec.syndrome (aliceKeyString peSel ω)) (partEquiv (m := m) peSel ω).2

open scoped Classical in
/-- The abort transcript for a seed pair and measurement outcome. -/
def failOutputIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  peFailOutIndex n m ℓ ℓEV peSel leakEC st
    (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
    (ec.syndrome (aliceKeyString peSel ω)) (partEquiv (m := m) peSel ω).2

open scoped Classical in
/-- The ideal accepted transcript, with one fresh key in both slots. -/
def idealPassOutputIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (k : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  pePassOutIndex n m ℓ ℓEV peSel leakEC k k st
    (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
    (ec.syndrome (aliceKeyString peSel ω)) (partEquiv (m := m) peSel ω).2

open scoped Classical in
/-- The unscaled passKraus branch, retaining Eve unchanged. -/
def passKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun ⟨st, ω⟩ => if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
    Matrix.single (passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) ω (1 : ℂ) ⊗ₖ (1 : Op E)
  else 0

open scoped Classical in
/-- The unscaled failKraus branch, retaining Eve unchanged. -/
def failKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun ⟨st, ω⟩ => if ¬ siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
    Matrix.single (failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) ω (1 : ℂ) ⊗ₖ (1 : Op E)
  else 0

open scoped Classical in
/-- The unscaled idealPassKraus branch, retaining Eve unchanged. -/
def idealPassKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Signals n × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun ⟨ω, k, st⟩ => if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
    Matrix.single (idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω) ω (1 : ℂ) ⊗ₖ (1 : Op E)
  else 0

open scoped Classical in
/-- Uniform seed sampling followed by real classical postprocessing, retaining Eve. -/
def real (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Operation (Signals n × E)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  mapTensorId ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
    ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel, classicalMap (fun ω =>
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω
      else failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω)) E

open scoped Classical in
/-- Uniform key and seed sampling, with the same abort output as the real map. -/
def ideal (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Operation (Signals n × E)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  mapTensorId ((Fintype.card (Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
    ∑ ks : Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel, classicalMap (fun ω =>
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q ks.2.2 ω then
        idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec ks.1 ks.2 ω
      else failOutputIndex n m ℓ ℓEV peSel leakEC ec ks.2 ω)) E

open scoped Classical in
/-- The real announcement map is a channel for every finite retained register. -/
theorem isChannel_real (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    IsChannel (real E n m ℓ ℓEV peSel xSel leakEC ec δ Q) :=
  (IsChannel.uniformAverage _ (fun _ => isChannel_classicalMap _)).mapTensorId

open scoped Classical in
/-- The ideal announcement map is a channel for every finite retained register. -/
theorem isChannel_ideal (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    IsChannel (ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q) :=
  (IsChannel.uniformAverage _ (fun _ => isChannel_classicalMap _)).mapTensorId

open scoped Classical in
/-- The pass Kraus adjoint product depends only on its input outcome. -/
lemma passKraus_conjTranspose_mul_self (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (st, ω))ᴴ *
        passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (st, ω) =
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        Matrix.single ω ω (1 : ℂ) ⊗ₖ (1 : Op E) else 0 := by
  simp only [passKraus]
  split_ifs <;> simp [conjTranspose_kronecker, ← mul_kronecker_mul]

open scoped Classical in
/-- The ideal pass Kraus has the same input support for every fresh key. -/
lemma idealPassKraus_conjTranspose_mul_self (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (ω : Signals n) (k : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (ω, k, st))ᴴ *
        idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (ω, k, st) =
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        Matrix.single ω ω (1 : ℂ) ⊗ₖ (1 : Op E) else 0 := by
  simp only [idealPassKraus]
  split_ifs <;> simp [conjTranspose_kronecker, ← mul_kronecker_mul]

open scoped Classical in
/-- The classical real map equals the seed-weighted pass and fail Kraus sum. -/
theorem real_eq_krausMap (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    real E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
        krausMap (passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) +
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
        krausMap (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) := by
  classical
  apply LinearMap.ext
  intro A
  ext p q
  let B : Op (Signals n) := Matrix.of fun i j => A (i, p.2) (j, q.2)
  change ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
    ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel, classicalMap (fun ω =>
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω
      else failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω))
      B p.1 q.1 = _
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
    krausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.sum_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  conv_rhs => rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro st _
  rw [classicalMap_apply]
  simp only [Matrix.sum_apply]
  dsimp only [B, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
  · by_cases hp : passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = p.1 <;>
      by_cases hq : passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = q.1 <;>
      simp [passKraus, failKraus, h, hp, hq, Matrix.mul_apply, Fintype.sum_prod_type,
        kroneckerMap_apply, Matrix.one_apply, single_apply, conjTranspose_apply, apply_ite] <;>
        simp_all
  · by_cases hp : failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = p.1 <;>
      by_cases hq : failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = q.1 <;>
      simp [passKraus, failKraus, h, hp, hq, Matrix.mul_apply, Fintype.sum_prod_type,
        kroneckerMap_apply, Matrix.one_apply, single_apply, conjTranspose_apply, apply_ite] <;>
        simp_all

open scoped Classical in
/-- The ideal map has the original fresh-key pass scale and seed-only abort scale. -/
theorem ideal_eq_krausMap (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))⁻¹ •
        krausMap (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) +
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
        krausMap (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) := by
  classical
  apply LinearMap.ext
  intro A
  ext p q
  let B : Op (Signals n) := Matrix.of fun i j => A (i, p.2) (j, q.2)
  change ((Fintype.card (Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
    ∑ ks : Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel, classicalMap (fun ω =>
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q ks.2.2 ω then
        idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec ks.1 ks.2 ω
      else failOutputIndex n m ℓ ℓEV peSel leakEC ec ks.2 ω))
      B p.1 q.1 = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_apply, krausMap, Matrix.sum_apply,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  simp_rw [classicalMap_apply, Matrix.sum_apply]
  dsimp only [B, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  conv_rhs => arg 1; arg 2; arg 2; ext; rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; arg 2; rw [Fintype.sum_prod_type]
  have h (ω : Signals n) (k : Bits ℓ) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
      (Matrix.single
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
          idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω
        else failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω)
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
          idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω
        else failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω)
        (A (ω, p.2) (ω, q.2))) p.1 q.1 =
      (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (ω, k, st) * A *
        (idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (ω, k, st))ᴴ) p q +
      (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (st, ω) * A *
        (failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q (st, ω))ᴴ) p q := by
    by_cases h : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
    · by_cases hp : idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω = p.1 <;>
        by_cases hq : idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω = q.1 <;>
        simp [idealPassKraus, failKraus, h, hp, hq, Matrix.mul_apply, Fintype.sum_prod_type,
          kroneckerMap_apply, Matrix.one_apply, single_apply, conjTranspose_apply, apply_ite] <;>
        simp_all
    · by_cases hp : failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = p.1 <;>
        by_cases hq : failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω = q.1 <;>
        simp [idealPassKraus, failKraus, h, hp, hq, Matrix.mul_apply, Fintype.sum_prod_type,
          kroneckerMap_apply, Matrix.one_apply, single_apply, conjTranspose_apply, apply_ite] <;>
        simp_all
  simp_rw [h, Finset.sum_add_distrib]
  rw [mul_add]
  congr 1
  · congr 1
    rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm), Finset.sum_comm]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp

end Announced

/-- The sifted measurement and postprocessing scheme on the complete padded output. -/
def siftedPEAnnounceEveVisibleProtocol (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    EveVisibleProtocolScheme n ℓ where
  Public := PEAnnouncePublic n m ℓ ℓEV peSel leakEC
  realProtocolMap := by
    classical
    exact (Announced.real _ n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp
      (mapTensorId (classicalMap id) _)
  idealProtocolMap := by
    classical
    exact (Announced.ideal _ n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp
      (mapTensorId (classicalMap id) _)

/-- Append the actual sampled permutation to the public transcript. -/
def siftedPEAnnounceLinear (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    Operation (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC))
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC)) where
  toFun A := Matrix.reindex (KeyedOutput.prodEquiv ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) _)
    (KeyedOutput.prodEquiv ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) _)
      (A ⊗ₖ permAnnounceProjector n perm)
  map_add' A B := by simp only [add_kronecker, reindex_add]
  map_smul' c A := by simp only [RingHom.id_apply, smul_kronecker, reindex_smul]

/-- Announce the permutation without modifying Eve's register. -/
def siftedPEAnnounceLinearEveVisible (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    Operation (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  mapTensorId (siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm) E

/-- Symmetrized retained-reference real channel, with a public permutation record. -/
def symRealEveVisible (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (pre : Operation (Signals n) (Signals n × E)) :
    Operation (Signals n)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  (n.factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n),
    (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π).comp
      (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
        (E := E)).comp ((siftedConjAfterPre E pre peSel xSel).comp (permConjLin π)))

/-- Symmetrized retained-reference ideal channel, with the same public record. -/
def symIdealEveVisible (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (pre : Operation (Signals n) (Signals n × E)) :
    Operation (Signals n)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  (n.factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n),
    (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π).comp
      (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).idealProtocolMap
        (E := E)).comp ((siftedConjAfterPre E pre peSel xSel).comp (permConjLin π)))

/-- The real model with the trivial retained register and no pre-attack. -/
def symReal (n m ℓ ℓEV : ℕ) (Q δ : ℝ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    Operation (Signals n)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit) :=
  symRealEveVisible Unit n m ℓ ℓEV Q δ peSel xSel leakEC ec (unitRegisterEmbed n)

/-- The ideal model with the trivial retained register and no pre-attack. -/
def symIdeal (n m ℓ ℓEV : ℕ) (Q δ : ℝ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    Operation (Signals n)
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit) :=
  symIdealEveVisible Unit n m ℓ ℓEV Q δ peSel xSel leakEC ec (unitRegisterEmbed n)

/-- The bare real model is exactly the retained-register instance at `Unit`. -/
theorem symReal_eq_symRealEveVisible_unitRegisterEmbed (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      symRealEveVisible Unit n m ℓ ℓEV Q δ peSel xSel leakEC ec (unitRegisterEmbed n) := rfl

/-- The bare ideal model is exactly the retained-register instance at `Unit`. -/
theorem symIdeal_eq_symIdealEveVisible_unitRegisterEmbed (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      symIdealEveVisible Unit n m ℓ ℓEV Q δ peSel xSel leakEC ec (unitRegisterEmbed n) := rfl

/-- Relabel only the recorded permutation by right multiplication. -/
private def symPermAnnounceCorrectionMap (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    Operation (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC))
      (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC)) :=
  let e := (Equiv.refl (Bits ℓ × Bits ℓ)).prodCongr
    ((Equiv.refl Bool).prodCongr
      ((Equiv.refl (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)).prodCongr (Equiv.mulRight π)))
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

private lemma symPermAnnounceCorrectionMap_siftedPEAnnounceLinear (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (π perm : Equiv.Perm (Fin n))
    (A : Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC))) :
    symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC π
      (siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm A) =
    siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC (perm * π) A := by
  classical
  ext p q
  simp [symPermAnnounceCorrectionMap, siftedPEAnnounceLinear, KeyedOutput.prodEquiv,
    permAnnounceProjector, Matrix.reindex_apply, Matrix.submatrix_apply,
    kroneckerMap_apply, single_apply, eq_mul_inv_iff_mul_eq]

omit [Fintype E] in
private lemma announceLinearEveVisible_sum_right_mul_eq_correction_map (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E))
    (σ : Equiv.Perm (Fin n)) :
    (∑ π : Equiv.Perm (Fin n),
      siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π (F (π * σ))) =
    mapTensorId (symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC σ.symm) E
      (∑ π : Equiv.Perm (Fin n),
        siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π (F π)) := by
  let G := fun π => siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC
    (π * σ.symm) (F π)
  have he : (∑ π, siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π
      (F (π * σ))) = ∑ π, G π := by
    convert Equiv.sum_comp (Equiv.mulRight σ) G using 1
    simp [G, ← Equiv.Perm.inv_def, mul_assoc]
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro π _
  ext p q
  exact (congrFun₂ (symPermAnnounceCorrectionMap_siftedPEAnnounceLinear
    n m ℓ ℓEV peSel leakEC σ.symm π (fun i j => F π (i, p.2) (j, q.2))) p.1 q.1).symm

/-- Every fixed base map becomes permutation covariant after a public permutation average. -/
theorem permutationCovariant_symAnnouncedMap (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ)
    (base : Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)) :
    PermutationCovariant ((n.factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n),
      (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π).comp
        (base.comp (permConjLin π))) := by
  refine ⟨fun σ => ⟨mapTensorId
    (symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC σ.symm) E,
    (isChannel_reindex _).mapTensorId, ?_⟩⟩
  intro A
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul]
  congr 1
  have h (π : Equiv.Perm (Fin n)) :
      permConjLin π (permutationRepresentation σ * A * (permutationRepresentation σ)ᴴ) =
        permConjLin (π * σ) A := by
    simp only [permConjLin, LinearMap.coe_mk, AddHom.coe_mk, permutationRepresentation,
      ← tensorPermutation_mul, conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [h]
  exact announceLinearEveVisible_sum_right_mul_eq_correction_map E
    n m ℓ ℓEV peSel leakEC (fun π => base (permConjLin π A)) σ

/-- The real/ideal model difference satisfies CKR permutation covariance. -/
theorem permutationCovariant_symReal_sub_symIdeal (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    PermutationCovariant
      (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) := by
  let R : Operation (Signals n × Unit)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit) :=
    (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
      (E := Unit)
  let I : Operation (Signals n × Unit)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × Unit) :=
    (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).idealProtocolMap
      (E := Unit)
  let S := siftedConjAfterPre Unit (unitRegisterEmbed n) peSel xSel
  let L := siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC
  convert permutationCovariant_symAnnouncedMap Unit n m ℓ ℓEV peSel leakEC
    ((R - I).comp S) using 1
  apply LinearMap.ext
  intro A
  simp only [symReal, symIdeal, symRealEveVisible, symIdealEveVisible,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  change (n.factorial : ℂ)⁻¹ • ∑ π, L π (R (S (permConjLin π A))) -
      (n.factorial : ℂ)⁻¹ • ∑ π, L π (I (S (permConjLin π A))) =
    (n.factorial : ℂ)⁻¹ • ∑ π, L π (R (S (permConjLin π A)) - I (S (permConjLin π A)))
  simp only [map_sub, Finset.sum_sub_distrib, smul_sub]

end QKD.BB84.Model
