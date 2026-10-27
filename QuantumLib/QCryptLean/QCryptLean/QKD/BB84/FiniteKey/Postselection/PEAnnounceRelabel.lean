import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Postselection.ProtocolMapCovariance
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.SiftedAcceptTwirlInvariant
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # PEAnnounce Relabel -/


open Quantum.Operators Matrix Quantum.Channels
open QKD.BB84.Measurement
open scoped Kronecker Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

open QKD.BB84.Model.Announced
open QKD.BB84.Model


/-- **The effective twirl string after the sift.**  `siftedRotation` applies `H ⊗ H` on
rounds that are both PE- and X-designated and the identity elsewhere, and `H ⊗ H` carries the
bilateral Bell twirl group to itself by the sign-free involution `bellHadSwap = ![0,3,2,1]`
(`hadamardPair_conj_bellTwirl`).  So the string the computational measurement sees is `g` relabelled
by `bellHadSwap` exactly on the X-designated PE rounds. -/
def siftedTwirlString {n : ℕ} (peSel xSel : Fin n → Bool) (g : Fin n → Fin 4) :
    Fin n → Fin 4 :=
  fun i => if peSel i && xSel i then bellHadSwap (g i) else g i

/-- On a key round the sift is the identity, so the effective twirl string is `g` itself.  This
is why the key-round error pattern `bellTwirlKeyError` may be read off either string. -/
theorem siftedTwirlString_of_key {n : ℕ} (peSel xSel : Fin n → Bool) (g : Fin n → Fin 4)
    (i : Fin n) (hi : peSel i = false) :
    siftedTwirlString peSel xSel g i = g i := by
  simp [siftedTwirlString, hi]

/-- **The sift conjugates the Bell twirl to the Bell twirl at the relabelled string.**

`V · U_g · V† = U_{g'}` with `V = siftedRotation n peSel xSel` and
`g' = siftedTwirlString peSel xSel g`.  This is an exact operator identity with no phase: the
per-round conjugation `H ⊗ H · G_k · H ⊗ H = G_{bellHadSwap k}` is sign-free
(`hadamardPair_conj_bellTwirl`), so unlike the Bell-rotation argument there is no measurement-level
absorption step and no masking. -/
theorem siftedRotation_bellTwirl_conj (n : ℕ) (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) :
    siftedRotation n peSel xSel * signalBellUnitary g *
        (siftedRotation n peSel xSel)ᴴ =
      signalBellUnitary (siftedTwirlString peSel xSel g) := by
  have hV : siftedRotation n peSel xSel =
      piTensorProduct (fun a => xTestPairOp (peSel a) (xSel a)) := rfl
  have hU : ∀ g' : Fin n → Fin 4,
      signalBellUnitary g' = piTensorProduct (fun a => signalBilateralPauli (g' a)) :=
    fun _ => rfl
  rw [hV, hU, hU, conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
  refine congrArg piTensorProduct (funext fun a => ?_)
  by_cases hx : (peSel a && xSel a) = true
  · rw [show xTestPairOp (peSel a) (xSel a) = hadamardPair by
        simp [xTestPairOp, hx],
      conjTranspose_hadamardPair, signalBilateralPauli, hadamardPair_conj_bellTwirl]
    simp [siftedTwirlString, hx, signalBilateralPauli]
  · rw [show xTestPairOp (peSel a) (xSel a) = (1 : Op Signal) by
        simp [xTestPairOp, hx]]
    simp [siftedTwirlString, hx]


/-- The **control register** of a base output index: the accept flag and the announced seed pair.
Both are announced output coordinates, so a permutation of the output register may read them. -/
abbrev PEAnnounceControl (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) : Type :=
  Bool × KeyHashSeedPairEV n ℓ ℓEV peSel


/-- **The key-round error pattern imposed by the twirl string `h`**: `e i = bellKeyOutcomeFlip
    (h i)`
on key rounds.  This is the `e` at which `siftedLocalPEAndEVPassed_bellTwirl_invariant` needs
the paired decoder clause, and the `e` the hash-argument shifts are taken at. -/
def bellTwirlKeyError {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    KeyBitString n peSel :=
  fun i => bellKeyOutcomeFlip (h i.val)

/-- **The flag- and seed-controlled permutation of the two key slots.**  On the pass flag both key
slots are shifted by the hash-argument shift `σ_{st.1}` at the twirl's key-round error pattern; on
the abort flag it is the identity, because `Announced.peFailOutIndex` writes the zero key in both
slots
on **both** the twirled and the untwirled outcome. -/
def peAnnounceKeyPairPerm {n : ℕ} (ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (c : PEAnnounceControl n ℓ ℓEV peSel) : Equiv.Perm (Bits ℓ × Bits ℓ) :=
  if c.1 then
    (keyHashShiftPerm c.2.1 (bellTwirlKeyError peSel h)).prodCongr
      (keyHashShiftPerm c.2.1 (bellTwirlKeyError peSel h))
  else Equiv.refl _


/-- Alice's key string shifts by the twirl's key-round error pattern. -/
theorem aliceKeyString_bellStringRelabel {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Signals n) :
    aliceKeyString peSel (bellOutcomePerm n h ω) =
      aliceKeyString peSel ω + bellTwirlKeyError peSel h :=
  (key_strings_shift peSel h ω).1

/-- Bob's raw key string shifts by the same pattern. -/
theorem bobKeyString_bellStringRelabel {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Signals n) :
    bobKeyString peSel (bellOutcomePerm n h ω) =
      bobKeyString peSel ω + bellTwirlKeyError peSel h :=
  (key_strings_shift peSel h ω).2


/-- The Kraus-index reindexing of the real/ideal **fail** and real **pass** families: relabel the
outcome string by the twirl.  An involution. -/
def peAnnounceOutcomeReindex (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    (KeyHashSeedPairEV n ℓ ℓEV peSel × (Signals n)) ≃
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Signals n)) :=
  (Equiv.refl (KeyHashSeedPairEV n ℓ ℓEV peSel)).prodCongr (bellOutcomePerm n h)

/-- The Kraus-index reindexing of the **ideal pass** family: relabel the outcome string by the twirl
and translate the fresh uniform key by the privacy-amplification-seed shift at the announced seed.
-/
def peAnnounceIdealReindex (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    ((Signals n) × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) ≃
      ((Signals n) × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) where
  toFun x := (bellOutcomePerm n h x.1,
    keyHashShiftPerm x.2.2.1 (bellTwirlKeyError peSel h)
      x.2.1, x.2.2)
  invFun x := (bellOutcomePerm n h x.1,
    (keyHashShiftPerm x.2.2.1 (bellTwirlKeyError peSel h)).symm
      x.2.1, x.2.2)
  left_inv x := by
    obtain ⟨ω, k, st⟩ := x
    simp only [bellOutcomePerm_involutive n h ω, Equiv.symm_apply_apply]
  right_inv x := by
    obtain ⟨ω, k, st⟩ := x
    simp only [bellOutcomePerm_involutive n h ω, Equiv.apply_symm_apply]


/-- The key-round error pattern is the same for the physical and the sift-relabelled twirl string:
key rounds are never rotated. -/
theorem bellTwirlKeyError_siftedTwirlString {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) :
    bellTwirlKeyError peSel (siftedTwirlString peSel xSel g) =
      bellTwirlKeyError peSel g :=
  funext fun i =>
    show bellKeyOutcomeFlip (siftedTwirlString peSel xSel g i.val) =
        bellKeyOutcomeFlip (g i.val) by
      rw [siftedTwirlString_of_key peSel xSel g i.val i.property]

open scoped Classical in
/-- **The sifted conjugation channel carries the Bell twirl to the relabelled Bell twirl.** -/
theorem siftedConjChannel_bellTwirl_conj (E : Type*) [Fintype E]
    (n : ℕ) (peSel xSel : Fin n → Bool) (g : Fin n → Fin 4) (M : Op (Signals n × E)) :
    siftedConjChannel E n peSel xSel
        ((signalBellUnitary g ⊗ₖ (1 : Op E)) * M * (signalBellUnitary g ⊗ₖ (1 : Op E))ᴴ) =
      (signalBellUnitary (siftedTwirlString peSel xSel g) ⊗ₖ (1 : Op E)) *
        siftedConjChannel E n peSel xSel M *
        (signalBellUnitary (siftedTwirlString peSel xSel g) ⊗ₖ (1 : Op E))ᴴ := by
  classical
  have hcomm : siftedRotation n peSel xSel * signalBellUnitary g =
      signalBellUnitary (siftedTwirlString peSel xSel g) * siftedRotation n peSel xSel := by
    rw [← siftedRotation_bellTwirl_conj n peSel xSel g, Matrix.mul_assoc, Matrix.mul_assoc,
      conjTranspose_mul_siftedRotation, Matrix.mul_one]
  have h : (Matrix.conjLinearMap (siftedRotation n peSel xSel)).comp
      (Matrix.conjLinearMap (signalBellUnitary g)) =
      (Matrix.conjLinearMap (signalBellUnitary (siftedTwirlString peSel xSel g))).comp
        (Matrix.conjLinearMap (siftedRotation n peSel xSel)) := by
    rw [← Matrix.conjLinearMap_mul, ← Matrix.conjLinearMap_mul, hcomm]
  have he := congrArg (fun Φ : Operation (Signals n) (Signals n) => mapTensorId Φ E M) h
  simpa only [mapTensorId_comp, LinearMap.comp_apply, siftedConjChannel,
    mapTensorId_conjLinearMap, Matrix.conjLinearMap_apply] using he

end QKD.BB84.FiniteKey
