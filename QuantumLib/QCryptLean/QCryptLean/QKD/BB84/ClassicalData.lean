import Mathlib.Tactic.Ring
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData

/-!
# Classical data for BB84

Functions of a party's local bit-string register, public announcement data, and the
parameter-estimation and error-verification decisions. These are the classical postprocessing
steps of Nahar et al., arXiv:2403.11851, Section V.C. Protocol actions consume these functions;
this module defines no executable protocol or channel.
-/

noncomputable section

open QKD.BB84.FiniteKey QKD.BB84.Measurement

namespace QKD.BB84

/-- Alice's raw key, restricted to the physical key-round positions. -/
def aliceRawKey (n : ℕ) (peSel : Fin n → Bool) (x : Bits n) : KeyBitString n peSel :=
  fun i => x i.val

/-- Bob's uncorrected key, restricted to the physical key-round positions. -/
def bobRawKey (n : ℕ) (peSel : Fin n → Bool) (y : Bits n) : KeyBitString n peSel :=
  fun i => y i.val

/-- Alice's verification tag and reconciliation syndrome at the sampled seed pair. -/
def tagAndSyndrome (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seeds : KeyHashSeedPairEV n ℓ ℓEV peSel) (x : Bits n) : Bits ℓEV × Bits leakEC :=
  (verificationTag n ℓEV peSel seeds.2 (aliceRawKey n peSel x),
    ec.syndrome (aliceRawKey n peSel x))

/-- Whether both announced Z- and X-test error rates lie within `δ` of `Q`,
requiring both basis-specific test samples to be nonempty. -/
def testsPassed {n : ℕ} (m : ℕ) (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (min n m) → Bit) : Bool :=
  (decide (0 < siftedZTestSampleSize peSel xSel) &&
    decide (|((Finset.univ.filter fun j => xSel (peRoundIdx peSel j) = false ∧
        as j ≠ bs j).card : ℝ) / siftedZTestSampleSize peSel xSel - Q| ≤ δ)) &&
  (decide (0 < siftedXTestSampleSize peSel xSel) &&
    decide (|((Finset.univ.filter fun j => xSel (peRoundIdx peSel j) = true ∧
        as j ≠ bs j).card : ℝ) / siftedXTestSampleSize peSel xSel - Q| ≤ δ))

/-- Bob accepts when the tests pass and his decoded key reproduces Alice's verification tag. -/
def acceptFlag (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (min n m) → Bit) (t : KeyHashSeed n ℓEV peSel)
    (evTag : Bits ℓEV) (syn : Bits leakEC) (y : Bits n) : Bool :=
  testsPassed m peSel xSel δ Q as bs &&
    decide (evTag = verificationTag n ℓEV peSel t (ec.decode (bobRawKey n peSel y) syn))

/-- The announced-test decision with the canonical test count `m = (n + 1) / 2`. -/
def canonicalTestsPassed {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (min n ((n + 1) / 2)) → Bit) : Bool :=
  testsPassed ((n + 1) / 2) peSel xSel δ Q as bs

/-- Bob's accept flag with the canonical test count `m = (n + 1) / 2`. -/
def canonicalAcceptFlag (n ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (min n ((n + 1) / 2)) → Bit) (t : KeyHashSeed n ℓEV peSel)
    (evTag : Bits ℓEV) (syn : Bits leakEC) (y : Bits n) : Bool :=
  acceptFlag n ((n + 1) / 2) ℓEV peSel xSel leakEC ec δ Q as bs t evTag syn y

/-- The default parameter-estimation decision is the instance with `m = (n + 1) / 2`. -/
theorem testsPassed_canonical {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (min n ((n + 1) / 2)) → Bit) :
    testsPassed ((n + 1) / 2) peSel xSel δ Q as bs =
      canonicalTestsPassed peSel xSel δ Q as bs := rfl

/-- Alice's privacy-amplified key. -/
def aliceKey (n ℓ : ℕ) (peSel : Fin n → Bool) (s : KeyHashSeed n ℓ peSel)
    (x : Bits n) : Bits ℓ :=
  keyHash n ℓ peSel s (aliceRawKey n peSel x)

/-- Bob's privacy-amplified key after syndrome decoding. -/
def bobKey (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (s : KeyHashSeed n ℓ peSel) (syn : Bits leakEC)
    (y : Bits n) : Bits ℓ :=
  keyHash n ℓ peSel s (ec.decode (bobRawKey n peSel y) syn)

end QKD.BB84
