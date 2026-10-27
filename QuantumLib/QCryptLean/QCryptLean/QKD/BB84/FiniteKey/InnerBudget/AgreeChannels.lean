import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus

/-!
# Agree-branch real and ideal pass channels for the general-`m` PE scheme

Restrictions of the general-`m` real and ideal pass Kraus families
(`Announced.passKraus`, `Announced.idealPassKraus`)
and of the corresponding pass channels to the branch on which Alice's and Bob's sifted key
strings agree (`siftedKeyStringsDiffer`), zeroing every outcome where they differ. Paired
with the complementary differ-branch pass channels, these split the base-scheme pass channel
into an agree part and a differ part.

## Main definitions

* `realPassAgreeKraus`, `idealPassAgreeKraus` — the agree-restricted real/ideal pass
  Kraus families.
* `announcedEveRealAgree`,
  `announcedEveIdealAgree` — the corresponding agree pass channels.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`), the general test-set
size `m` at `main.tex:909` ("a random subset of $m$ signals") and `:913`
("the remaining $\nkey = n - m$ signals").
-/

open Quantum.Operators Matrix Quantum.Channels
open QKD.BB84.Measurement
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

variable (E : Type*) [Fintype E]

open scoped Classical in
/-- The general-`m` real pass Kraus family, zeroed on the outcomes where Alice's and Bob's
sifted key strings differ. -/
def realPassAgreeKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun k =>
    if siftedKeyStringsDiffer peSel ec k.2 then 0
    else Announced.passKraus E n m ℓ ℓEV
      peSel xSel leakEC ec δ Q k

open scoped Classical in
/-- The general-`m` ideal pass Kraus family, zeroed on the outcomes where Alice's and Bob's
sifted key strings differ. -/
def idealPassAgreeKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Signals n × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun k =>
    if siftedKeyStringsDiffer peSel ec k.1 then 0
    else Announced.idealPassKraus E n m ℓ ℓEV
      peSel xSel leakEC ec δ Q k

open scoped Classical in
/-- The accept branch of the general-`m` real privacy-amplification/abort channel, restricted to
the outcomes where Alice's and Bob's sifted key strings agree. -/
noncomputable def announcedEveRealAgree
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMap (realPassAgreeKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

open scoped Classical in
/-- The accept branch of the general-`m` ideal privacy-amplification/abort channel, restricted to
the outcomes where Alice's and Bob's sifted key strings agree. -/
noncomputable def announcedEveIdealAgree
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMap (idealPassAgreeKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

end QKD.BB84.FiniteKey

end
