import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Registers

/-!
# The differ event

`siftedKeyStringsDiffer` splits the inner-budget Kraus family by whether Alice's and Bob's
reconciled key strings actually differ. The protocol-level objects it is built from — key strings,
`ECScheme` — live in `QCryptLean.QKD.BB84.ErrorCorrection`; this analysis-layer predicate
stays in the `FiniteKey`, upstream of both the inner-budget Kraus split by this predicate and the
announce-conditioning lemmas about it.

## Main definitions

- `siftedKeyStringsDiffer`: the `Bool`-valued differ event, Alice's key string against Bob's
  syndrome-decoded string.

## Main results

- `siftedKeyStringsDiffer_eq_true_iff` (`@[simp]`): identifies the `Bool` differ event
  with the `Prop` it decides.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

/-- **The differ event**, as a `Bool`: Alice's key string differs from Bob's reconciled string.
    Bool-valued so that it can test a Kraus family alongside the accept predicate
    `siftedLocalPEAndEVPassed`; `siftedKeyStringsDiffer_eq_true_iff` identifies it with
    the `Prop` the scalar weight functional `siftedEveVisibleDifferAcceptWeight` uses. -/
def siftedKeyStringsDiffer {n : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : QKD.BB84.ECScheme n peSel leakEC) (ω : QKD.BB84.Measurement.Signals n) : Bool :=
  decide (QKD.BB84.aliceKeyString peSel ω ≠
    ec.decode (QKD.BB84.bobKeyString peSel ω) (ec.syndrome (QKD.BB84.aliceKeyString peSel ω)))

@[simp] lemma siftedKeyStringsDiffer_eq_true_iff {n : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : QKD.BB84.ECScheme n peSel leakEC) (ω : QKD.BB84.Measurement.Signals n) :
    siftedKeyStringsDiffer peSel ec ω = true ↔
      QKD.BB84.aliceKeyString peSel ω ≠
        ec.decode (QKD.BB84.bobKeyString peSel ω)
          (ec.syndrome (QKD.BB84.aliceKeyString peSel ω)) := by
  simp [siftedKeyStringsDiffer]

end QKD.BB84.FiniteKey

end
