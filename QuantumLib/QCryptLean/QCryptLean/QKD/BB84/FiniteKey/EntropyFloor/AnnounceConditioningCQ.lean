import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-! # Announcement-conditioned BB84 CQ states

Public announcements stay in the quantum conditioning register before the secret register
is coarsened to Alice's key. On the agreement event, verification accepts for every seed,
so the accept filter depends only on the measurement outcome.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement
open scoped Kronecker

variable {E A Y : Type*} [Fintype E] [Fintype A] [DecidableEq A]
  [Fintype Y] [DecidableEq Y]

/-- Record the announcement on the quantum side, then coarsen the secret register. -/
def announceCoarsenCQ {n : ℕ} (g : Signals n → Y) (ann : Signals n → A)
    (ρ : CQState (Signals n) E) : CQState Y (A × E) :=
  (ρ.tensorLeftKernel fun ω => (stdNormKet (ann ω)).toDensityOp.toSubDensityOp).coarsen g

/-- Blocks of the announced state retain the complete public record. -/
theorem announceCoarsenCQ_stateMap {n : ℕ} (g : Signals n → Y) (ann : Signals n → A)
    (ρ : CQState (Signals n) E) (y : Y) :
    ((announceCoarsenCQ g ann ρ).stateMap y).toOp =
      ∑ ω, if g ω = y then (stdNormKet (ann ω)).projector ⊗ₖ (ρ.stateMap ω).toOp else 0 :=
  rfl

/-- Alice's secret key with the complete public announcement in the conditioning register. -/
def aliceKeyAnnounceCQ {n : ℕ} (peSel : Fin n → Bool) (ann : Signals n → A)
    (ρ : CQState (Signals n) E) : CQState (KeyBitString n peSel) (A × E) :=
  announceCoarsenCQ (aliceKeyString peSel) ann ρ

/-- **Agreeing key strings pass error verification, for every seed.**

`evVerified` compares the error-verification tags of Alice's key string and of Bob's
syndrome-decoded string.  When the two strings are equal the two tags are equal by `congrArg`, so
the test accepts whatever the announced seed `t` is.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C.  This is the *soundness*
direction of the error-verification test and carries no probability; the converse — that
disagreeing strings are rejected — holds only with probability `1 − 2^(−ℓEV)` and is charged
jointly by `errorVerification_joint_correctness_indexed`. -/
theorem evVerified_of_keyStrings_eq {n ℓEV : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (ω : Signals n)
    (h : aliceKeyString peSel ω =
      ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω))) :
    evVerified ℓEV peSel ec t ω = true := by
  unfold evVerified
  rw [← h]
  simp

/-! ## The differ-predicate forms, and the seed-free agree-and-accept keep predicate

These restate `evVerified_of_keyStrings_eq` and the accept-test collapse above at the
`siftedKeyStringsDiffer` predicate instead of key-string equality, and give the seed-free keep
predicate they build towards. -/

/-- **Not differing implies error verification passes**, for every announced seed.

`siftedKeyStringsDiffer = false` says Alice's key string equals Bob's syndrome-decoded
string; `evVerified_of_keyStrings_eq` then gives `evVerified = true` by `congrArg` on the
error-verification tag. -/
theorem evVerified_of_not_differ {n ℓEV : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (ω : Signals n)
    (h : siftedKeyStringsDiffer peSel ec ω = false) :
    evVerified ℓEV peSel ec t ω = true := by
  refine evVerified_of_keyStrings_eq peSel ec t ω ?_
  by_contra hne
  exact absurd ((siftedKeyStringsDiffer_eq_true_iff peSel ec ω).mpr hne) (by simp [h])

/-- **The accept test is seed-free on the agree block**, phrased at the differ predicate the
Kraus split uses (`realPassAgreeKraus` / `idealPassAgreeKraus`,
`AnnouncedChannels.lean`). -/
theorem _root_.QKD.BB84.Model.siftedLocalPEAndEVPassed.eq_siftedLocalPETestPassed_of_not_differ
    {n ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Signals n)
    (h : siftedKeyStringsDiffer peSel ec ω = false) :
    siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω =
      siftedLocalPETestPassed peSel xSel δ Q ω := by
  unfold siftedLocalPEAndEVPassed
  rw [evVerified_of_not_differ peSel ec t ω h, Bool.and_true]

/-- **The seed-free agree-and-accept keep predicate**: the fail-closed LOCC two-basis PE test passes
and Alice's key string agrees with Bob's syndrome-decoded string.

A function of the round outcome `ω` alone, hence a legal `keep : X → Bool` for
`CQState.filterKeep`.  It coincides with the agree restriction of the full seed-dependent accept
test, so filtering by it filters by the protocol's actual accept event on the agree block. -/
def siftedAgreeAcceptKeep {n : ℕ} (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (ω : Signals n) : Bool :=
  siftedLocalPETestPassed peSel xSel δ Q ω && !siftedKeyStringsDiffer peSel ec ω

end QKD.BB84.FiniteKey
