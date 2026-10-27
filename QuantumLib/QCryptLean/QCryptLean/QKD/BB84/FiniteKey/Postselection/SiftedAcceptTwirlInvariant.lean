import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers

/-!
# Bell-twirl invariance of the genuine-LOCC accept test

The bilateral-Pauli (Bell) twirl acts on the round outcomes by the per-round relabel
`ω i ↦ bellKeyOutcomePerm (g i) (ω i)` (`RoundKernel.lean`, the key-round signed-Pauli
pass-through `bellSinglePair_conj_compProjector`). This module proves that the **full accept
predicate `QKD.BB84.Model.siftedLocalPEAndEVPassed` is invariant under that relabel**, which is
what lets the twirl be pushed through the pass/fail Kraus split.

Two independent mechanisms, one per conjunct:

* **PE**: `bellKeyOutcomePerm k` fixes the disagreement set `{1, 2}` **setwise** for every `k`
  (identity at `k ∈ {I⊗I, Z⊗Z}`, `ω ↦ 3 - ω` at `k ∈ {X⊗X, Y⊗Y}`, and `3 - ·` swaps `1 ↔ 2`), so
  both test error counts and hence the fail-closed two-basis decision are literally unchanged.
* **EV**: `bellKeyOutcomePerm k` shifts Alice's and Bob's outcome bits by the **same** `Fin 2` value
  `bellKeyOutcomeFlip k`, so both key strings shift by the same key-round pattern `e`. Error
  verification is then invariant exactly when the reconciliation scheme is translation-equivariant
  at `e`.

This is analysis built on the model's accept-test definitions (`QKD.BB84.Model.SiftedMeasurement`)
and the FiniteKey's twirl-permutation machinery (`bellKeyOutcomePerm`, `RoundKernel.lean`), which is
why it lives in the FiniteKey rather than in the Model family: the Model states what the accept test
*is*; this module analyses what it is invariant under.

## Main definitions and results

* `bellKeyOutcomeFlip` — the per-round key-bit flip of the bilateral Bell twirl.
* `siftedLocalPEAndEVPassed_bellTwirl_invariant` — the **full accept test is invariant under
  the bilateral Bell (Pauli) twirl relabel** `ω i ↦ bellKeyOutcomePerm (g i) (ω i)`, given the
  translation-equivariance clause of the reconciliation scheme at the twirl's own key-round error
  pattern.
* `evVerified_shift_invariant`, `key_strings_shift`,
  `siftedLocalPETestPassed_bellTwirl_invariant` — the two halves: the twirl shifts BOTH key
  strings by the same pattern (so error verification is covariant), and it fixes the `{1,2}`
  disagreement sets setwise (so the two-basis PE decision is literally unchanged).

## References

Renner 2005 §5, §6.5; Nahar et al. 2024 (`arXiv:2403.11851`) §B.
-/

open QKD.BB84.Model QKD.BB84.Measurement
noncomputable section

namespace QKD.BB84.FiniteKey

/-- **The per-round key-bit flip of the bilateral Bell twirl.**  Conjugating a computational-basis
outcome by `G_k` flips Alice's bit and Bob's bit by this common value: `0` for the diagonal Paulis
`k ∈ {I⊗I, Z⊗Z}`, `1` for the off-diagonal ones `k ∈ {X⊗X, Y⊗Y}`.  The `n`-round pattern
`fun i => bellKeyOutcomeFlip (g i)` is the key-round error pattern the twirl imposes. -/
def bellKeyOutcomeFlip (k : Fin 4) : Fin 2 :=
  if k = 1 ∨ k = 2 then 1 else 0

/-- Simultaneously flipping the two bits preserves their disagreement. -/
theorem bellKeyOutcomePerm_ne_iff (k : Fin 4) (ω : Signal) :
    (bellKeyOutcomePerm k ω).1 ≠ (bellKeyOutcomePerm k ω).2 ↔ ω.1 ≠ ω.2 := by
  revert k ω; decide

/-- **The structural fact the EV half rests on**: the twirl relabel shifts Alice's bit and Bob's bit
by the **same** `Fin 2` value, i.e. it acts on the outcome bit pair as `(a, b) ↦ (a + f, b + f)`
with `f = bellKeyOutcomeFlip k`.  A relabel that moved the two bits by different amounts would
change the disagreement pattern and could not be absorbed into a translation of the key strings. -/
theorem bellKeyOutcomePerm_bits_shift (k : Fin 4) (ω : Signal) :
    (bellKeyOutcomePerm k ω).1 = ω.1 + bellKeyOutcomeFlip k ∧
    (bellKeyOutcomePerm k ω).2 = ω.2 + bellKeyOutcomeFlip k := by
  revert k ω; decide

/-- **The twirl shifts BOTH key strings by the same key-round pattern** `e i = bellKeyOutcomeFlip
(g i)`.  Key rounds are never rotated — `xTestPairOp` applies `H ⊗ H` only on rounds
with `peSel && xSel` — so the shift pattern comes from the twirl string `g` directly, with no `σ`
relabel in between. -/
theorem key_strings_shift {n : ℕ} (peSel : Fin n → Bool) (g : Fin n → Fin 4)
    (ω : Signals n) :
    aliceKeyString peSel (fun i => bellKeyOutcomePerm (g i) (ω i))
        = aliceKeyString peSel ω + (fun i => bellKeyOutcomeFlip (g i.val)) ∧
    bobKeyString peSel (fun i => bellKeyOutcomePerm (g i) (ω i))
        = bobKeyString peSel ω + (fun i => bellKeyOutcomeFlip (g i.val)) :=
  ⟨funext fun i => (bellKeyOutcomePerm_bits_shift (g i.val) (ω i.val)).1,
   funext fun i => (bellKeyOutcomePerm_bits_shift (g i.val) (ω i.val)).2⟩

/-- The Z-test disagreement count is invariant under the twirl relabel. -/
theorem siftedZTestErrorCount_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) (ω : Signals n) :
    siftedZTestErrorCount peSel xSel (fun i => bellKeyOutcomePerm (g i) (ω i))
      = siftedZTestErrorCount peSel xSel ω := by
  simp only [siftedZTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bellKeyOutcomePerm_ne_iff]

/-- The X-test disagreement count is invariant under the twirl relabel. -/
theorem siftedXTestErrorCount_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) (ω : Signals n) :
    siftedXTestErrorCount peSel xSel (fun i => bellKeyOutcomePerm (g i) (ω i))
      = siftedXTestErrorCount peSel xSel ω := by
  simp only [siftedXTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bellKeyOutcomePerm_ne_iff]

/-- **The whole fail-closed LOCC two-basis PE decision is twirl-invariant.**  Both subsample sizes
are functions of the selectors alone and both disagreement counts are invariant, so the accept ball
test is unchanged outcome by outcome — no hypothesis on the reconciliation scheme is needed for this
conjunct. -/
theorem siftedLocalPETestPassed_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (δ Q : ℝ) (g : Fin n → Fin 4) (ω : Signals n) :
    siftedLocalPETestPassed peSel xSel δ Q (fun i => bellKeyOutcomePerm (g i) (ω i))
      = siftedLocalPETestPassed peSel xSel δ Q ω := by
  simp only [siftedLocalPETestPassed,
    siftedZTestErrorCount_bellTwirl_invariant peSel xSel g ω,
    siftedXTestErrorCount_bellTwirl_invariant peSel xSel g ω]

/-- **Error verification is invariant when both key strings shift by the same key-round pattern
    `e`.**

The only property of the reconciliation scheme this uses is the **paired decoder clause**
`ec.decode (b + e) (ec.syndrome (a + e)) = ec.decode b (ec.syndrome a) + e` — clause (ii) of
translation equivariance.  **No syndrome permutation enters**: the hypothesis is stated on the
composite `decode ∘ syndrome`, so no permutation of the syndrome alphabet appears in the statement
and none is used in the proof.  Clause (i) of translation equivariance is not needed for the accept
flag.

The EV tag `verificationTag t` **depends on the seed `t`**, and so does its shift.  That is harmless
here — both tags in a single comparison are taken at the same `t` — but it means a downstream
output relabel built on this lemma must be defined **fibrewise over the announced seed register**;
a single `t`-independent global relabel of the key/tag slots is wrong. -/
theorem evVerified_shift_invariant {n ℓEV leakEC : ℕ} {peSel : Fin n → Bool}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (e : KeyBitString n peSel)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + e) (ec.syndrome (a + e)) = ec.decode b (ec.syndrome a) + e)
    (ω ω' : Signals n)
    (ha : aliceKeyString peSel ω' = aliceKeyString peSel ω + e)
    (hb : bobKeyString peSel ω' = bobKeyString peSel ω + e) :
    evVerified ℓEV peSel ec t ω' = evVerified ℓEV peSel ec t ω := by
  simp only [evVerified, ha, hb, hdec, verificationTag]
  apply decide_eq_decide.mpr
  rw [keyHash_add_right, keyHash_add_right]
  exact (keyHashShiftPerm t e).apply_eq_iff_eq

/-- **THE ACCEPT test IS BELL-TWIRL INVARIANT.**

For every twirl string `g : Fin n → Fin 4`, the full accept predicate — fail-closed LOCC
two-basis parameter estimation **and** error verification — takes the same value on the round
outcomes `ω` and on their bilateral-Pauli relabel `fun i => bellKeyOutcomePerm (g i) (ω i)`.

The hypothesis is the **paired decoder clause at the twirl's own key-round error pattern**
`e i = if g i = 1 ∨ g i = 2 then 1 else 0` (`bellKeyOutcomeFlip (g i)`), i.e. **clause (ii) of
translation equivariance of `ec`, and only clause (ii)** — no permutation of the syndrome alphabet
is required anywhere in the accept test.

Both conjuncts move for different reasons: the PE conjunct is invariant unconditionally
(`siftedLocalPETestPassed_bellTwirl_invariant`, the disagreement set `{1,2}` is fixed
setwise), while the EV conjunct needs the hypothesis (`evVerified_shift_invariant`) and genuinely
fails without it: there is a reconciliation scheme at which the accept test flips from `true` to
`false` under the twirl.

Key rounds are never rotated (`xTestPairOp` applies `H ⊗ H` only on `peSel && xSel`
rounds), so the shift pattern is read off `g` directly.  On X-designated PE rounds the sift relabels
the twirl element by `QKD.BB84.Model.hadamardPair_conj_bellTwirl`'s `σ = ![0,3,2,1]`, whose flip set
is `{Y, Z}`; that relabel is invisible here because the PE conjunct is invariant for **every** twirl
element. -/
theorem siftedLocalPEAndEVPassed_bellTwirl_invariant {n ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (g : Fin n → Fin 4) (ω : Signals n)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0))
          (ec.syndrome (a + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0)))
        = ec.decode b (ec.syndrome a) + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0)) :
    siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t
        (fun i => bellKeyOutcomePerm (g i) (ω i))
      = siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω := by
  have hev : evVerified ℓEV peSel ec t (fun i => bellKeyOutcomePerm (g i) (ω i))
      = evVerified ℓEV peSel ec t ω :=
    evVerified_shift_invariant ec t (fun i => bellKeyOutcomeFlip (g i.val)) hdec ω _
      (key_strings_shift peSel g ω).1 (key_strings_shift peSel g ω).2
  simp only [siftedLocalPEAndEVPassed,
    siftedLocalPETestPassed_bellTwirl_invariant peSel xSel δ Q g ω, hev]

end QKD.BB84.FiniteKey

end
