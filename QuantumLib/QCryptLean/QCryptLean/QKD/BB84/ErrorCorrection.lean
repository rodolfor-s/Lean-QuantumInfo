import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.Registers

/-!
# BB84 key strings and error-correction schemes

The protocol-level objects a BB84 error-correction/reconciliation round is built from: each
party's raw key-round bit string, and the announced-syndrome error-correction scheme that lets Bob
reconcile his string against Alice's. These are protocol data — every real BB84 run fixes an `n`,
a PE selector `peSel` and an `ec : ECScheme n peSel leakEC` — so they are homed here in the
protocol layer, not in the security-analysis `FiniteKey`.

## Main definitions
- `KeyBitString`: a key-round bit string on the subtype domain `{i // peSel i = false}` (indexed
  directly by the physical key rounds, not a `Fin n_K` reindex).
- `aliceKeyString` / `bobKeyString`: each party's raw key-round bit string.
- `ECScheme`: an announced-syndrome error-correction scheme on key strings. It carries **no**
  correctness guarantee — `decode` is an arbitrary function of Bob's string and the announced
  syndrome; correctness under an arbitrary attack comes from the error-verification test
  (`QKD.BB84.evVerified`), not from any property of `ec`, so the security statements quantify over
  EVERY `ec`.
- `ECScheme.IsTranslationEquivariant`: the two-clause covariance of a scheme under a common shift
  of both parties' key strings — what the bilateral Bell twirl needs in order to act on the
  transcript by a permutation. Its non-vacuity, and the independence of its two clauses, are
  build-enforced by counterexamples alongside the Bell-twirl consumers of this predicate.
- `ECScheme.relabel`: relabelling the announced syndrome alphabet by a public permutation.
- `ECScheme.DecodesWhp`: the probabilistic (typical-decoding) reconciliation guarantee — a
  **completeness-only** hypothesis, never a security one (see the `Completeness` module).

## Main statements
- `ECScheme.IsTranslationEquivariant.relabel`: relabelling the syndrome alphabet does not
  affect translation equivariance.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C (error correction
with `λEC(Fobs)` bits followed by error verification comparing hash values of length
`log(1/ε_EV)`); Renner 2005 §6.5.
-/

noncomputable section

namespace QKD.BB84

open Measurement

/-- A **key-round bit string**: one bit per key round, on the subtype domain
`{i // peSel i = false}`. Using the subtype domain (rather than a `Fin n_K` reindex) keeps the
key string directly indexed by the physical key rounds, killing the `peSel`-mismatch hazard where
a reindexed key string could silently address the wrong rounds. -/
abbrev KeyBitString (n : ℕ) (peSel : Fin n → Bool) : Type :=
  {i : Fin n // peSel i = false} → Bit

/-- Alice's raw key string: her computational-basis outcome bit on each key round
(the complement of the PE selector). -/
def aliceKeyString {n : ℕ} (peSel : Fin n → Bool)
    (ω : Signals n) : KeyBitString n peSel :=
  fun i => (ω i.val).1

/-- Bob's raw key string: his computational-basis outcome bit on each key round. -/
def bobKeyString {n : ℕ} (peSel : Fin n → Bool)
    (ω : Signals n) : KeyBitString n peSel :=
  fun i => (ω i.val).2

/-- An **error-correction scheme** on key-round bit strings: Alice publishes a `leakEC`-bit
syndrome of her string, and Bob decodes his string against that announced syndrome. The
`leakEC` syndrome bits are the modeled information-reconciliation leakage, priced on the cost side
of the key-rate conditions exactly like the hash length `ℓ` and the error-verification tag length
`ℓEV`.

The structure carries **no** correctness guarantee: `decode` is an arbitrary function of Bob's
string and the announced syndrome. Correctness of the reconciled key under an arbitrary attack is
enforced downstream by the error-verification test `evVerified`, not by any property of `ec`; the
security statements therefore quantify over EVERY `ec`. -/
structure ECScheme (n : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) where
  /-- Alice's public error-correction message: a `leakEC`-bit syndrome of her key string. -/
  syndrome : KeyBitString n peSel → Bits leakEC
  /-- Bob's decoder: his raw key string and Alice's announced syndrome ↦ his corrected string. -/
  decode : KeyBitString n peSel → Bits leakEC → KeyBitString n peSel

/-- **Translation equivariance of a reconciliation scheme.** For every key-round error pattern
`e : KeyBitString n peSel`, both of:

* **(i) the syndrome clause** — the announced syndrome intertwines the shift `a ↦ a + e` with a
  permutation `π` of the syndrome alphabet `Bits leakEC`;
* **(ii) the decoder clause** — shifting Alice's *and* Bob's key strings by the same `e` shifts
  Bob's reconciled string by `e`.

Both clauses are what the bilateral Bell twirl needs in order to act on the transcript by a
permutation: (i) relabels the announced-syndrome register, (ii) makes `evVerified`, the accept flag
and Bob's hashed key slot covariant.

**Clause (ii) is stated in the PAIRED form** `ec.decode (b + e) (ec.syndrome (a + e))`, not in the
`∀ b s` form that quantifies over an arbitrary syndrome letter `s`. The Kraus operators only ever
feed `ec.decode` a syndrome Alice actually announced, and `ECScheme` deliberately carries no
constraint on `ec.decode` off the syndrome image, so the `∀ b s` form would constrain behaviour
nothing in the protocol reads.

**Neither clause is implied by the other, and neither is vacuous** (build-enforced counterexamples
live alongside the Bell-twirl consumers of this predicate). -/
def ECScheme.IsTranslationEquivariant {n leakEC : ℕ} {peSel : Fin n → Bool}
    (ec : ECScheme n peSel leakEC) : Prop :=
  ∀ e : KeyBitString n peSel,
    (∃ π : Equiv.Perm (Bits leakEC),
        ∀ a : KeyBitString n peSel, ec.syndrome (a + e) = π (ec.syndrome a)) ∧
    (∀ a b : KeyBitString n peSel,
        ec.decode (b + e) (ec.syndrome (a + e)) = ec.decode b (ec.syndrome a) + e)

/-- **Relabelling the announced syndrome alphabet by a public permutation.** Alice announces
`σ (ec.syndrome a)` and Bob undoes `σ` before decoding: same leakage, same reconciled string, same
accept decision. -/
def ECScheme.relabel {n leakEC : ℕ} {peSel : Fin n → Bool} (ec : ECScheme n peSel leakEC)
    (σ : Equiv.Perm (Bits leakEC)) : ECScheme n peSel leakEC where
  syndrome := fun a => σ (ec.syndrome a)
  decode := fun b s => ec.decode b (σ.symm s)

/-- **`ECScheme.IsTranslationEquivariant` does not see a relabelling of the syndrome alphabet.**
Conjugating the clause-(i) relabel by `σ` gives the new one; clause (ii) is unchanged because Bob
undoes `σ` before decoding. -/
theorem ECScheme.IsTranslationEquivariant.relabel {n leakEC : ℕ} {peSel : Fin n → Bool}
    {ec : ECScheme n peSel leakEC} (h : ec.IsTranslationEquivariant)
    (σ : Equiv.Perm (Bits leakEC)) : (ec.relabel σ).IsTranslationEquivariant := by
  intro e
  obtain ⟨⟨π, hπ⟩, hdec⟩ := h e
  refine ⟨⟨(σ.symm.trans π).trans σ, fun a => ?_⟩, fun a b => ?_⟩
  · change σ (ec.syndrome (a + e)) = σ (π (σ.symm (σ (ec.syndrome a))))
    rw [Equiv.symm_apply_apply, ← hπ a]
  · change ec.decode (b + e) (σ.symm (σ (ec.syndrome (a + e)))) =
      ec.decode b (σ.symm (σ (ec.syndrome a))) + e
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hdec a b

/-- **Probabilistic (typical-decoding) reconciliation guarantee — a COMPLETENESS hypothesis.**

`ec.DecodesWhp errWeight εEC` says: for every Alice key string `a`, the total honest-channel
probability that Bob's syndrome-decode fails is at most `εEC`, where `errWeight a b` is the
honest conditional probability that Bob holds string `b` given Alice holds `a`.

The guarantee concerns the supplied honest conditional error law, including its noisy inputs.
It imposes no decoding bound on a different adversarial input law. Correctness under an arbitrary
attack comes from the error-verification test `evVerified`, whose charge is `2 ^ (−ℓEV)`; the
security statements hold for every `ec`. `DecodesWhp` is the completeness-side hypothesis of
`one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band`, whose failure mass is charged to the `εEC`
term of
`hoeffdingTestAbortBound`. -/
def ECScheme.DecodesWhp {n : ℕ} {peSel : Fin n → Bool} {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC)
    (errWeight : KeyBitString n peSel → KeyBitString n peSel → ℝ) (εEC : ℝ) : Prop :=
  ∀ a : KeyBitString n peSel,
    ∑ b : KeyBitString n peSel,
      (if ec.decode b (ec.syndrome a) = a then 0 else errWeight a b) ≤ εEC

/-- **The identity reconciliation scheme**: Alice announces nothing (`leakEC = 0`, so the syndrome
alphabet `Bits 0` is a singleton) and Bob keeps his raw key string. -/
def ECScheme.identity (n : ℕ) (peSel : Fin n → Bool) : ECScheme n peSel 0 where
  syndrome := fun _ => 0
  decode := fun b _ => b

/-- The identity reconciliation scheme is translation equivariant: its syndrome is constant, so the
identity permutation of the one-letter alphabet intertwines every shift, and Bob's reconciled string
`b + e` is his shifted string. -/
theorem ECScheme.identity_isTranslationEquivariant (n : ℕ) (peSel : Fin n → Bool) :
    (ECScheme.identity n peSel).IsTranslationEquivariant := by
  intro e
  exact ⟨⟨Equiv.refl _, fun _ => rfl⟩, fun _ _ => rfl⟩

/-- Bob subtracts his syndrome and adds back a fixed representative of the resulting error class. -/
@[simps]
def ECScheme.coset {n m : ℕ} {peSel : Fin n → Bool}
    (syn : KeyBitString n peSel →+ (Fin m → Bit)) (rep : (Fin m → Bit) → KeyBitString n peSel) :
    ECScheme n peSel m where
  syndrome := syn
  decode b s := b + rep (s - syn b)

/-- Every coset-representative scheme has both required translation covariance properties. -/
lemma ECScheme.coset_isTranslationEquivariant {n m : ℕ} {peSel : Fin n → Bool}
    (syn : KeyBitString n peSel →+ (Fin m → Bit)) (rep : (Fin m → Bit) → KeyBitString n peSel) :
    (coset syn rep).IsTranslationEquivariant := by
  intro e
  refine ⟨⟨Equiv.addRight (syn e), fun a => ?_⟩, fun a b => ?_⟩
  · simp [coset, map_add]
  · simp only [coset, map_add, add_sub_add_right_eq_sub]
    abel

/-- Coset decoding succeeds precisely when the actual error is its class representative. -/
lemma ECScheme.coset_decode_eq_iff {n m : ℕ} {peSel : Fin n → Bool}
    (syn : KeyBitString n peSel →+ (Fin m → Bit)) (rep : (Fin m → Bit) → KeyBitString n peSel)
    (a b : KeyBitString n peSel) :
    (coset syn rep).decode b ((coset syn rep).syndrome a) = a ↔
      rep (syn (a - b)) = a - b := by
  simp only [coset, map_sub]
  exact eq_sub_iff_add_eq'.symm

end QKD.BB84

end
