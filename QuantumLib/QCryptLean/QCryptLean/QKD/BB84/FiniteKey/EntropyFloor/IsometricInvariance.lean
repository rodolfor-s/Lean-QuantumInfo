import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.EnVDecomposition
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.SiftedRoundFactorization
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Structural key-register identification and accepted-weight factorization

The sorted key string is bijective with the physical key positions. The normalized
key factor leaves the full accepted weight on the disclosed test factor, including
empty keys and zero acceptance.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement

/-- The general-`m` sorted key-round index map is injective: it is the key-first sort
    `peSelSort`
(an `Equiv`) precomposed with the injections `Fin.castAdd` and `Fin.cast`. -/
lemma keyRoundIdx_injective {n m : ℕ} (peSel : Fin n → Bool) :
    Function.Injective (keyRoundIdx (n := n) (m := m) peSel) := by
  intro i j hij
  have h := (peSelSort peSel).injective hij
  have hv : (i : ℕ) = (j : ℕ) := by
    have := congrArg Fin.val h
    simpa [Fin.castAdd, Fin.castLE] using this
  exact Fin.ext hv

/-- **The general-`m` sorted key rounds are exactly the physical key rounds.**

`keyRoundIdx peSel` sends the `i`-th slot of the key-first sort to a round with
`peSel = false` (`peSel_keyRoundIdx`); under the count
hypothesis `hcount : KeyCount n m peSel` it is a bijection onto `{i // peSel i = false}`,
the domain of `KeyBitString`.  Injectivity is `keyRoundIdx_injective` and surjectivity
follows from the equal cardinalities.

This is the *bijection* that lets a floor on the sorted key-bit register transfer to Alice's key
string; a coarsening would not, since `Hmin(f(X)|E) ≤ Hmin(X|E)`. -/
def keyRoundSubtypeEquiv {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : KeyCount n m peSel) :
    Fin (keyRounds n m) ≃ {i : Fin n // peSel i = false} :=
  Equiv.ofBijective
    (fun i => ⟨keyRoundIdx peSel i, peSel_keyRoundIdx peSel hcount i⟩)
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
      · intro i j hij
        exact keyRoundIdx_injective peSel (congrArg Subtype.val hij)
      · rw [Fintype.card_fin, hcount])

/-- **Alice's key string, read in general-`m` sorted key-round order.**

The relabelling of the secret register that identifies `KeyBitString n peSel` with the sorted
key-bit register `Fin n_K → Fin 2`, at `n_K = keyRounds n m`.  A bijection, not a
coarsening. -/
def sortedKeyBitEquiv {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : KeyCount n m peSel) :
    KeyBitString n peSel ≃ (Fin (keyRounds n m) → Fin 2) :=
  (Equiv.arrowCongr (keyRoundSubtypeEquiv peSel hcount) (Equiv.refl (Fin 2))).symm

/-- **The general-`m` relabel is Alice's key string.**  `sortedKeyBitEquiv` carries
`aliceKeyString peSel ω` to the sorted Alice bits
`fun i => aliceBitMap ((partEquiv peSel ω).1 i)` that the general-`m` coarsen-key
operation `coarsenKey` reads; this is what makes the register identification the physically
correct one rather than an arbitrary enumeration. -/
lemma sortedKeyBitEquiv_aliceKeyString {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : KeyCount n m peSel) (ω : Signals n) :
    sortedKeyBitEquiv peSel hcount (aliceKeyString peSel ω) =
      fun i => ((partEquiv (m := m) peSel ω).1 i).1 := by
  funext i
  rw [partEquiv_apply_fst]
  rfl

/-- The test factor carries exactly the accepted weight of the paired IID component. -/
lemma siftedPERoundProd_weight_eq_pairedHaar {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel) (Q δ : ℝ)
    (ψ : DensityOp (Signal × Signal)) :
    ∑ p, ((siftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p).trace =
      ∑ x, ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ).stateMap x).trace := by
  have hA : ∑ z, ((coarsenKey (m := m) peSel xSel Q δ ψ).stateMap z).trace =
      ∑ x, ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ).stateMap x).trace := by
    rw [← CQState.quantumMarginal_trace, coarsenKey, CQState.quantumMarginal_coarsen,
      CQState.quantumMarginal_trace]
    simp only [CQState.reindex, SubDensityOp.trace, SubDensityOp.reindex, Matrix.reindex_trace]
  have hB : ∑ z, ((coarsenKey (m := m) peSel xSel Q δ ψ).stateMap z).trace =
      ∑ p, ((siftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p).trace := by
    rw [sifted_unitRegisterEmbed_coarsenKey_eq peSel xSel Q δ hcount ψ,
      CQState.tensor_sum_trace,
      CQState.tensorPower_sum_trace _ (aliceZCQState_weight_eq_one Signal ψ), one_mul]
  exact hB.symm.trans hA

end QKD.BB84.FiniteKey
