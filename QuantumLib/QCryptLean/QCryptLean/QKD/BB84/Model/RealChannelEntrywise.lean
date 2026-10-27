import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.ClassicalSemantics
import QCryptLean.QKD.BB84.Model.DePaddedQuantumStack
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # The real BB84 map as a classical kernel

The seed-averaged kernel writes the actual public tuple and retains both keys.
Selector coverage relates the analytical test to the bits publicly announced by
the program. The final identity exhibits the model's sift, measurement and
public permutation record directly on natural registers.
-/

open Quantum.Operators Quantum.Channels Quantum.Symmetry Matrix
open QKD.BB84.Measurement QKD.BB84.FiniteKey
open scoped Kronecker

noncomputable section

namespace QKD.BB84.Model

/-- The complete real output for one seed pair and one measured signal string. -/
def outIndex (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Signals n) :
    KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) :=
  if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
    Announced.passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω
  else Announced.failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω

open scoped Classical in
/-- The real classical postprocessor without a retained reference factor. -/
def classicalPostBare (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Operation (Signals n) (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)) :=
  (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
    ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel,
      classicalMap (outIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st)

/-- The retained-reference real map is the amplification of its classical kernel. -/
theorem announcedReal_eq_mapTensorId_classicalPostBare (E : Type*)
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Announced.real E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      mapTensorId (classicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q) E := rfl

open scoped Classical in
/-- On every input the real classical map depends only on the measured diagonal. -/
theorem classicalPostBare_apply (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (A : Op (Signals n)) :
    classicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q A =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ •
        ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel, ∑ ω : Signals n,
          Matrix.single (outIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st ω)
            (outIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st ω) (A ω ω) := by
  simp only [classicalPostBare, LinearMap.smul_apply, LinearMap.sum_apply, classicalMap_apply]

/-- The announced test positions are distinct. -/
theorem peRoundIdx_injective (n m : ℕ) (peSel : Fin n → Bool) :
    Function.Injective (peRoundIdx (n := n) (m := m) peSel) := by
  intro j j' h
  have h' : roundEquiv (m := m) peSel (Sum.inr j) =
      roundEquiv (m := m) peSel (Sum.inr j') := by
    rw [roundEquiv_inr, roundEquiv_inr, h]
  exact Sum.inr_injective ((roundEquiv (m := m) peSel).injective h')

/-- **The PE error counts at a general `m`, re-indexed onto the announced rounds.** Mirror of
`peErrorCount_eq`. -/
theorem peErrorCount_eq (n m : ℕ) (peSel : Fin n → Bool)
    (hcount : KeyCount n m peSel)
    (pr : Fin n → Prop) [DecidablePred pr] (x y : Bits n) :
    (Finset.univ.filter fun i : Fin n => peSel i = true ∧ pr i ∧
        x i ≠ y i).card =
      (Finset.univ.filter fun j : Fin (min n m) =>
        pr (peRoundIdx peSel j) ∧
          x (peRoundIdx peSel j) ≠
            y (peRoundIdx peSel j)).card := by
  classical
  refine (Finset.card_bij (fun j _ => peRoundIdx peSel j) ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, peSel_peRoundIdx peSel hcount j, hj.2.1,
      hj.2.2⟩
  · intro j _ j' _ h
    exact peRoundIdx_injective n m peSel h
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨j, rfl⟩ := exists_eq_peRoundIdx peSel hcount i hi.2.1
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2.2.1, hi.2.2.2⟩

/-- **The accept test at a general `m` is a function of the announced PE bits** — under the count
hypothesis. Mirror of `siftedLocalPETestPassed_jointOutcome_eq_testsPassed`. -/
theorem siftedLocalPETestPassed_jointOutcome_eq_testsPassed (n m : ℕ) (peSel xSel : Fin n →
    Bool) (δ Q : ℝ)
    (hcount : KeyCount n m peSel) (x y : Bits n) :
    siftedLocalPETestPassed peSel xSel δ Q (jointOutcome n x y) =
      testsPassed m peSel xSel δ Q
        (fun j => x (peRoundIdx peSel j))
        (fun j => y (peRoundIdx peSel j)) := by
  classical
  have hZ := peErrorCount_eq n m peSel hcount (fun i => xSel i = false) x y
  have hX := peErrorCount_eq n m peSel hcount (fun i => xSel i = true) x y
  apply Bool.eq_iff_iff.mpr
  simp only [siftedLocalPETestPassed, testsPassed, Bool.and_eq_true, decide_eq_true_eq]
  have hZ' : siftedZTestErrorCount peSel xSel (jointOutcome n x y) = _ := hZ
  have hX' : siftedXTestErrorCount peSel xSel (jointOutcome n x y) = _ := hX
  rw [hZ', hX']

/-- The Boolean accept decision agrees with the analysis test under the key-count hypothesis. -/
theorem acceptFlag_eq (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (hcount : KeyCount n m peSel)
    (t : KeyHashSeed n ℓEV peSel) (x y : Bits n) :
    acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
        (fun j => x (peRoundIdx peSel j))
        (fun j => y (peRoundIdx peSel j)) t
        (verificationTag n ℓEV peSel t (aliceRawKey n peSel (x)))
        (ec.syndrome (aliceRawKey n peSel (x)))
        (y) =
      if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t (jointOutcome n x y) then
        true else false := by
  have hpe := siftedLocalPETestPassed_jointOutcome_eq_testsPassed n m peSel xSel δ Q hcount x y
  apply Bool.eq_iff_iff.mpr
  simp only [acceptFlag, siftedLocalPEAndEVPassed, evVerified,
    aliceKeyString_jointOutcome, bobKeyString_jointOutcome, ← hpe, Bool.and_eq_true,
    decide_eq_true_eq, Bool.ite_false_right, Bool.and_true,
    and_congr_right_iff]
  intro _
  exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩

/-- Measure the signal register and perform the real classical postprocessing. -/
def realProtocolMapBare (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Operation (Signals n) (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)) :=
  (classicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp (classicalMap id)

/-- Adjoining the trivial reference commutes with the scheme's real protocol map. -/
theorem realProtocolMapBare_apply (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (A : Op (Signals n)) :
    (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
        (E := Unit) (unitRegisterEmbed n A) =
      reindex (Equiv.prodUnique _ Unit).symm (Equiv.prodUnique _ Unit).symm
        (realProtocolMapBare n m ℓ ℓEV peSel xSel leakEC ec δ Q A) := by
  change (mapTensorId (classicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q) Unit)
    (mapTensorId (classicalMap id) Unit
      (reindex (Equiv.prodUnique _ Unit).symm (Equiv.prodUnique _ Unit).symm A)) = _
  rw [mapTensorId_prodUnique, mapTensorId_prodUnique]
  rfl

/-- The real model averages the local sift, classical kernel and public permutation record. -/
theorem symReal_apply_eq_sum (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (ρ : Op (Signals n)) :
    symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ =
      (n.factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n),
        reindex (Equiv.prodUnique _ Unit).symm (Equiv.prodUnique _ Unit).symm
          (siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π
            (realProtocolMapBare n m ℓ ℓEV peSel xSel leakEC ec δ Q
              (siftedRotation n peSel xSel * permConjLin π ρ *
                (siftedRotation n peSel xSel)ᴴ))) := by
  simp only [symReal, symRealEveVisible, LinearMap.smul_apply, LinearMap.sum_apply]
  apply congrArg _
  apply Finset.sum_congr rfl
  intro π _
  change siftedPEAnnounceLinearEveVisible Unit n m ℓ ℓEV peSel leakEC π
    ((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
      (E := Unit) (siftedConjChannel Unit n peSel xSel
        (unitRegisterEmbed n (permConjLin π ρ)))) = _
  rw [siftedConjChannel_unitRegisterEmbed, realProtocolMapBare_apply]
  exact mapTensorId_prodUnique (siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π) _

end QKD.BB84.Model
