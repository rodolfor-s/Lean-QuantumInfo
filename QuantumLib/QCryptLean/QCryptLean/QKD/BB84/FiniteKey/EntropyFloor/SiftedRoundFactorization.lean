import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.KroneckerSandwich
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRotationFactorization
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQCore
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Paired

/-! # Round factorization of the sifted reference experiment

Each X-test round is measured after a local Hadamard pair. The reference blocks of
an IID input factor over the actual round positions; no reversal or dimension cast
is required. The accepted test factor is independent of Alice's retained key.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement Matrix
open scoped Kronecker

/-- The single-round reference block after the physical, local sift. -/
def xTestRoundRefBlock (ψ : DensityOp (Signal × Signal)) (b x : Bool) (k : Signal) :
    SubDensityOp Signal :=
  singleRoundConditioned Signal
    (UnitaryOp.evolve (⟨xTestPairOp b x ⊗ₖ (1 : Op Signal), mem_unitaryGroup_iff'.mpr (by
      rw [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
        ← mul_kronecker_mul, conjTranspose_mul_xTestPairOp, one_mul, one_kronecker_one])⟩ :
          UnitaryOp (Signal × Signal)) ψ) k

/-- Conditioning the rotated state contracts only the single signal coordinate. -/
lemma xTestRoundRefBlock_toOp_apply (ψ : DensityOp (Signal × Signal)) (b x : Bool)
    (k r r' : Signal) :
    (xTestRoundRefBlock ψ b x k).toOp r r' =
      ∑ t : Signal, ∑ t' : Signal,
        xTestPairOp b x k t * ψ.toOp (t, r) (t', r') * star (xTestPairOp b x k t') := by
  change ((xTestPairOp b x ⊗ₖ (1 : Op Signal)) * ψ.toOp *
    (xTestPairOp b x ⊗ₖ (1 : Op Signal))ᴴ) (k, r) (k, r') = _
  rw [conjTranspose_kronecker, conjTranspose_one, kronecker_one_sandwich_apply]
  rfl

/-- Non-X-test rounds have exactly the computational key-round reference block. -/
lemma xTestRoundRefBlock_eq_of_not_xTest (ψ : DensityOp (Signal × Signal))
    (b x : Bool) (h : (b && x) = false) (k : Signal) :
    xTestRoundRefBlock ψ b x k = siftedRoundRefBlock ψ false k := by
  apply SubDensityOp.ext
  ext r r'
  rw [xTestRoundRefBlock_toOp_apply, siftedRoundRefBlock_false_toOp_apply]
  simp [xTestPairOp, h, one_apply]

/-- All sifted outcomes together retain unit weight. -/
lemma sum_trace_xTestRoundRefBlock (ψ : DensityOp (Signal × Signal)) (b x : Bool) :
    ∑ k, (xTestRoundRefBlock ψ b x k).trace = 1 :=
  singleRoundConditioned_weight_sum Signal _

/-- The trivial attack contributes only its one-point reference coordinate. -/
lemma siftedTauEveRefConditioned_trivial_entry {n : ℕ}
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (Signal × Signal)) (ω : Signals n)
    (i j : Unit × Signals n) :
    (siftedTauEveRefConditioned Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)) ω).toOp i j =
      ∑ sa : Signals n, ∑ sc : Signals n,
        siftedRotation n peSel xSel ω sa *
          (ψ.tensorPow n).toOp (fun a => (sa a, i.2 a)) (fun a => (sc a, j.2 a)) *
          star (siftedRotation n peSel xSel ω sc) := by
  let : DecidableEq (Signals n) := Classical.decEq _
  simp only [siftedTauEveRefConditioned, SubDensityOp.submatrix, DensityOp.toSubDensityOp,
    siftedTauPreOutputDensity, UnitaryOp.evolve, tauOutputDensity, IsChannel.applyDensity,
    submatrix_apply, tauOutcomeEveRefEmbedding]
  rw [conjTranspose_kronecker, conjTranspose_one, kronecker_one_sandwich_apply]
  simp [Fintype.sum_prod_type, mapTensorId_apply, unitRegisterEmbed, reindex_apply,
    submatrix_apply, DensityOp.reindex, kroneckerMap_apply, conjTranspose_apply,
    one_apply, pairFunctions, Equiv.arrowProdEquivProdArrow]

/-- The sifted IID contraction is the product of the single-round contractions. -/
lemma siftedTrivial_doubleSum_eq_prod {n : ℕ}
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (Signal × Signal)) (ω ri rj : Signals n) :
    (∑ sa : Signals n, ∑ sc : Signals n,
      siftedRotation n peSel xSel ω sa *
        (ψ.tensorPow n).toOp (fun a => (sa a, ri a)) (fun a => (sc a, rj a)) *
        star (siftedRotation n peSel xSel ω sc)) =
      ∏ a : Fin n, (xTestRoundRefBlock ψ (peSel a) (xSel a) (ω a)).toOp (ri a) (rj a) := by
  simp only [xTestRoundRefBlock_toOp_apply, siftedRotation, DensityOp.tensorPow,
    DensityOp.tensorFamily, piTensorProduct_apply, star_prod, ← Finset.prod_mul_distrib]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The complete reference block factors in the natural order of the round positions. -/
theorem siftedUnitRegisterEmbed_tauConditioned_eq_tensorFamily {n : ℕ}
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (Signal × Signal)) (ω : Signals n) :
    siftedTauEveRefConditioned Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)) ω =
      (SubDensityOp.tensorFamily fun a => xTestRoundRefBlock ψ (peSel a) (xSel a) (ω a)).reindex
        (Equiv.uniqueProd (Signals n) Unit).symm := by
  apply SubDensityOp.ext
  ext i j
  rw [siftedTauEveRefConditioned_trivial_entry, siftedTrivial_doubleSum_eq_prod]
  rfl

/-- The parameter-estimation verdict depends only on disclosed test outcomes. -/
theorem siftedLocalPETestPassed_key_indep {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ω ω' : Signals n)
    (h : ∀ a, peSel a = true → ω a = ω' a) :
    siftedLocalPETestPassed peSel xSel δ Q ω =
      siftedLocalPETestPassed peSel xSel δ Q ω' := by
  have hZ : siftedZTestErrorCount peSel xSel ω = siftedZTestErrorCount peSel xSel ω' := by
    unfold siftedZTestErrorCount
    congr 1
    apply Finset.filter_congr
    intro i _
    by_cases hpe : peSel i = true
    · rw [h i hpe]
    · simp [hpe]
  have hX : siftedXTestErrorCount peSel xSel ω = siftedXTestErrorCount peSel xSel ω' := by
    unfold siftedXTestErrorCount
    congr 1
    apply Finset.filter_congr
    intro i _
    by_cases hpe : peSel i = true
    · rw [h i hpe]
    · simp [hpe]
  simp only [siftedLocalPETestPassed, hZ, hX]

/-- Extend the test outcomes arbitrarily on key rounds to evaluate the test verdict. -/
def siftedPEPass {n m : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (p : Signals (min n m)) : Bool :=
  siftedLocalPETestPassed peSel xSel δ Q
    ((partEquiv (m := m) peSel).symm ((fun _ => (0, 0)), p))

/-- The verdict factors through the sorted test-round restriction. -/
lemma siftedLocalPETestPassed_eq_pePass {n m : ℕ} (peSel xSel : Fin n → Bool)
    (δ Q : ℝ) (hcount : KeyCount n m peSel) (ω : Signals n) :
    siftedLocalPETestPassed peSel xSel δ Q ω =
      siftedPEPass (m := m) peSel xSel δ Q (partEquiv (m := m) peSel ω).2 := by
  unfold siftedPEPass
  apply siftedLocalPETestPassed_key_indep
  intro a ha
  obtain ⟨j, rfl⟩ := exists_eq_peRoundIdx peSel hcount a ha
  rw [partEquiv_symm_apply_peIdx, partEquiv_apply_snd]

/-- The accepted reference product over the sorted test rounds, independent of the key. -/
def siftedPERoundProd {n m : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ψ : DensityOp (Signal × Signal)) :
    CQState (Signals (min n m)) (Signals (min n m)) :=
  CQState.filterKeep (siftedPEPass (m := m) peSel xSel δ Q)
    { stateMap := fun p => SubDensityOp.tensorFamily
        (fun j => xTestRoundRefBlock ψ true (xSel (peRoundIdx peSel j)) (p j))
      weight_le_one := by
        simp only [SubDensityOp.trace_tensorFamily]
        rw [← Fintype.prod_sum (fun (j : Fin (min n m)) (k : Signal) =>
          (xTestRoundRefBlock ψ true (xSel (peRoundIdx peSel j)) k).trace)]
        simp only [sum_trace_xTestRoundRefBlock, Finset.prod_const_one, le_refl] }

end QKD.BB84.FiniteKey
