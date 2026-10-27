import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorFamilyTrace
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BadBranchConcentration
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Paired

/-! # The paired-Haar family and its physical accept mass

Reference blocks retain the actual Eve and signal-word types. Continuity and
integrability use the Frobenius matrix norm locally. The accept mass is identified
with the physical local-basis Born experiment on every component.
-/

noncomputable section

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open Quantum.DeFinetti InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix MeasureTheory
open scoped Kronecker ComplexOrder

private local instance {X : Type*} [Fintype X] : ContinuousENorm (Op X) :=
  SeminormedAddGroup.toContinuousENorm

/-- The accepted reference experiment on an IID paired component. -/
def pairedHaarPerSigmaFamily {n : ℕ} (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (Signal × Signal)) :
    CQState (Signals n) (E × Signals n) :=
  postMeasurementCQSiftedLocalPEPassFilter (E × Signals n) peSel xSel Q δ
    (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
      ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)))

/-- Every accepted family block varies continuously with its paired component. -/
theorem continuous_pairedHaarPerSigmaFamily_blocks {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    Continuous (fun ψ =>
      ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp) := by
  let : DecidableEq (Signals n) := Classical.decEq _
  let U := (siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op (Signals n))
  have hi : Continuous (fun ψ : DensityOp (Signal × Signal) =>
      ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)).toOp) :=
    continuous_pi fun i => continuous_pi fun j => DensityOp.continuous_tensorPow_entry n _ _
  have ha := (mapTensorId pre (Signals n)).continuous_of_finiteDimensional.comp hi
  by_cases h : siftedLocalPETestPassed peSel xSel δ Q x = true
  · have he : (fun ψ => ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp) =
        fun ψ => (U * mapTensorId pre (Signals n)
          ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)).toOp * Uᴴ).submatrix
            (tauOutcomeEveRefEmbedding x) (tauOutcomeEveRefEmbedding x) := by
      funext ψ
      simp only [pairedHaarPerSigmaFamily, postMeasurementCQSiftedLocalPEPassFilter,
        CQState.filterKeep, h, ite_true]
      rfl
    rw [he]
    exact ((continuous_const.matrix_mul ha).matrix_mul continuous_const).matrix_submatrix _ _
  · have he : (fun ψ => ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp) =
        fun _ : DensityOp (Signal × Signal) => (0 : Op (E × Signals n)) := by
      funext ψ
      simp [pairedHaarPerSigmaFamily, postMeasurementCQSiftedLocalPEPassFilter,
        CQState.filterKeep, h, SubDensityOp.zero]
    rw [he]
    exact continuous_const

/-- Continuous blocks on the compact state space are integrable for the paired Haar measure. -/
theorem integrable_pairedHaarPerSigmaFamily_blocks {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    Integrable (fun ψ => ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
      (haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure := by
  have := (haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).isProbability
  exact (continuous_pairedHaarPerSigmaFamily_blocks E pre hpre peSel xSel Q δ
    x).integrable_of_compactSpace

/-- **The `n`-round sifted tensor vector.**

`|w_ω⟩ = (siftedRotation n peSel xSel)ᴴ |ωIdx⟩`, entry
`(|w_ω⟩)_idx = ∏_a conj((H⊗H or 1)_{ω a, idx_a})`, the product vector `tensorFamilyVec` of the
conjugated round rows: the round factor is the `H ⊗ H` row on a PE∧X-designated round and the
standard basis vector `e_{ω a}` elsewhere.  Explicit; no `Classical.choose`. -/
def siftedTensorState {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Signals n) : Ket (Signals n) :=
  Ket.tensorFamily fun a => ⟨fun x => star (xTestPairOp (peSel a) (xSel a) (ω a) x)⟩

/-- **Design identity, row form.**  The `ωIdx` row of the sift unitary is the conjugate of the
sifted tensor vector. -/
lemma siftedRotation_row_eq_conj_tensorState {n : ℕ}
    (peSel xSel : Fin n → Bool) (ω : Signals n)
    (l : Signals n) :
    siftedRotation n peSel xSel ω l =
      (starRingEnd ℂ) ((siftedTensorState peSel xSel ω).vec l) := by
  simp only [siftedRotation, piTensorProduct_apply, siftedTensorState,
    Ket.tensorFamily, map_prod, starRingEnd_apply, star_star]

/-- **Design identity, quadratic-form version.**  The `(ωIdx, ωIdx)` diagonal entry of the
sift-conjugated operator is the Born value of `|w_ω⟩`. -/
lemma siftedRotation_conj_diag_eq_quadForm {n : ℕ}
    (peSel xSel : Fin n → Bool) (ω : Signals n)
    (M : Op (Signals n)) :
    (siftedRotation n peSel xSel * M * (siftedRotation n peSel xSel)ᴴ)
        ω ω =
      ((siftedTensorState peSel xSel ω).dag * M *
        (siftedTensorState peSel xSel ω) : ℂ) := by
  change (siftedRotation n peSel xSel * M * (siftedRotation n peSel xSel)ᴴ) ω ω =
    ∑ k, (∑ l, star ((siftedTensorState peSel xSel ω).vec l) * M l k) *
      (siftedTensorState peSel xSel ω).vec k
  simp only [mul_apply, conjTranspose_apply, siftedRotation_row_eq_conj_tensorState,
    starRingEnd_apply, star_star]

/-- **Outcome-block trace = Born value of the pre-channel's Alice–Bob marginal.**

Pushing the sift `siftedRotation peSel xSel ⊗ 1_E` through the Eve partial trace turns the
`ω`-block trace of the post-measurement CQ state into the Born value
`⟨w_ω| ρ_AB |w_ω⟩.re`, where `ρ_AB = Tr_E (pre ρ)`.

At `pre := attackChannelLinear atk` the marginal `(hpre.applyDensity ρ).partialTraceRight` is
`atk.aliceBobState ρ`. -/
theorem siftedEveConditioned_trace_eq_quadForm {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) (ω : Signals n) :
    (siftedEveConditioned E pre
        hpre peSel xSel ρ ω).trace =
      ((siftedTensorState peSel xSel ω).dag *
          ((hpre.applyDensity ρ).partialTraceRight).toOp *
        (siftedTensorState peSel xSel ω) : ℂ).re := by
  have hPT : partialTraceRight (siftedRotatedPreOutput E pre hpre peSel xSel ρ).toOp =
      siftedRotation n peSel xSel * (hpre.applyDensity ρ).partialTraceRight.toOp *
        (siftedRotation n peSel xSel)ᴴ := by
    change partialTraceRight ((siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) * pre ρ.toOp *
      (siftedRotation n peSel xSel ⊗ₖ (1 : Op E))ᴴ) = _
    rw [conjTranspose_kronecker, conjTranspose_one, partialTraceRight_kronecker_one_sandwich]
    rfl
  have he : (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace =
      (partialTraceRight (siftedRotatedPreOutput E pre hpre peSel xSel ρ).toOp ω ω).re := by
    rfl
  rw [he, hPT, siftedRotation_conj_diag_eq_quadForm]

/-- A density operator's computational diagonal entry is real. -/
private lemma densityOp_diag_ofReal (ρ : DensityOp Signal) (k : Signal) :
    ρ.toOp k k = ↑((ρ.toOp k k).re) := by
  refine Complex.ext (by rw [Complex.ofReal_re]) ?_
  rw [Complex.ofReal_im]
  have hH : ρ.toOp k k = (starRingEnd ℂ) (ρ.toOp k k) := by
    have hherm := ρ.posSemidef.isHermitian
    have hkk := congrFun (congrFun hherm k) k
    rw [Matrix.conjTranspose_apply] at hkk
    exact hkk.symm
  exact Complex.conj_eq_iff_im.mp hH.symm

/-- **Per-round double-sum collapse.**  The per-round double sum of the sifted vector against
`σ` is the single-round Born weight `siftedBorn`: on a PE∧X round it is the computational
diagonal of `H⊗H · σ · H⊗H` (`xBasisConjugate`), elsewhere the computational diagonal of `σ`. -/
private lemma sifted_perRound_double_sum (peSel xSel : Bool) (σ : DensityOp Signal)
    (k : Signal) :
    (∑ x : Signal, ∑ y : Signal,
      (starRingEnd ℂ) (star (xTestPairOp peSel xSel k x)) * σ.toOp x y *
        star (xTestPairOp peSel xSel k y)) =
      ↑(siftedBorn peSel xSel σ k) := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) (star z) = z := fun z => by
    rw [starRingEnd_apply, star_star]
  simp only [hconj]
  by_cases h : (peSel && xSel) = true
  · -- X-test round: the `H ⊗ H` conjugate's computational diagonal.
    have hU : xTestPairOp peSel xSel = hadamardPair := by
      unfold xTestPairOp; rw [ite_eq_left h]
    have hquad : (∑ x : Signal, ∑ y : Signal,
          hadamardPair k x * σ.toOp x y * star (hadamardPair k y)) =
        (hadamardPair * σ.toOp * hadamardPair) k k := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hH : star (hadamardPair k y) = hadamardPair y k := by
        have := congrFun (congrFun conjTranspose_hadamardPair y) k
        rw [Matrix.conjTranspose_apply] at this
        exact this
      rw [hH]
    rw [hU, hquad, siftedBorn]
    rw [ite_eq_left h]
    exact densityOp_diag_ofReal (xBasisConjugate σ) k
  · -- Z-test or key round: the unrotated computational diagonal.
    have hU : xTestPairOp peSel xSel = (1 : Op Signal) := by
      unfold xTestPairOp; rw [ite_eq_right h]
    have hcollapse : (∑ x : Signal, ∑ y : Signal,
          (1 : Op Signal) k x * σ.toOp x y * star ((1 : Op Signal) k y)) =
        σ.toOp k k := by
      simp only [Matrix.one_apply]
      rw [Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      · intro x _ hx; simp [Ne.symm hx]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hU, hcollapse, siftedBorn, ite_eq_right h]
    exact densityOp_diag_ofReal σ k

/-- **Per-string Born factorization.**

The quadratic form of the sifted tensor vector against `σ^{⊗n}` factors over the rounds into the
product of single-round Born weights:
`⟨w_ω| σ^{⊗n} |w_ω⟩ = ∏_i siftedBorn (peSel i) (xSel i) σ (ω i)`: the vector is a
product vector and `σ^{⊗n}` a product operator (`tensorFamily_mulVec`,
`dotProduct_tensorFamilyVec`), and each round factor is `sifted_perRound_double_sum`. -/
theorem siftedTensorState_quadForm_eq_prod_born {n : ℕ}
    (peSel xSel : Fin n → Bool) (σ : DensityOp Signal)
    (ω : Signals n) :
    ((siftedTensorState peSel xSel ω).dag * (σ.tensorPow n).toOp *
        (siftedTensorState peSel xSel ω) : ℂ) =
      ↑(∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i)) := by
  rw [← siftedRotation_conj_diag_eq_quadForm]
  change (piTensorProduct (fun a : Fin n => xTestPairOp (peSel a) (xSel a)) *
    piTensorProduct (fun _ : Fin n => σ.toOp) *
    (piTensorProduct (fun a : Fin n => xTestPairOp (peSel a) (xSel a)))ᴴ) ω ω = _
  rw [conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul,
    piTensorProduct_apply, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [← sifted_perRound_double_sum (peSel a) (xSel a) σ (ω a)]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, starRingEnd_apply, star_star]
  exact Finset.sum_comm

/-! ## 4. The unit-register accept-mass identity -/

/-- **The accept mass of a de Finetti component `σ`, through a bare CPTP pre-channel.**

The total weight retained by the fail-closed LOCC two-basis filter on the post-measurement CQ
state of the `n`-fold tensor power `σ^{⊗n}` fed through `pre`.  At `pre := attackChannelLinear atk`
this is the attacked accept mass.  The genuine-LOCC counterpart of the Bell-basis
quantity `(bb84SiftedAcceptOp n peSel Q δ · aliceBobState(σ^{⊗n})).trace.re`. -/
noncomputable def siftedPreLocalAcceptMass {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) : ℝ :=
  ∑ ω : Signals n,
    ((postMeasurementCQSiftedLocalPEPassFilter E peSel xSel Q δ
        (siftedPostMeasurementCQState E pre hpre peSel xSel (σ.tensorPow n))).stateMap
            ω).trace

/-- The total accepted paired-component weight depends only on its signal marginal. -/
theorem pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (Signal × Signal)) :
    (∑ x, ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp.trace.re) =
      siftedPreLocalAcceptMass E pre hpre peSel xSel Q δ ψ.partialTraceRight := by
  let : DecidableEq (Signals n) := Classical.decEq _
  have hm : ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)).partialTraceRight =
      ψ.partialTraceRight.tensorPow n :=
    DensityOp.ext (partialTraceRight_reindex_piTensorProduct (fun _ : Fin n => ψ.toOp))
  unfold pairedHaarPerSigmaFamily siftedPreLocalAcceptMass
  apply Finset.sum_congr rfl
  intro x _
  cases hx : siftedLocalPETestPassed peSel xSel δ Q x
  · simp [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, hx,
      SubDensityOp.zero, SubDensityOp.trace]
  · simp only [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, hx, ite_true]
    change (siftedTauEveRefConditioned E pre hpre peSel xSel
      ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)) x).toOp.trace.re =
        (siftedEveConditioned E pre hpre peSel xSel
          (ψ.partialTraceRight.tensorPow n) x).toOp.trace.re
    rw [← trace_partialTraceRight, partialTraceRight_conditioned_eq, hm]

/-- The pre-channel's accepted mass is continuous in the single-round source state. -/
theorem continuous_siftedPreLocalAcceptMass {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    Continuous (siftedPreLocalAcceptMass E pre hpre peSel xSel Q δ) := by
  let : DecidableEq (Signals n) := Classical.decEq _
  let T := (Matrix.conjLinearMap (siftedRotation n peSel xSel ⊗ₖ (1 : Op E))).comp pre
  have ht : Continuous (fun σ : DensityOp Signal => T (σ.tensorPow n).toOp) :=
    T.continuous_of_finiteDimensional.comp
      (continuous_pi fun i => continuous_pi fun j => DensityOp.continuous_tensorPow_entry n i j)
  unfold siftedPreLocalAcceptMass postMeasurementCQSiftedLocalPEPassFilter CQState.filterKeep
  apply continuous_finsetSum
  intro ω _
  dsimp only
  split_ifs
  · change Continuous (fun σ : DensityOp Signal =>
      ((T (σ.tensorPow n).toOp).submatrix (fun e => (ω, e)) (fun e => (ω, e))).trace.re)
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Complex.re_sum]
    exact continuous_finsetSum _ fun e _ => Complex.continuous_re.comp (ht.matrix_elem _ _)
  · exact continuous_const

/-- The accept mass as the accept-filtered sum of the Born values of the pre-channel's
Alice–Bob marginal against the sifted tensor vectors. -/
theorem siftedPreLocalAcceptMass_eq_sum_quadForm {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) :
    siftedPreLocalAcceptMass E pre hpre peSel xSel Q δ σ =
      ∑ ω : Signals n,
        if siftedLocalPETestPassed peSel xSel δ Q ω then
          ((siftedTensorState peSel xSel ω).dag *
              ((hpre.applyDensity (σ.tensorPow n)).partialTraceRight).toOp *
              (siftedTensorState peSel xSel ω) : ℂ).re
        else 0 := by
  apply Finset.sum_congr rfl
  intro ω _
  cases h : siftedLocalPETestPassed peSel xSel δ Q ω
  · simp [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h,
      SubDensityOp.zero, SubDensityOp.trace]
  · simp only [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h, ite_true]
    exact siftedEveConditioned_trace_eq_quadForm E pre hpre peSel xSel (σ.tensorPow n) ω

/-- **At the unit register embedding the accept mass IS the per-component accept mass.**

The one-dimensional side register leaves the Alice–Bob marginal equal to the source `σ^{⊗n}`
(`unitRegisterEmbed_partialTraceRight_toOp`), and the per-string Born factorization
(`siftedTensorState_quadForm_eq_prod_born`) turns each accepted Born value into the product of
the per-round Born weights — which is exactly the summand of
`componentAcceptProbability`.

This is the identity between the CQ-state accept mass that the paired-Haar family carries and the
scalar accept mass the split-test concentration bounds are stated for. -/
theorem unitRegisterEmbed_localAcceptMass_eq_onComponent (n : ℕ)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) :
    siftedPreLocalAcceptMass Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel
        xSel Q δ σ =
      componentAcceptProbability n peSel xSel Q δ σ := by
  rw [siftedPreLocalAcceptMass_eq_sum_quadForm,
    componentAcceptProbability]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs with h
  · have hm :
        ((isChannel_unitRegisterEmbed n).applyDensity (σ.tensorPow n)).partialTraceRight.toOp =
        (σ.tensorPow n).toOp := by
      change partialTraceRight (unitRegisterEmbed n (σ.tensorPow n).toOp) = _
      rw [unitRegisterEmbed_apply, partialTraceRight_kronecker]
      simp
    rw [hm, siftedTensorState_quadForm_eq_prod_born peSel xSel σ ω, Complex.ofReal_re]
  · rfl

end QKD.BB84.FiniteKey
