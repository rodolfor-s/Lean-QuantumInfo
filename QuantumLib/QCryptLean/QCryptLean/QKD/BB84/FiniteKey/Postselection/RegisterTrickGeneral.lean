import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabel
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PEAnnounceRelabelGeneral
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RegisterTrick
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.CovariantBound
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-!
# Bell covariance with a public permutation record

Different public permutations occupy orthogonal blocks. The pre-channel covariance,
local sift covariance and announced classical relabelling therefore preserve the trace
norm of the symmetrized real–ideal difference, with every reference register retained.
-/

noncomputable section
namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators Quantum.Channels
open Quantum.Metrics Quantum.Symmetry
open QKD.BB84.Model QKD.BB84.Measurement QKD.BB84.Model.Announced
open scoped Kronecker

/-- Different announced permutations occupy orthogonal output blocks. -/
theorem traceNorm_sum_siftedPEAnnounceLinearEveVisible {E : Type*} [Fintype E]
    {n m ℓ ℓEV : ℕ} (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)) :
    traceNorm (∑ π, siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π (F π)) =
      ∑ π, traceNorm (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π (F π)) := by
  classical
  have he : (∑ π, siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π (F π)) =
      Matrix.reindex (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC)
        (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC) (blockDiagonal F) := by
    simp only [announceEve_eq_reindex_kronecker]
    apply (Matrix.reindex (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC).symm
      (peAnnounceReferenceEquiv E n m ℓ ℓEV peSel leakEC).symm).injective
    ext ⟨x, π⟩ ⟨y, σ⟩
    simp only [reindex_apply, submatrix_apply, Matrix.sum_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply, kroneckerMap_apply, single_apply,
      blockDiagonal_apply]
    by_cases h : π = σ
    · subst σ
      simp [eq_comm]
    · have hh (τ : Equiv.Perm (Fin n)) : ¬ (τ = π ∧ τ = σ) :=
        fun ht => h (ht.1.symm.trans ht.2)
      simp [h, hh]
  rw [he, traceNorm_reindex, traceNorm_blockDiagonal]
  simp only [traceNorm_siftedPEAnnounceLinearEveVisible]

/-- Orthogonal announcement blocks remain orthogonal after adjoining a reference. -/
theorem traceNorm_announceEve_sum {E R : Type*} [Fintype E] [Fintype R]
    {n m ℓ ℓEV : ℕ} (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R)) :
    traceNorm (∑ π, mapTensorId
      (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π) R (F π)) =
      ∑ π, traceNorm (mapTensorId
        (siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC π) R (F π)) := by
  classical
  let e := (Equiv.prodAssoc
    (KeyedOutput ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC)) E R).symm
  let G := fun π => siftedPEAnnounceLinearEveVisible (E × R) n m ℓ ℓEV peSel leakEC π
    (reindex (Equiv.prodAssoc _ E R) (Equiv.prodAssoc _ E R) (F π))
  change traceNorm (∑ π, reindex e e (G π)) = ∑ π, traceNorm (reindex e e (G π))
  have he : (∑ π, reindex e e (G π)) = reindex e e (∑ π, G π) := by
    ext p q
    simp only [reindex_apply, submatrix_apply, Matrix.sum_apply]
  rw [he, traceNorm_reindex]
  simp only [traceNorm_reindex]
  exact traceNorm_sum_siftedPEAnnounceLinearEveVisible peSel leakEC _

/-- The protocol difference before appending the public permutation. -/
private def peAnnounceBareSummandInner (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (pre : Operation (Signals n) (Signals n × E)) (π : Equiv.Perm (Fin n)) :
    Operation (Signals n) (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap -
    (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).idealProtocolMap).comp
      ((siftedConjAfterPre E pre peSel xSel).comp (permConjLin π)))

open scoped Classical in
/-- The bare summand carries the physical twirl to the announced output action. -/
private theorem peAnnounceBareSummandInner_bellTwirl_conj
    (E : Type*) [Fintype E] (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (pre : Operation (Signals n) (Signals n × E)) (hcov : IsBellTwirlCovariantPre pre)
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin 4) (πsyn : Equiv.Perm (Bits leakEC))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel (g ∘ π.symm)) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel (g ∘ π.symm))
          (ec.syndrome (a + bellTwirlKeyError peSel (g ∘ π.symm))) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel (g ∘ π.symm))
    (A : Op (Signals n)) :
    peAnnounceBareSummandInner E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre π
      (signalBellUnitary g * A * (signalBellUnitary g)ᴴ) =
      (peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
        (siftedTwirlString peSel xSel (g ∘ π.symm)) πsyn ⊗ₖ (1 : Op E)) *
        peAnnounceBareSummandInner E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre π A *
        (peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (siftedTwirlString peSel xSel (g ∘ π.symm)) πsyn ⊗ₖ (1 : Op E))ᴴ := by
  classical
  have hp : permConjLin π (signalBellUnitary g * A * (signalBellUnitary g)ᴴ) =
      signalBellUnitary (g ∘ π.symm) * permConjLin π A *
        (signalBellUnitary (g ∘ π.symm))ᴴ := by
    have hg := tensorPermutation_conj_piTensorProduct π (fun i => signalBilateralPauli (g i))
    change tensorPermutation π * signalBellUnitary g * (tensorPermutation π)ᴴ =
      signalBellUnitary (g ∘ π.symm) at hg
    rw [← hg]
    simp only [permConjLin, LinearMap.coe_mk, AddHom.coe_mk, permutationRepresentation,
      conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (tensorPermutation π)ᴴ (tensorPermutation π),
      (tensorPermutation_unitary π).1, Matrix.one_mul]
  change ((real E n m ℓ ℓEV peSel xSel leakEC ec δ Q -
    ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp
    (mapTensorId (classicalMap (id : Signals n → Signals n)) E))
      (siftedConjChannel E n peSel xSel (pre (permConjLin π
        (signalBellUnitary g * A * (signalBellUnitary g)ᴴ)))) = _
  rw [hp, hcov]
  exact siftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj E n m ℓ ℓEV peSel xSel
    leakEC ec δ Q (g ∘ π.symm) πsyn hsyn hdec _

open scoped Classical in
/-- The symmetrized difference preserves the amplified trace norm under bilateral twirling. -/
theorem bellTwirl_traceNorm_invariant_stabilized_of_preCov (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (g : Fin n → Fin 4)
    (hec : ∀ π : Equiv.Perm (Fin n),
      (∃ πsyn : Equiv.Perm (Bits leakEC), ∀ a : KeyBitString n peSel,
        ec.syndrome (a + bellTwirlKeyError peSel (g ∘ π.symm)) = πsyn (ec.syndrome a)) ∧
      (∀ a b : KeyBitString n peSel,
        ec.decode (b + bellTwirlKeyError peSel (g ∘ π.symm))
            (ec.syndrome (a + bellTwirlKeyError peSel (g ∘ π.symm))) =
          ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel (g ∘ π.symm)))
    (E : Type*) [Fintype E] (pre : Operation (Signals n) (Signals n × E))
    (hcov : IsBellTwirlCovariantPre pre) (R : Type*) [Fintype R] (M : Op (Signals n × R)) :
    traceNorm (mapTensorId
      (symRealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre -
        symIdealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre) R
      ((signalBellUnitary g ⊗ₖ (1 : Op R)) * M * (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ)) =
      traceNorm (mapTensorId
        (symRealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre -
          symIdealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre) R M) := by
  classical
  let F := peAnnounceBareSummandInner E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre
  let L := siftedPEAnnounceLinearEveVisible E n m ℓ ℓEV peSel leakEC
  let Mtw := (signalBellUnitary g ⊗ₖ (1 : Op R)) * M *
    (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ
  have hs (π : Equiv.Perm (Fin n)) :
      traceNorm (mapTensorId (L π) R (mapTensorId (F π) R Mtw)) =
        traceNorm (mapTensorId (L π) R (mapTensorId (F π) R M)) := by
    rw [traceNorm_mapTensorId_siftedPEAnnounceLinearEveVisible,
      traceNorm_mapTensorId_siftedPEAnnounceLinearEveVisible]
    obtain ⟨πsyn, hsyn⟩ := (hec π).1
    let V := peAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
      (siftedTwirlString peSel xSel (g ∘ π.symm)) πsyn ⊗ₖ (1 : Op E)
    have hc := mapTensorId_conj_eq_of_covariance (F π) (Matrix.conjLinearMap V)
      (signalBellUnitary g)
      (fun A => peAnnounceBareSummandInner_bellTwirl_conj E n m ℓ ℓEV Q δ peSel xSel
        leakEC ec pre hcov π g πsyn hsyn (hec π).2 A) M
    rw [hc, mapTensorId_conjLinearMap, Matrix.conjLinearMap_apply]
    apply traceNorm_isometry_conj
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, V, conjTranspose_mul_peAnnounceBellRelabelUnitary, one_kronecker_one]
    ext i j
    simp [Matrix.one_apply]
  have hd : (symRealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre -
      symIdealEveVisible E n m ℓ ℓEV Q δ peSel xSel leakEC ec pre) =
      (n.factorial : ℂ)⁻¹ • ∑ π, (L π).comp (F π) := by
    apply LinearMap.ext
    intro A
    simp only [symRealEveVisible, symIdealEveVisible, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.sum_apply]
    let B (π : Equiv.Perm (Fin n)) :=
      mapTensorId (classicalMap (id : Signals n → Signals n)) E
        (siftedConjAfterPre E pre peSel xSel (permConjLin π A))
    change (n.factorial : ℂ)⁻¹ • (∑ π,
        L π (real E n m ℓ ℓEV peSel xSel leakEC ec δ Q (B π))) -
      (n.factorial : ℂ)⁻¹ • (∑ π,
        L π (ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q (B π))) =
      (n.factorial : ℂ)⁻¹ • ∑ π, L π
        (real E n m ℓ ℓEV peSel xSel leakEC ec δ Q (B π) -
          ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q (B π))
    simp only [map_sub, Finset.sum_sub_distrib, smul_sub]
  rw [hd]
  simp only [mapTensorId_smul, mapTensorId_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    mapTensorId_comp, LinearMap.comp_apply, traceNorm_smul]
  rw [traceNorm_announceEve_sum, traceNorm_announceEve_sum]
  exact congrArg (_ * ·) (Finset.sum_congr rfl fun π _ => hs π)

open scoped Classical in
/-- The attack-free unit-register model satisfies stabilized Bell invariance. -/
theorem bellTwirl_traceNorm_invariant_stabilized (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (hec : ec.IsTranslationEquivariant)
    (R : Type*) [Fintype R] (g : Fin n → Fin 4) (M : Op (Signals n × R)) :
    traceNorm (mapTensorId (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
      symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) R
        ((signalBellUnitary g ⊗ₖ (1 : Op R)) * M * (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ)) =
      traceNorm (mapTensorId (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) R M) :=
  bellTwirl_traceNorm_invariant_stabilized_of_preCov n m ℓ ℓEV Q δ peSel xSel leakEC ec g
    (fun π => hec (bellTwirlKeyError peSel (g ∘ π.symm))) Unit (unitRegisterEmbed n)
    (isBellTwirlCovariantPre_unitRegisterEmbed n) R M

end QKD.BB84.FiniteKey
