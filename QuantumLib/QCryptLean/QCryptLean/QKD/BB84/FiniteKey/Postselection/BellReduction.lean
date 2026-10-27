import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReference
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RegisterTrick
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CKRBound
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.PositiveBound
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.RecordedConjugation
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellReference
import QCryptLean.Quantum.Symmetry.BellReferenceAlgebra
import QCryptLean.Quantum.Symmetry.Twirl

/-!
# Bell-symmetric CKR reduction on signal registers

Permutation covariance first bounds a positive input by a purification of an invariant
marginal. Recording the bilateral Pauli action preserves the output trace norm. Native
Bell-sector domination then supplies exactly `choose (n + 3) 3`, and substate extraction
finishes the estimate. Adjoint preservation is used only for the diamond-norm lift.

The Bell group is the bilateral Pauli group, with four one-dimensional irreducible sectors;
the coefficient uses the general compact-group purification bound of Nahar et al. (2024),
not its separate product-group corollary.
-/

noncomputable section
namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators Quantum.Channels
open Quantum.Metrics Quantum.Symmetry QKD.BB84.Measurement
open scoped Kronecker ComplexOrder

open scoped Classical in
/-- Bell-invariant amplified norms admit the exact Bell de Finetti positive-input bound. -/
theorem bellSym_ckr_psd_bound_of_bellTwirl_invariant {n : ℕ} {Y : Type*} [Fintype Y]
    (Δ : Operation (Signals n) Y) (hΔ : PermutationCovariant Δ)
    (hinv : ∀ (R : Type) [Fintype R] (g : Fin n → Fin 4) (M : Op (Signals n × R)),
      traceNorm (mapTensorId Δ R
        ((signalBellUnitary g ⊗ₖ (1 : Op R)) * M * (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ)) =
        traceNorm (mapTensorId Δ R M))
    (A : Op (Signals n × Signals n)) (hA : A.PosSemidef) (ht : A.trace.re ≤ 1) :
    traceNorm (mapTensorId Δ (Signals n) A) ≤
      (Nat.choose (n + 3) 3 : ℝ) * ckrTraceNorm Δ (bellCKRDeFinettiPurification n) := by
  classical
  let : DecidableEq (Signals n) := Classical.decEq _
  obtain ⟨σ, hσ, hb⟩ := hΔ.exists_invariant_purification_bound Δ A hA ht
  let e : Signals n ≃ (Fin n → Bool × Bool) :=
    Equiv.piCongrRight fun _ => finTwoEquiv.prodCongr finTwoEquiv
  let σ' := σ.reindex e
  have hσ' : IsPermutationInvariant σ' := hσ.reindex (finTwoEquiv.prodCongr finTwoEquiv)
  let D := recordedConjugation (signalBellUnitary (n := n)) σ.purification.toOp
  have hD : D.PosSemidef := recordedConjugation_posSemidef _ _ σ.purification.posSemidef
  have hn : traceNorm (mapTensorId Δ (Signals n × (Fin n → Fin 4)) D) =
      traceNorm (mapTensorId Δ (Signals n) σ.purification.toOp) := by
    rw [traceNorm_mapTensorId_recordedConjugation]
    simp only [hinv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  have hU (g : Fin n → Fin 4) : signalBellUnitary g =
      reindex e.symm e.symm (bellTwirlUnitary g).val := by
    exact piTensorProduct_reindex (fun _ => finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
      (fun _ => finTwoEquiv.symm.prodCongr finTwoEquiv.symm) (fun i => bilateralPauli (g i))
  have hm : partialTraceRight D = reindex e.symm e.symm (bellTwirl n σ'.toOp) := by
    rw [partialTraceRight_recordedConjugation]
    have hmarg : partialTraceRight σ.purification.toOp = σ.toOp :=
      congrArg DensityOp.toOp (DensityOp.partialTraceRight_purification σ)
    rw [hmarg]
    have he : σ.toOp = reindex e.symm e.symm σ'.toOp := by
      ext x y
      simp [σ', DensityOp.reindex, reindex_apply, submatrix_apply]
    conv_lhs => rw [he]
    simp only [hU, conjTranspose_reindex, ← reindex_mul]
    ext x y
    simp only [reindex_apply, submatrix_apply, Matrix.smul_apply, Matrix.sum_apply,
      bellTwirl, twirl_apply]
  have hp (π : Equiv.Perm (Fin n)) :
      permutationRepresentation π * bellTwirl n σ'.toOp =
        bellTwirl n σ'.toOp * permutationRepresentation π := by
    have hh : permutationRepresentation π * bellTwirl n σ'.toOp *
        (permutationRepresentation π)ᴴ = bellTwirl n σ'.toOp := by
      rw [← bellTwirl_perm_conj, hσ' π]
    calc _ = (permutationRepresentation π * bellTwirl n σ'.toOp *
          (permutationRepresentation π)ᴴ) * permutationRepresentation π := by
            rw [Matrix.mul_assoc, (tensorPermutation_unitary π).1, Matrix.mul_one]
         _ = _ := by rw [hh]
  have hdom := bellSym_subnormalized_marginal_dominated n (bellTwirl n σ'.toOp)
    (posSemidef_bellTwirl σ'.posSemidef)
    (by rw [trace_bellTwirl, σ'.trace_one]; norm_num) hp (bellTwirl_idempotent σ'.toOp)
  have hd : (((Nat.choose (n + 3) 3 : ℝ) : ℂ) •
      (bellCKRDeFinettiPurification n).partialTraceRight.toOp -
        partialTraceRight D).PosSemidef := by
    rw [(isPurification_bellCKRDeFinettiPurification n).marginal, hm]
    convert hdom.submatrix e using 1
    ext x y
    simp [bellDeFinettiState, DensityOp.toSubDensityOp, DensityOp.reindex,
      Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sub_apply, e, Equiv.piCongrRight,
      Equiv.prodCongr]
  have hs := traceNorm_mapTensorId_substate_bound Δ D hD (bellCKRDeFinettiPurification n)
    (isPurification_bellCKRDeFinettiPurification n).isPure (Nat.choose (n + 3) 3 : ℝ)
    (by exact_mod_cast Nat.choose_pos (by omega)) hd
  rw [hn] at hs
  exact hb.trans hs

open scoped Classical in
/-- Adjoint preservation lifts the positive Bell bound to the all-operator diamond norm. -/
theorem diamondNorm_le_bellDim_mul_ckrTraceNorm {n : ℕ} {Y : Type*} [Fintype Y]
    (Δ : Operation (Signals n) Y) (hΔ : PermutationCovariant Δ)
    (hstar : ∀ A, Δ Aᴴ = (Δ A)ᴴ)
    (hinv : ∀ (R : Type) [Fintype R] (g : Fin n → Fin 4) (M : Op (Signals n × R)),
      traceNorm (mapTensorId Δ R
        ((signalBellUnitary g ⊗ₖ (1 : Op R)) * M * (signalBellUnitary g ⊗ₖ (1 : Op R))ᴴ)) =
        traceNorm (mapTensorId Δ R M)) :
    diamondNorm Δ ≤ (Nat.choose (n + 3) 3 : ℝ) *
      ckrTraceNorm Δ (bellCKRDeFinettiPurification n) :=
  diamondNorm_le_of_traceNorm_mapTensorId_le Δ hstar _
    (fun A hA ht => bellSym_ckr_psd_bound_of_bellTwirl_invariant Δ hΔ hinv A hA ht)

end QKD.BB84.FiniteKey
