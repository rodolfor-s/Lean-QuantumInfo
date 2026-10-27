import QCryptLean.Math.Analysis.ImaginaryIdentityTheorem
import QCryptLean.Math.Probability.UnitaryHaarTransport
import QCryptLean.Math.SpectralTheory.HermitianCpow
import QCryptLean.Math.SpectralTheory.HermitianCpowAnalytic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.CommutantAlgebra
import QCryptLean.Quantum.Symmetry.UnitaryCentralizerTensorPowers

/-! # Unitary Centralizer -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Math.SpectralTheory
open scoped MatrixOrder ComplexOrder Topology
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- Commuting with unitary centralizer powers implies commuting with all its powers. -/
theorem commute_tensorPow_of_unitaryCentralizer
    (S : Set (Op X)) (hS : ∀ M ∈ S, Mᴴ ∈ S) (T : Op (Fin k → X))
    (hU : ∀ U : Matrix.unitaryGroup X ℂ,
      (∀ M ∈ S, Commute M (U : Op X)) → Commute (Op.tensorPow (U : Op X) k) T)
    (A : Op X) (hAS : ∀ M ∈ S, Commute M A) : Commute (Op.tensorPow A k) T := by
  classical
  have differentiable_tensorPow {n : ℕ} {f : ℂ → Op X} (hf : Differentiable ℂ f) :
      Differentiable ℂ (fun z => Op.tensorPow (f z) n) := by
    apply differentiable_pi.mpr
    intro i
    apply differentiable_pi.mpr
    intro j
    simp only [Op.tensorPow_apply]
    exact Differentiable.fun_finsetProd fun k _ =>
      differentiable_pi.mp (differentiable_pi.mp hf _) _
  have hermCpow_commute  {A T : Op X} (hA : A.IsHermitian)
      (h : Commute A T) (z : ℂ) : Commute (hermCpow hA z) T := by
    let e := Unitary.conjStarAlgAut ℂ (Op X) hA.eigenvectorUnitary
    have hdiag : e.symm A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
      exact (congrArg e.symm hA.spectral_theorem).trans (e.symm_apply_apply _)
    have h' := h.map e.symm
    rw [hdiag] at h'
    have hp := Quantum.Symmetry.commute_diagonal_map _ (fun x : ℂ => x ^ z) h'
    simpa only [StarAlgEquiv.apply_symm_apply, Function.comp_def, hermCpow, e] using hp.map e
  have commute_tensorPow_of_unitaryCentralizer_of_posDef {n : ℕ} (S : Set (Op X))
      (T : Op (Fin n → X))
      (hU : ∀ U : Matrix.unitaryGroup X ℂ,
        (∀ M ∈ S, Commute M (U : Op X)) → Commute (Op.tensorPow (U : Op X) n) T)
      {P : Op X} (hP : P.PosDef) (hPS : ∀ M ∈ S, Commute M P) :
      Commute (Op.tensorPow P n) T := by
    have hpow := differentiable_tensorPow (n := n)
      (hermCpow_differentiable hP.isHermitian fun i => (hP.eigenvalues_pos i).ne')
    have hdiff := (differentiable_matrix_mul_right T hpow).sub
      (differentiable_matrix_mul_left T hpow)
    ext i j
    have hz := Complex.eq_zero_of_differentiable_of_eq_zero_on_imaginary
      (differentiable_pi.mp (differentiable_pi.mp hdiff i) j) (by
        intro t
        have hu := Matrix.PosDef.hermCpow_mem_unitary hP (w := (t : ℂ) * Complex.I) (by simp)
        have hc := hU ⟨hermCpow hP.isHermitian ((t : ℂ) * Complex.I), hu⟩ (by
          intro M hM
          exact (hermCpow_commute hP.isHermitian (hPS M hM).symm _).symm)
        exact congrFun (congrFun (sub_eq_zero.mpr hc.eq) i) j)
    have h := congrFun hz 1
    simpa only [Pi.sub_apply, hermCpow_one, Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] using h
  have conjTranspose_mem_commutant  (S : Set (Op X))
      (hS : ∀ M ∈ S, Mᴴ ∈ S) {A : Op X} (hA : ∀ M ∈ S, Commute M A) :
      ∀ M ∈ S, Commute M Aᴴ := by
    intro M hM
    have h := congrArg Matrix.conjTranspose (hA Mᴴ (hS M hM)).eq
    simpa only [Commute, SemiconjBy, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using h.symm
  have nonsing_inv_commute_of_isUnit  {A M : Op X}
      (hA : IsUnit A) (h : Commute M A) : Commute M A⁻¹ := by
    let := hA.invertible
    simpa only [Matrix.invOf_eq_nonsing_inv] using h.invOf_right
  have commute_tensorPow_of_unitaryCentralizer_of_isUnit {n : ℕ}
      (S : Set (Op X)) (hS : ∀ M ∈ S, Mᴴ ∈ S) (T : Op (Fin n → X))
      (hU : ∀ U : Matrix.unitaryGroup X ℂ,
        (∀ M ∈ S, Commute M (U : Op X)) → Commute (Op.tensorPow (U : Op X) n) T)
      {A : Op X} (hA : IsUnit A) (hAS : ∀ M ∈ S, Commute M A) :
      Commute (Op.tensorPow A n) T := by
    have hgram : (Aᴴ * A).PosDef :=
      (Matrix.posSemidef_conjTranspose_mul_self A).posDef_iff_isUnit.mpr
        ((isUnit_star.mpr hA).mul hA)
    let P := CFC.sqrt (Aᴴ * A)
    have hP : P.PosDef := hgram.isStrictlyPositive.sqrt.posDef
    have hPP : P * P = Aᴴ * A := CFC.sqrt_mul_sqrt_self _ hgram.posSemidef.nonneg
    have hPS (M : Op X) (hM : M ∈ S) : Commute M P := by
      have hc := ((conjTranspose_mem_commutant S hS hAS M hM).mul_right (hAS M hM)).symm
      -- Apply spectral calculus to the commutation relation for `Aᴴ * A`.
      exact ((hc.cfcₙ_nnreal NNReal.sqrt).eq).symm
    let U := A * P⁻¹
    have hUmem : U ∈ Matrix.unitaryGroup X ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      change (A * P⁻¹)ᴴ * (A * P⁻¹) = 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP.isHermitian.eq]
      calc P⁻¹ * Aᴴ * (A * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by rw [hPP]; simp [mul_assoc]
        _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [mul_assoc]
        _ = 1 := by rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit),
          Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit), one_mul]
    have hUP : U * P = A := by
      rw [mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit),
        mul_one]
    rw [← hUP, Op.tensorPow_mul]
    apply Commute.mul_left
    · apply hU ⟨U, hUmem⟩
      intro M hM
      exact (hAS M hM).mul_right (nonsing_inv_commute_of_isUnit hP.isUnit (hPS M hM))
    · exact commute_tensorPow_of_unitaryCentralizer_of_posDef S T hU hP hPS
  have hdense : Dense (Set.ofPred fun z : ℂ => IsUnit (A + z • (1 : Op X))) := by
    have hd := Dense.sdiff_finite dense_univ (-A).finite_spectrum
    have hs : Set.univ \ spectrum ℂ (-A) =
        Set.ofPred (fun z : ℂ => IsUnit (A + z • (1 : Op X))) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, spectrum.mem_iff, not_not,
        Algebra.algebraMap_eq_smul_one, sub_neg_eq_add, add_comm, Set.mem_ofPred_eq]
    rwa [hs] at hd
  have hp : Continuous (fun z : ℂ => Op.tensorPow (A + z • (1 : Op X)) k) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun a : ℂ => ∏ t : Fin k, (A + a • 1) (i t) (j t))
    apply continuous_finsetProd
    intro a _
    exact (continuous_apply _).comp ((continuous_apply _).comp
      (continuous_const.add (continuous_id.smul continuous_const)))
  have heq : (fun z : ℂ => Op.tensorPow (A + z • (1 : Op X)) k * T) =
      (fun z : ℂ => T * Op.tensorPow (A + z • (1 : Op X)) k) := by
    apply Continuous.ext_on hdense
      (hp.matrix_mul continuous_const) (continuous_const.matrix_mul hp)
    intro z hz
    exact (commute_tensorPow_of_unitaryCentralizer_of_isUnit S hS T hU hz fun M hM =>
      (hAS M hM).add_right ((Commute.one_right M).smul_right z)).eq
  simpa only [Commute, SemiconjBy, zero_smul, add_zero] using congrFun heq 0

end Quantum.Symmetry
