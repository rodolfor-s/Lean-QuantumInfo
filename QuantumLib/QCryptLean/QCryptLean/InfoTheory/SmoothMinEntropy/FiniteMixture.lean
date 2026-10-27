import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleRegularization
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.MixtureDistance
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SmoothTransport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Native finite subconvex CQ mixtures and extended smooth-entropy floors -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {C Q I : Type*} [Fintype C] [Fintype Q] [Fintype I]

/-- A finite subconvex combination of CQ states, including zero weights and empty families. -/
def CQState.subconvexMixture (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (ρ : I → CQState C Q) : CQState C Q :=
  CQState.ofBlocks (fun c => ∑ i, (p i : ℂ) • ((ρ i).stateMap c).toOp)
    (fun c => Matrix.posSemidef_sum _ fun i _ =>
      ((ρ i).stateMap c).posSemidef.smul (RCLike.ofReal_nonneg.mpr (hp i)))
    (by
      simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul, smul_eq_mul,
        Complex.re_ofReal_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      exact (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ρ i).weight_le_one (hp i)).trans (by simpa using hs))

/-- Blockwise subconvex combinations also combine the joint operators. -/
theorem CQState.toJointOp_eq_sum_of_blocks [DecidableEq C]
    (p : I → ℝ) (ρ : I → CQState C Q) (σ : CQState C Q)
    (hσ : ∀ c, (σ.stateMap c).toOp = ∑ i, (p i : ℂ) • ((ρ i).stateMap c).toOp) :
    σ.toJointOp = ∑ i, (p i : ℂ) • (ρ i).toJointOp := by
  ext ⟨q, c⟩ ⟨r, d⟩
  simp only [CQState.toJointOp, Matrix.blockDiagonal_apply, hσ, Matrix.sum_apply,
    Matrix.smul_apply]
  split_ifs <;> simp

/-- A common feasible scale is retained under a subconvex combination. -/
theorem IsFeasible.subconvexMixture
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (ρ : I → CQState C Q) (τ : CQState C Q)
    (hτ : ∀ c, (τ.stateMap c).toOp = ∑ i, (p i : ℂ) • ((ρ i).stateMap c).toOp)
    (σ : I → SubDensityOp Q) (ω : SubDensityOp Q)
    (hω : OpLe (∑ i, (p i : ℂ) • (σ i).toOp) ω.toOp)
    {t : ℝ} (ht : 0 ≤ t) (h : ∀ i, IsFeasible (ρ i) (σ i) t) :
    IsFeasible τ ω t := by
  refine ⟨ht, fun c v => ?_⟩
  have hquad : ∀ (M : I → Op Q),
      (quadraticForm (∑ i, (p i : ℂ) • M i) v).re =
        ∑ i, p i * (quadraticForm (M i) v).re := by
    intro M
    simp only [quadraticForm, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
      dotProduct_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul]
  rw [hτ c, hquad]
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left ((h i).2 c v) (hp i)
  apply hh.trans
  have hn := mul_le_mul_of_nonneg_left (hω v) ht
  simpa only [quadraticForm, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
    dotProduct_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul,
    Finset.mul_sum, mul_left_comm (p _)] using hn

/-- Every common extended smooth-entropy floor passes to a finite subconvex CQ mixture. -/
theorem smoothMinEntropy_subconvexMixture_floor [DecidableEq C] [Nonempty C] [Nonempty Q]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (ρ : I → CQState C Q) (τ : CQState C Q)
    (hτ : ∀ c, (τ.stateMap c).toOp = ∑ i, (p i : ℂ) • ((ρ i).stateMap c).toOp)
    (σ : I → SubDensityOp Q) (ω : SubDensityOp Q)
    (hω : OpLe (∑ i, (p i : ℂ) • (σ i).toOp) ω.toOp)
    {ε : ℝ} (hε : 0 ≤ ε) {K : ENNReal}
    (hK : ∀ i, K ≤ smoothMinEntropy ε (ρ i) (σ i)) :
    K ≤ smoothMinEntropy ε τ ω := by
  classical
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hex (i : I) : ∃ υ : CQState C Q, (ρ i).purifiedDistance υ ≤ ε ∧
      IsFeasible υ (σ i) (2 ^ (-(r : ℝ))) := by
    obtain ⟨υ, hv⟩ := lt_iSup_iff.mp (hr.trans_le (hK i))
    obtain ⟨hd, he⟩ := lt_iSup_iff.mp hv
    have he' : ENNReal.ofReal (r : ℝ) < minEntropy υ (σ i) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using he
    obtain ⟨a, ha, har⟩ := exists_isFeasible_lt_rpow_of_lt_minEntropy υ (σ i) he'
    exact ⟨υ, hd, ha.mono har.le⟩
  choose υ hd hf using hex
  let τ' := CQState.subconvexMixture p hp hs υ
  have hτ' (c : C) : (τ'.stateMap c).toOp = ∑ i, (p i : ℂ) • ((υ i).stateMap c).toOp := rfl
  have hdist : τ.purifiedDistance τ' ≤ ε :=
    purifiedDistance_subconvex_mixture p hp hs
      (fun i => (ρ i).toJointDensity) (fun i => (υ i).toJointDensity)
      τ.toJointDensity τ'.toJointDensity
      (CQState.toJointOp_eq_sum_of_blocks p ρ τ hτ)
      (CQState.toJointOp_eq_sum_of_blocks p υ τ' hτ') hε hd
  have hfeas := IsFeasible.subconvexMixture p hp υ τ' hτ' σ ω hω
    (Real.rpow_nonneg (by norm_num) _) hf
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (ofReal_le_minEntropy_of_isFeasible τ' ω (r : ℝ) hfeas).trans
      (minEntropy_le_smoothMinEntropy_of_purifiedDistance_le τ τ' ω hdist)

/-- Classical coarsening commutes with finite subconvex mixtures. -/
theorem CQState.coarsen_subconvexMixture {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I]
    (g : C → D) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (f : I → CQState C Q) :
    (CQState.subconvexMixture p hp hs f).coarsen g =
      CQState.subconvexMixture p hp hs (fun i => (f i).coarsen g) := by
  ext d a b
  change (∑ c, if g c = d then (∑ i, (p i : ℂ) • ((f i).stateMap c).toOp) else 0) a b =
    (∑ i, (p i : ℂ) • (∑ c, if g c = d then ((f i).stateMap c).toOp else 0)) a b
  apply congrArg (fun M : Op Q => M a b)
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

end InfoTheory.SmoothMinEntropy
