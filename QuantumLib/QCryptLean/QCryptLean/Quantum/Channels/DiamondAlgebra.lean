import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondBounds
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.PositiveBound
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Diamond Algebra -/


noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

private theorem diamondNorm_reindex_le {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (a : A ≃ A') (b : B ≃ B') (Ψ : Operation A B) :
    diamondNorm ((Matrix.reindexLinearEquiv ℂ ℂ b b).toLinearMap.comp
      (Ψ.comp (Matrix.reindexLinearEquiv ℂ ℂ a.symm a.symm).toLinearMap)) ≤
        diamondNorm Ψ := by
  apply diamondNorm_le_of_forall
  intro M hM
  obtain ⟨N, rfl⟩ := (Matrix.reindexLinearEquiv ℂ ℂ
    (a.prodCongr a) (a.prodCongr a)).surjective M
  change traceNorm (Matrix.reindex (a.prodCongr a) (a.prodCongr a) N) ≤ 1 at hM
  change traceNorm (Quantum.Channels.mapTensorId _ A'
    (Matrix.reindex (a.prodCongr a) (a.prodCongr a) N)) ≤ _
  rw [mapTensorId_reindex, traceNorm_reindex]
  rw [traceNorm_reindex] at hM
  exact traceNorm_mapTensorId_le_diamondNorm Ψ N hM

/-- Relabelling the input and output registers preserves the intrinsic diamond norm. -/
theorem diamondNorm_reindex {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (e : X ≃ X') (f : Y ≃ Y') (Φ : Operation X Y) :
    diamondNorm ((Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap.comp
      (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap)) =
        diamondNorm Φ := by
  apply le_antisymm (diamondNorm_reindex_le e f Φ)
  have h := diamondNorm_reindex_le e.symm f.symm
    ((Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap.comp
      (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap))
  have he : (Matrix.reindexLinearEquiv ℂ ℂ f.symm f.symm).toLinearMap.comp
      (((Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap.comp
        (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap)).comp
          (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) = Φ := by
    apply LinearMap.ext
    intro M
    apply Matrix.ext
    intro i j
    change Φ (fun x y => M (e.symm (e x)) (e.symm (e y)))
      (f.symm (f i)) (f.symm (f j)) = Φ M i j
    simp only [Equiv.symm_apply_apply]
  simp only [Equiv.symm_symm] at h
  rw [he] at h
  exact h

/-- Scalar multiplication scales the diamond norm by the complex norm. -/
@[simp] theorem diamondNorm_smul (c : ℂ) (Φ : Operation X Y) :
    diamondNorm (c • Φ) = ‖c‖ * diamondNorm Φ := by
  have upper (d : ℂ) (Ψ : Operation X Y) :
      diamondNorm (d • Ψ) ≤ ‖d‖ * diamondNorm Ψ := by
    apply diamondNorm_le_of_forall
    intro A hA
    change traceNorm (d • Quantum.Channels.mapTensorId Ψ X A) ≤ _
    rw [traceNorm_smul]
    exact mul_le_mul_of_nonneg_left (traceNorm_mapTensorId_le_diamondNorm Ψ A hA)
      (norm_nonneg d)
  apply le_antisymm (upper c Φ)
  by_cases hc : c = 0
  · simp [hc]
  have h := upper c⁻¹ (c • Φ)
  rw [inv_smul_smul₀ hc, norm_inv] at h
  exact (le_inv_mul_iff₀ (norm_pos_iff.mpr hc)).mp h

/-- Negation preserves the diamond norm. -/
@[simp] theorem diamondNorm_neg (Φ : Operation X Y) : diamondNorm (-Φ) = diamondNorm Φ := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using diamondNorm_smul (-1) Φ

/-- The diamond norm of a difference is bounded by the sum of the norms. -/
theorem diamondNorm_sub_le (Φ Ψ : Operation X Y) :
    diamondNorm (Φ - Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := by
  simpa only [sub_eq_add_neg, diamondNorm_neg] using diamondNorm_add_le Φ (-Ψ)

/-- The normalized diamond distance is symmetric. -/
theorem diamondDist_comm (Φ Ψ : Operation X Y) : diamondDist Φ Ψ = diamondDist Ψ Φ := by
  unfold diamondDist
  rw [← neg_sub Ψ Φ, diamondNorm_neg]

/-- The normalized diamond distance satisfies the triangle inequality. -/
theorem diamondDist_triangle (Φ Ψ Λ : Operation X Y) :
    diamondDist Φ Λ ≤ diamondDist Φ Ψ + diamondDist Ψ Λ := by
  have h := diamondNorm_add_le (Φ - Ψ) (Ψ - Λ)
  rw [sub_add_sub_cancel] at h
  unfold diamondDist
  linarith

/-- Common channel postprocessing contracts the diamond norm of an arbitrary operation. -/
theorem IsChannel.diamondNorm_comp_le {Ψ : Operation Y Z} (hΨ : IsChannel Ψ)
    (Φ : Operation X Y) : diamondNorm (Ψ.comp Φ) ≤ diamondNorm Φ := by
  apply diamondNorm_le_of_forall
  intro A hA
  rw [mapTensorId_comp, LinearMap.comp_apply]
  exact (traceNorm_mapTensorId_le Ψ hΨ _).trans
    (traceNorm_mapTensorId_le_diamondNorm Φ A hA)

/-- A channel on a nonempty input has diamond norm one. -/
theorem IsChannel.diamondNorm_eq_one [Nonempty X] {Φ : Operation X Y} (hΦ : IsChannel Φ) :
    diamondNorm Φ = 1 := by
  classical
  let ρ := DensityOp.maxMixed (X := X × X)
  have hn : traceNorm ρ.toOp = 1 := by
    rw [traceNorm_of_posSemidef _ ρ.posSemidef, ρ.trace_one, Complex.one_re]
  have hout : traceNorm (Quantum.Channels.mapTensorId Φ X ρ.toOp) = 1 := by
    rw [traceNorm_of_posSemidef _ (hΦ.mapTensorId.1.posSemidef ρ.posSemidef),
      hΦ.mapTensorId.2, ρ.trace_one, Complex.one_re]
  apply le_antisymm
  · apply diamondNorm_le_of_forall
    intro A hA
    exact (traceNorm_mapTensorId_le Φ hΦ A).trans hA
  · rw [← hout]
    exact traceNorm_mapTensorId_le_diamondNorm Φ ρ.toOp hn.le

/-- The normalized distance between two channels is at most one. -/
theorem IsChannel.diamondDist_le_one {Φ Ψ : Operation X Y}
    (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : diamondDist Φ Ψ ≤ 1 := by
  have h := diamondNorm_sub_le_two hΦ hΨ
  unfold diamondDist
  linarith

/-- Bounds on normalized square-reference states control an adjoint-preserving operation. -/
theorem diamondNorm_le_of_density_bound (Φ : Operation X Y)
    (hΦ : ∀ A, Φ Aᴴ = (Φ A)ᴴ) (b : ℝ) (hb : 0 ≤ b)
    (hρ : ∀ ρ : DensityOp (X × X), traceNorm (Quantum.Channels.mapTensorId Φ X ρ.toOp) ≤ b) :
    diamondNorm Φ ≤ b := by
  apply diamondNorm_le_of_traceNorm_mapTensorId_le Φ hΦ b
  intro A hA ht
  by_cases hz : A.trace = 0
  · rw [hA.trace_eq_zero_iff.mp hz, map_zero, traceNorm_zero]
    exact hb
  have hn := Complex.nonneg_iff.mp hA.trace_nonneg
  have hp : 0 < A.trace.re := lt_of_le_of_ne hn.1
    (fun he => hz (Complex.ext he.symm hn.2.symm))
  let ρ : DensityOp (X × X) :=
    ⟨A.trace⁻¹ • A, hA.smul (inv_nonneg.mpr hA.trace_nonneg), by
      rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hz]⟩
  have he : A = A.trace • ρ.toOp := by
    change A = A.trace • (A.trace⁻¹ • A)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  have hnorm : ‖A.trace‖ = A.trace.re := by
    have hr : (A.trace.re : ℂ) = A.trace := Complex.ext rfl hn.2
    calc
      ‖A.trace‖ = ‖(A.trace.re : ℂ)‖ := congrArg norm hr.symm
      _ = A.trace.re := by rw [Complex.norm_real, Real.norm_of_nonneg hp.le]
  calc
    traceNorm (Quantum.Channels.mapTensorId Φ X A) =
        A.trace.re * traceNorm (Quantum.Channels.mapTensorId Φ X ρ.toOp) := by
      conv_lhs => rw [he, map_smul, traceNorm_smul, hnorm]
    _ ≤ A.trace.re * b := mul_le_mul_of_nonneg_left (hρ ρ) hp.le
    _ ≤ b := mul_le_of_le_one_left hb ht

/-- Channel distance is the supremum of output distances on input-sized joint density states. -/
theorem IsChannel.diamondDist_eq_sSup_traceDistance [Nonempty X]
    {Φ Ψ : Operation X Y} (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    diamondDist Φ Ψ = sSup (Set.range fun ρ : DensityOp (X × X) =>
      traceDistance (Quantum.Channels.mapTensorId Φ X ρ.toOp)
        (Quantum.Channels.mapTensorId Ψ X ρ.toOp)) := by
  classical
  let f (ρ : DensityOp (X × X)) :=
    (1 / 2 : ℝ) * traceNorm (Quantum.Channels.mapTensorId (Φ - Ψ) X ρ.toOp)
  have hbound (ρ : DensityOp (X × X)) : f ρ ≤ diamondDist Φ Ψ := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply traceNorm_mapTensorId_le_diamondNorm
    rw [traceNorm_of_posSemidef _ ρ.posSemidef, ρ.trace_one, Complex.one_re]
  have hbdd : BddAbove (Set.range f) := ⟨_, by rintro _ ⟨ρ, rfl⟩; exact hbound ρ⟩
  have hne : (Set.range f).Nonempty := ⟨_, Set.mem_range_self (DensityOp.maxMixed)⟩
  have hn : 0 ≤ sSup (Set.range f) := le_csSup_of_le hbdd
    (Set.mem_range_self (DensityOp.maxMixed))
    (mul_nonneg (by norm_num) (traceNorm_nonneg _))
  have h := diamondNorm_le_of_density_bound (Φ - Ψ) (hΦ.1.sub_conjTranspose hΨ.1)
    (2 * sSup (Set.range f)) (by positivity) (fun ρ => by
      have hh := le_csSup hbdd (Set.mem_range_self ρ)
      dsimp only [f] at hh
      linarith)
  have he : diamondDist Φ Ψ = sSup (Set.range f) := le_antisymm
    (by unfold diamondDist; linarith) (csSup_le hne (by rintro _ ⟨ρ, rfl⟩; exact hbound ρ))
  simpa only [f, traceDistance, mapTensorId_sub, LinearMap.sub_apply] using he

/-- An untouched reference does not increase the diamond norm of an adjoint-preserving map. -/
theorem diamondNorm_mapTensorId_le {R : Type*} [Fintype R] (Φ : Operation X Y)
    (hΦ : ∀ A, Φ Aᴴ = (Φ A)ᴴ) :
    diamondNorm (Quantum.Channels.mapTensorId Φ R) ≤ diamondNorm Φ := by
  apply diamondNorm_le_of_forall
  intro A hA
  rw [mapTensorId_assoc, traceNorm_reindex]
  apply traceNorm_mapTensorId_le_diamondNorm_of_map_conjTranspose Φ hΦ
  rwa [traceNorm_reindex]

end Quantum.Channels
