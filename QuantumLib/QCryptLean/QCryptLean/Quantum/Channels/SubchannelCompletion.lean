import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Extension
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Completing a trace-nonincreasing operation with an abort outcome

The finite Kraus deficit is positive in matrix star order. An explicit abort
register completes the operation to a channel; no matrix norm is selected.
-/

noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

open Classical in
/-- A Kraus map is trace-nonincreasing exactly when its completeness sum is at most one. -/
theorem trace_krausMap_le_iff (K : I → Matrix Y X ℂ) :
    (∀ A : Op X, A.PosSemidef → (krausMap K A).trace.re ≤ A.trace.re) ↔
      ∑ i, (K i)ᴴ * K i ≤ 1 := by
  classical
  let S : Op X := ∑ i, (K i)ᴴ * K i
  have hS : S.PosSemidef := posSemidef_sum _ fun i _ => posSemidef_conjTranspose_mul_self _
  rw [Matrix.le_iff]
  constructor
  · intro ht
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_one.sub hS.isHermitian)
    intro v
    have hh := ht (vecMulVec v (star v)) (posSemidef_vecMulVec_self_star v)
    rw [trace_krausMap, mul_vecMulVec, trace_vecMulVec, trace_vecMulVec] at hh
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re]
      simpa only [dotProduct_comm] using sub_nonneg.mpr hh
    · have he := (isHermitian_one.sub hS.isHermitian).star_dotProduct_mulVec_comm v v
      have him := congrArg Complex.im he
      change -(star v ⬝ᵥ (1 - S) *ᵥ v).im = (star v ⬝ᵥ (1 - S) *ᵥ v).im at him
      linarith
  · intro ht A hA
    have he := Complex.nonneg_iff.mp (ht.trace_mul_nonneg hA)
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at he
    rw [trace_krausMap]
    exact sub_nonneg.mp he.1

/-- A trace-nonincreasing completely positive operation extends to a channel on abort registers. -/
theorem IsCompletelyPositive.exists_channel_extend {Φ : Operation X Y}
    (hΦ : IsCompletelyPositive Φ)
    (ht : ∀ A : Op X, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re) :
    ∃ Ψ : Operation (X ⊕ Unit) (Y ⊕ Unit), IsChannel Ψ ∧
      ∀ (ρ : SubDensityOp X) (σ : SubDensityOp Y), σ.toOp = Φ ρ.toOp →
        Ψ ρ.extendOp = σ.extendOp := by
  classical
  obtain ⟨K, rfl⟩ := hΦ.exists_kraus
  let S : Op X := ∑ i, (K i)ᴴ * K i
  have hd : (1 - S).PosSemidef := Matrix.le_iff.mp ((trace_krausMap_le_iff K).mp ht)
  let D := CFC.sqrt (1 - S)
  have hD : Dᴴ * D = 1 - S := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - S))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ hd.nonneg
  let L : (X × Y) ⊕ X ⊕ Unit → Matrix (Y ⊕ Unit) (X ⊕ Unit) ℂ :=
    Sum.elim (fun i => fromBlocks (K i) 0 0 0)
      (Sum.elim (fun x => fromBlocks 0 0 (fun (_ : Unit) j => D x j) 0)
        (fun _ => fromBlocks 0 0 0 1))
  have hL : ∑ i, (L i)ᴴ * L i = 1 := by
    ext (i | i) (j | j)
    · have he := congrFun (congrFun hD i) j
      simp only [Matrix.mul_apply, conjTranspose_apply] at he
      simp only [Matrix.sum_apply]
      suffices (∑ a, ∑ x, star (K a x i) * K a x j) +
          (∑ x, star (D x i) * D x j) = if i = j then 1 else 0 by
        simpa [L, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks,
          conjTranspose_apply, Matrix.one_apply] using this
      rw [he]
      simp only [S, Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply,
        conjTranspose_apply, Matrix.one_apply]
      ring
    · simp [L, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        fromBlocks, conjTranspose_apply]
    · simp [L, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        fromBlocks, conjTranspose_apply]
    · simp [L, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        fromBlocks, conjTranspose_apply]
  have htp : IsTracePreserving (krausMap L) := by
    apply (isTracePreserving_krausMap_iff L).mpr
    convert hL using 1
    ext i j
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  refine ⟨krausMap L, ⟨isCompletelyPositive_krausMap L, htp⟩, ?_⟩
  intro ρ σ hσ
  have htrace : (krausMap L ρ.extendOp).trace = 1 :=
    (htp ρ.extendOp).trans ρ.trace_extendOp
  have hlive (i j : Y) : krausMap L ρ.extendOp (Sum.inl i) (Sum.inl j) = σ.toOp i j := by
    rw [hσ]
    change (∑ a, L a * ρ.extendOp * (L a)ᴴ) (Sum.inl i) (Sum.inl j) = _
    change _ = (∑ a, K a * ρ.toOp * (K a)ᴴ) i j
    simp [L, SubDensityOp.extendOp, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, fromBlocks, conjTranspose_apply]
  have hcross (i : Y) (j : Unit) :
      krausMap L ρ.extendOp (Sum.inl i) (Sum.inr j) = 0 := by
    change (∑ a, L a * ρ.extendOp * (L a)ᴴ) (Sum.inl i) (Sum.inr j) = 0
    simp [L, SubDensityOp.extendOp, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.sum_apply, fromBlocks, conjTranspose_apply]
  have hcross' (i : Unit) (j : Y) :
      krausMap L ρ.extendOp (Sum.inr i) (Sum.inl j) = 0 := by
    have hh := (posSemidef_krausMap L ρ.posSemidef_extendOp).isHermitian.apply
      (Sum.inl j) (Sum.inr i)
    have hz := congrArg star hh
    simpa only [hcross, star_zero, star_star] using hz
  ext (i | i) (j | j)
  · exact hlive i j
  · exact hcross i j
  · exact hcross' i j
  · cases i; cases j
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, hlive,
      Fintype.sum_unique] at htrace
    change _ = (σ.defect : ℂ) * 1
    rw [mul_one]
    have hs : (σ.trace : ℂ) = σ.toOp.trace := by
      apply Complex.ext
      · rfl
      · exact σ.trace_im.symm
    rw [SubDensityOp.defect, Complex.ofReal_sub, Complex.ofReal_one, hs]
    change σ.toOp.trace + _ = 1 at htrace
    linear_combination htrace

end Quantum.Channels
