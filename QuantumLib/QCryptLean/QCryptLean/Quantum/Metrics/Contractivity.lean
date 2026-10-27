import QCryptLean.Quantum.Channels.Adjoint
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.LeftAmplification
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-!
# Native trace-norm contraction for quantum subchannels

Positive trace contraction on Hermitian inputs is extended to arbitrary inputs
by a Boolean self-adjoint dilation. Both the channel and subchannel cases use
this one proof. No matrix norm instance is selected.
-/

noncomputable section
namespace Quantum.Metrics
open Matrix Quantum.Operators Quantum.Channels
open scoped ComplexOrder
variable {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]

/-- Trace nonincrease on positive inputs persists under a left finite reference. -/
theorem trace_mapIdTensor_le (Φ : Operation X Y)
    (htr : ∀ A, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (A : Op (R × X)) (hA : A.PosSemidef) :
    (mapIdTensor R Φ A).trace.re ≤ A.trace.re := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro r _
  change (∑ i, (Φ (fun x y => A (r, x) (r, y)) i i).re) ≤
    ∑ i, (A (r, i) (r, i)).re
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum] using
    htr (fun i j => A (r, i) (r, j)) (hA.submatrix (fun i => (r, i)))

/-- Completely positive trace-nonincreasing maps contract trace norm on all operators. -/
theorem traceNorm_apply_le_of_isCompletelyPositive_of_trace_le
    (Φ : Operation X Y) (h : IsCompletelyPositive Φ)
    (htr : ∀ A, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re) (A : Op X) :
    traceNorm (Φ A) ≤ traceNorm A := by
  classical
  let D (B : Op X) : Op (Bool × X) :=
    reindex (Equiv.boolProdEquivSum X).symm (Equiv.boolProdEquivSum X).symm
      (fromBlocks 0 B Bᴴ 0)
  let D' (B : Op Y) : Op (Bool × Y) :=
    reindex (Equiv.boolProdEquivSum Y).symm (Equiv.boolProdEquivSum Y).symm
      (fromBlocks 0 B Bᴴ 0)
  have hn (B : Op X) : traceNorm (D B) = 2 * traceNorm B := by
    dsimp only [D]
    rw [traceNorm_reindex, traceNorm_fromBlocks_dilation]
  have hn' (B : Op Y) : traceNorm (D' B) = 2 * traceNorm B := by
    dsimp only [D']
    rw [traceNorm_reindex, traceNorm_fromBlocks_dilation]
  have hD : (D A).IsHermitian := by
    apply IsHermitian.reindex
    simp [Matrix.IsHermitian, fromBlocks_conjTranspose]
  have he : mapIdTensor Bool Φ (D A) = D' (Φ A) := by
    ext ⟨b, i⟩ ⟨c, j⟩
    change Φ (fun x y => D A (b, x) (c, y)) i j = D' (Φ A) (b, i) (c, j)
    cases b <;> cases c <;>
      simp only [D, D', reindex_apply, submatrix_apply, Equiv.boolProdEquivSum, fromBlocks]
    all_goals first
      | exact congrFun (congrFun (map_zero Φ) i) j
      | exact congrFun (congrFun (h.conjTranspose_apply A) i) j
      | rfl
  have hb := traceNorm_apply_le_of_isHermitian (mapIdTensor Bool Φ)
    (fun B hB => h.mapIdTensor.posSemidef hB) (trace_mapIdTensor_le Φ htr) (D A) hD
  rw [he, hn', hn] at hb
  linarith

/-- Channels contract generalized trace distance on arbitrary operators. -/
theorem traceDistanceGen_apply_le (Φ : Operation X Y) (hΦ : IsChannel Φ) (A B : Op X) :
    traceDistanceGen (Φ A) (Φ B) ≤ traceDistanceGen A B := by
  unfold traceDistanceGen traceDistance
  rw [hΦ.2 A, hΦ.2 B, ← map_sub]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact traceNorm_apply_le_of_isCompletelyPositive_of_trace_le Φ hΦ.1
    (fun C _ => le_of_eq (congrArg Complex.re (hΦ.2 C))) _

end Quantum.Metrics
