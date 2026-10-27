import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Announcement Bounds -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix
open scoped ComplexOrder

variable {S T Q : Type*} [Fintype S] [Fintype T] [Fintype Q]
  [DecidableEq S] [DecidableEq T] {s t q : ℕ}

omit [Fintype Q] in
/-- A graph projector is bounded by the identity, independently of graph collisions. -/
theorem opLe_seedGraphProj_one (g : S → T) : OpLe (seedGraphProj g) 1 := by
  apply opLe_of_posSemidef_sub
  rw [seedGraphProj_eq_diagonal, ← diagonal_one, diagonal_sub]
  apply PosSemidef.diagonal
  intro p
  change (0 : ℂ) ≤ 1 - (if p.2 = g p.1 then 1 else 0)
  split_ifs <;> simp

omit [Fintype Q] in
/-- Only the tag cardinality is charged for a public uniform seed. -/
theorem opLe_uniformSeededAnnounce_smul_maxMixed [Nonempty S] [Nonempty T]
    (g : S → T) :
    OpLe (uniformSeededAnnounce g).toOp
      ((Fintype.card T : ℂ) • (DensityOp.maxMixed (X := S × T)).toOp) := by
  have he : (Fintype.card T : ℂ) • (DensityOp.maxMixed (X := S × T)).toOp =
      (↑((Fintype.card S : ℝ)⁻¹) : ℂ) • (1 : Op (S × T)) := by
    change (Fintype.card T : ℂ) •
      (((Fintype.card (S × T) : ℝ)⁻¹ : ℂ) • (1 : Op (S × T))) = _
    rw [smul_smul]
    congr 1
    simp [Fintype.card_prod, Fintype.card_ne_zero]
  rw [he]
  apply opLe_of_posSemidef_sub
  change ((↑((Fintype.card S : ℝ)⁻¹) : ℂ) • 1 -
    (↑((Fintype.card S : ℝ)⁻¹) : ℂ) • seedGraphProj g).PosSemidef
  rw [← smul_sub]
  apply PosSemidef.smul _ (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))
  rw [seedGraphProj_eq_diagonal, ← diagonal_one, diagonal_sub]
  apply PosSemidef.diagonal
  intro p
  change (0 : ℂ) ≤ 1 - (if p.2 = g p.1 then 1 else 0)
  split_ifs <;> simp

end InfoTheory.SmoothMinEntropy
