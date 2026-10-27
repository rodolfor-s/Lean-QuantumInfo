import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Seeded announcements and block-diagonal references on natural registers -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped ComplexOrder

variable {S T Q : Type*} [Fintype S] [Fintype T] [Fintype Q]
  [DecidableEq S] [DecidableEq T]

/-- Project onto the graph of a seed-indexed announcement. -/
def seedGraphProj (g : S → T) : Op (S × T) :=
  ∑ s, Matrix.single (s, g s) (s, g s) 1

omit [Fintype T] in
/-- The graph projector is diagonal, with one supported value for each seed. -/
theorem seedGraphProj_eq_diagonal (g : S → T) :
    seedGraphProj g = Matrix.diagonal (fun p => if p.2 = g p.1 then 1 else 0) := by
  ext ⟨s, t⟩ ⟨u, v⟩
  simp [seedGraphProj, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply, Prod.ext_iff,
    ite_and, eq_comm]
  split_ifs <;> simp_all

omit [Fintype T] in
/-- Graph projectors are positive semidefinite. -/
theorem seedGraphProj_posSemidef (g : S → T) : (seedGraphProj g).PosSemidef := by
  rw [seedGraphProj_eq_diagonal, Matrix.posSemidef_diagonal_iff]
  intro p
  split_ifs <;> positivity

/-- The trace counts seeds, including the empty seed type. -/
theorem seedGraphProj_trace (g : S → T) : (seedGraphProj g).trace = Fintype.card S := by
  simp [seedGraphProj, Matrix.trace_sum]

/-- Uniform seed and its announcement, with the zero state for an empty seed register. -/
def uniformSeededAnnounce (g : S → T) : SubDensityOp (S × T) where
  toOp := (((Fintype.card S : ℝ)⁻¹ : ℝ) : ℂ) • seedGraphProj g
  posSemidef := (seedGraphProj_posSemidef g).smul
    (Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card S)), rfl⟩)
  trace_le_one := by
    simp only [Matrix.trace_smul, seedGraphProj_trace, smul_eq_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
    by_cases h : (Fintype.card S : ℝ) = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]

/-- A nonempty uniform seed gives a normalized announcement state. -/
theorem uniformSeededAnnounce_trace [Nonempty S] (g : S → T) :
    (uniformSeededAnnounce g).trace = 1 := by
  simp [SubDensityOp.trace, uniformSeededAnnounce, Matrix.trace_smul,
    seedGraphProj_trace, Fintype.card_ne_zero]

/-- A classical family with total mass at most one gives a reference with the classical
register first. This uses the existing complete CQ joint-state construction. -/
def blockDiagRef (ν : T → SubDensityOp Q) (hν : ∑ t, (ν t).trace ≤ 1) :
    SubDensityOp (T × Q) :=
  (CQState.toJointDensity ⟨ν, hν⟩).reindex (Equiv.prodComm Q T)

/-- The block-diagonal reference has exactly the supplied diagonal blocks. -/
theorem blockDiagRef_toOp (ν : T → SubDensityOp Q) (hν : ∑ t, (ν t).trace ≤ 1) :
    (blockDiagRef ν hν).toOp =
      (Matrix.blockDiagonal (fun t => (ν t).toOp)).submatrix Prod.swap Prod.swap := rfl

/-- The block reference retains the sum of the block masses. -/
theorem blockDiagRef_trace (ν : T → SubDensityOp Q) (hν : ∑ t, (ν t).trace ≤ 1) :
    (blockDiagRef ν hν).trace = ∑ t, (ν t).trace := by
  change (Matrix.reindex (Equiv.prodComm Q T) (Equiv.prodComm Q T)
    (CQState.toJointDensity ⟨ν, hν⟩).toOp).trace.re = _
  rw [Matrix.reindex_trace]
  exact CQState.toJointDensity_trace ⟨ν, hν⟩

end InfoTheory.SmoothMinEntropy
