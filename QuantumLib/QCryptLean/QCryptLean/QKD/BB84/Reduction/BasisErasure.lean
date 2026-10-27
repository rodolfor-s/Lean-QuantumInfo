import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-!
# Basis erasure as a map of diagonals

The actual private `forgetAliceBases` and `forgetBobBases` actions sum the selected-record diagonal
mass over the discarded basis strings. Their natural successor registers are the two raw strings
consumed by `classicalTail`.
-/

open Quantum.Operators (Op)

open scoped BigOperators
noncomputable section
namespace QKD.BB84.Reduction
open LOCC LOCC.TwoParty Measurement

/-- Forgetting both private basis strings sends selected-record mass to its raw bit strings. -/
theorem forgetAliceBases_forgetBobBases_denote_diag (N n : ℕ)
    (sigma : Op (system (SelectedLocalRecord N n) (SelectedLocalRecord N n)).total)
    (x : (system (Bits n) (Bits n)).total) :
    (forgetBobBases N n).successorOperation ()
      ((forgetAliceBases N n).successorOperation () sigma) x x =
      ∑ qB : SelectedLocalRecord N n, ∑ qA : SelectedLocalRecord N n,
        if x .alice = qA.2 ∧ x .bob = qB.2 then
          sigma ((pairEquiv _ _).symm (qA, qB)) ((pairEquiv _ _).symm (qA, qB))
        else 0 := by
  have hx := (pairEquiv (Bits n) (Bits n)).symm_apply_apply x
  refine (congrArg₂ ((forgetBobBases N n).successorOperation ()
    ((forgetAliceBases N n).successorOperation () sigma)) hx.symm hx.symm).trans ?_
  refine (functionAndForget_pair_operation_apply (fun q : SelectedLocalRecord N n => q.2)
    (fun q : SelectedLocalRecord N n => q.2) sigma (x .alice) (x .alice) (x .bob) (x .bob)).trans ?_
  simp only [and_self]
  apply Finset.sum_congr rfl
  intro qB _
  by_cases hb : x .bob = qB.2
  · simp only [hb, ite_true, and_true]
  · simp only [hb, ite_false, and_false, Finset.sum_const_zero]

end QKD.BB84.Reduction
