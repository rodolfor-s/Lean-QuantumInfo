import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Single-round signal measurement with an arbitrary retained register

Conditioning the joint signal pair on its computational outcome extracts the
corresponding principal block. The complete pair is classical here; Alice's key
bit is a subsequent classical coarsening.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators InfoTheory.SmoothMinEntropy Measurement Matrix

variable (E : Type*) [Fintype E]

/-- Eve's subnormalized block for a computational-basis outcome of the signal pair. -/
def singleRoundConditioned (Ψ : DensityOp (Signal × E)) (x : Signal) : SubDensityOp E :=
  Ψ.toSubDensityOp.submatrix (fun a => (x, a)) (fun _ _ h => congrArg Prod.snd h)

/-- The weight of a conditioned outcome is its diagonal block trace. -/
theorem singleRoundConditioned_trace (Ψ : DensityOp (Signal × E)) (x : Signal) :
    (singleRoundConditioned E Ψ x).trace = ∑ a, (Ψ.toOp (x, a) (x, a)).re := by
  simp only [singleRoundConditioned, SubDensityOp.trace, SubDensityOp.submatrix,
    DensityOp.toSubDensityOp, Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Complex.re_sum]

/-- Conditioning on every signal-pair outcome exhausts the state's total weight. -/
theorem singleRoundConditioned_weight_sum (Ψ : DensityOp (Signal × E)) :
    ∑ x, (singleRoundConditioned E Ψ x).trace = 1 := by
  simp_rw [singleRoundConditioned_trace]
  simpa only [trace, diag, Complex.re_sum, Fintype.sum_prod_type, Complex.one_re]
    using congrArg Complex.re Ψ.trace_one

/-- The signal outcome paired with its conditional retained quantum state. -/
def singleRoundCQState (Ψ : DensityOp (Signal × E)) : CQState Signal E where
  stateMap := singleRoundConditioned E Ψ
  weight_le_one := (singleRoundConditioned_weight_sum E Ψ).le

/-- Every CQ block keeps exactly the corresponding retained-register matrix entries. -/
theorem singleRoundCQState_stateMap_toOp_apply (Ψ : DensityOp (Signal × E))
    (x : Signal) (a b : E) :
    ((singleRoundCQState E Ψ).stateMap x).toOp a b = Ψ.toOp (x, a) (x, b) := rfl

end QKD.BB84.FiniteKey
