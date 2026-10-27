import QCryptLean.InfoTheory.QuantumLHL.KeyCopy
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic

/-! # Key Copy Algebra -/


noncomputable section

namespace InfoTheory.QuantumLHL.KeyCopy

open Quantum.Operators Quantum.Channels Matrix
open scoped Kronecker

variable {C K T E R : Type*} [Fintype C] [Fintype K] [Fintype T]
  [Fintype E] [Fintype R] [DecidableEq C] [DecidableEq K] [DecidableEq T]

omit [Fintype K] [Fintype T] [Fintype R] in
/-- Key copying acts on every complex operator by summing its retained reference blocks. -/
theorem classicalMap_apply (key : C → K) (transcript : C → T) (A : Op ((E × R) × C)) :
    classicalMap key transcript A = ∑ c, outputBlock (transcript c) (key c)
      (fun r r' => ∑ e, A ((e,r),c) ((e,r'),c)) := by
  ext p q
  have h := congrArg (fun M : Op ((K × K) × T) => M p.1 q.1)
    (Quantum.Channels.classicalMap_apply
      (fun c => ((key c,key c),transcript c))
      (fun c d => ∑ e, A ((e,p.2),c) ((e,q.2),d)))
  refine h.trans ?_
  simp [outputBlock, Matrix.kroneckerMap, Matrix.of_apply, Matrix.single_apply, Matrix.sum_apply,
    ite_and]

end InfoTheory.QuantumLHL.KeyCopy
