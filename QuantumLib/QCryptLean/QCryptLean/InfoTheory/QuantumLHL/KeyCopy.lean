import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.PartialTrace
import QCryptLean.Quantum.Operators.Basic

/-! # Visible classical key-copy postprocessing on natural registers -/

noncomputable section

namespace InfoTheory.QuantumLHL.KeyCopy

open Matrix Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy
open scoped Kronecker

variable {C K T E R : Type*}
  [Fintype C] [Fintype K] [Fintype T] [Fintype E] [Fintype R]
  [DecidableEq C] [DecidableEq K] [DecidableEq T]

/-- Put the discarded register first and the visible classical label before the reference. -/
def inputEquiv : ((E × R) × C) ≃ E × (C × R) where
  toFun p := (p.1.1, p.2, p.1.2)
  invFun p := ((p.1, p.2.2), p.2.1)

/-- Copy the key determined by a visible label, publish its transcript, discard Eve,
and retain the entire reference register. -/
def classicalMap (key : C → K) (transcript : C → T) :
    Operation ((E × R) × C) (((K × K) × T) × R) :=
  (mapTensorId (Quantum.Channels.classicalMap
    (fun c => ((key c, key c), transcript c))) R).comp
    ((Matrix.partialTraceLeftLinearMap (S := ℂ)).comp
      (Matrix.reindexLinearEquiv ℂ ℂ inputEquiv inputEquiv).toLinearMap)

/-- Visible-classical key copying is a channel, including empty reference registers. -/
theorem isChannel_classicalMap (key : C → K) (transcript : C → T) :
    IsChannel (classicalMap (E := E) (R := R) key transcript) :=
  (Quantum.Channels.isChannel_classicalMap _).mapTensorId.comp
    (isChannel_partialTraceLeft.comp (isChannel_reindex inputEquiv))

/-- A copied key and public transcript tensored with the retained reference block. -/
def outputBlock (t : T) (k : K) (A : Op R) : Op (((K × K) × T) × R) :=
  Matrix.single ((k, k), t) ((k, k), t) 1 ⊗ₖ A

omit [Fintype K] [Fintype T] in
/-- The key-copy map sums the visible CQ blocks after discarding Eve. -/
theorem classicalMap_toJointDensity_eq_sum_outputBlocks
    (key : C → K) (transcript : C → T) (ρ : CQState C (E × R)) :
    classicalMap key transcript ρ.toJointDensity.toOp =
      ∑ c, outputBlock (transcript c) (key c)
        (Matrix.partialTraceLeft (ρ.stateMap c).toOp) := by
  ext p q
  have h := congrArg (fun M : Op ((K × K) × T) => M p.1 q.1)
    (Quantum.Channels.classicalMap_apply (fun c => ((key c, key c), transcript c))
      (fun c d => ∑ e, ρ.toJointOp ((e, p.2), c) ((e, q.2), d)))
  refine h.trans ?_
  simp [CQState.toJointOp, outputBlock, Matrix.kroneckerMap_apply, Matrix.single_apply,
    Matrix.partialTraceLeft, Matrix.sum_apply, ite_and]


end InfoTheory.QuantumLHL.KeyCopy
