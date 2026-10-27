import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # BB84Locality -/


open Equiv

open Quantum.Operators Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open QKD.BB84.FiniteKey
open scoped Kronecker Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model


/-- **The per-round sift splits across the cut of a single round.** On an X-test round it is
`H ⊗ H`; elsewhere it is `1 ⊗ 1`. Not `rfl`: the identity branch is spelled `(1 : Op Signal)`, and
`one_kronecker_one` is what identifies it with `1 ⊗ₖ 1`. -/
theorem xTestPairOp_eq_tensor (peSel xSel : Bool) :
    xTestPairOp peSel xSel
      = (if peSel && xSel then reindex finTwoEquiv.symm finTwoEquiv.symm
          Quantum.Gates.hadamard else (1 : Op Bit)) ⊗ₖ
        (if peSel && xSel then reindex finTwoEquiv.symm finTwoEquiv.symm
          Quantum.Gates.hadamard else (1 : Op Bit)) := by
  unfold xTestPairOp
  by_cases h : (peSel && xSel) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · simp only [ite_eq_right h, one_kronecker_one]


/-- **(a), operator level.** Transported along the round regrouping, the V2 sift
`siftedRotation` is the tensor product of two single-party `n`-qubit operators: Hadamard exactly
on the X-test rounds and the identity elsewhere, **on each side separately**.

Arbitrary `peSel`, `xSel` — a product factorization of an operator cannot depend on how many rounds
are key rounds, so there is no `KeyCount` hypothesis and none would help.

This is the theorem the `xTestPairOp` and `siftedRotation` docstrings assert.

**Scope limit.** Both factors are the *same* term, so this statement is blind to the A|B
orientation: the swapped right-hand side is literally this one. The orientation is fixed instead by
`Matrix.reindex_piTensorProduct_kronecker`, which this proof consumes,
and which is
false when swapped. -/
theorem siftedRotation_reindex_roundGroupEquiv (n : ℕ) (peSel xSel : Fin n → Bool) :
    Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n)
        (siftedRotation n peSel xSel)
      = ((piTensorProduct
            (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit))) ⊗ₖ (piTensorProduct
            (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit)))) := by
  rw [siftedRotation]
  simp only [xTestPairOp_eq_tensor]
  exact reindex_piTensorProduct_kronecker _ _

/-- **(a), map level — the consumer-facing form.** Transported along the round regrouping,
conjugation by the V2 sift is conjugation by a **product** unitary: Alice applies `⊗ₐ Hᵃ` to her own
`n` qubits, Bob applies the same to his, and nothing crosses the cut. -/
theorem siftedRotation_conj_reindex_roundGroupEquiv (n : ℕ) (peSel xSel : Fin n → Bool)
    (ρ : Op (Signals n)) :
    Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n)
        (siftedRotation n peSel xSel * ρ * (siftedRotation n peSel xSel)ᴴ)
      = ((piTensorProduct
              (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit))) ⊗ₖ (piTensorProduct
              (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit)))) *
          Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n) ρ *
          (((piTensorProduct
              (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit))) ⊗ₖ (piTensorProduct
              (fun a => if peSel a && xSel a then
                reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
              else (1 : Op Bit)))))ᴴ := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_mul, map_mul,
    Matrix.coe_reindexAlgEquiv,
    siftedRotation_reindex_roundGroupEquiv, ← Matrix.conjTranspose_reindex,
    siftedRotation_reindex_roundGroupEquiv]


/-- **(b), map level — the consumer-facing form.** Transported along the round regrouping,
`permuteSignalLinear n π` is conjugation by the product unitary `U^A_π ⊗ U^B_π`: each party permutes
its **own** `n` subsystems by the same `π`, and no data crosses the cut.

**Scope limit.** This proves that *for each fixed `π`* the layer is a product across the cut.
It does **not** say `π` is *public*, so both parties can apply it — that is a statement about the
surrounding channel's announcement register and is proved nowhere. Each factor's unitarity is
free. -/
theorem permuteSignalLinear_reindex_roundGroupEquiv (n : ℕ)
    (π : Equiv.Perm (Fin n)) (ρ : Op (Signals n)) :
    Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n)
        (permConjLin π ρ)
      = (permutationRepresentation (X := Bit) π ⊗ₖ permutationRepresentation (X := Bit) π) *
          Matrix.reindex (pairFunctions Bit Bit n) (pairFunctions Bit Bit n) ρ *
          (permutationRepresentation (X := Bit) π ⊗ₖ
            permutationRepresentation (X := Bit) π)ᴴ := by
  simp only [permConjLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_mul, map_mul,
    Matrix.coe_reindexAlgEquiv,
    reindex_permutationRepresentation_pair, ← Matrix.conjTranspose_reindex,
    reindex_permutationRepresentation_pair]

end QKD.BB84.Model

end
