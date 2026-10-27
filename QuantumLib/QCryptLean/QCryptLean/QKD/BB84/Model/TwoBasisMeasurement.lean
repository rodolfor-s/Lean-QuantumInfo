import QCryptLean.Math.Analysis.ComplexSqrtTwo
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BellCovariance
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellBasis
import QCryptLean.Quantum.Symmetry.BellMixture

/-!
# The Hadamard basis rotation and phase observability

The `H ⊗ H` two-qubit basis-rotation unitary that turns the computational (`Z`) basis into the
Hadamard (`X`) basis on the Alice–Bob pair, and the resulting **phase observability** identity:
the bit-flip rate of a component read in the `X` basis equals its phase-flip rate read in the `Z`
basis. In the `Z`-only model every diagonal `σ` has phase rate identically `½`
(`phaseFlipProjector` is non-diagonal), so the joint condition `goodRateSet`
(`bit ≤ Q+δ ∧ phase ≤ Q+δ`) is unsatisfiable for a diagonal post-measurement state; the `X`-basis
measurement recovers it.

## The enabling identity

With `hadamardPair := H ⊗ H` (Hermitian, unitary):
`hadamardPair · bitFlipProjector · hadamardPair = phaseFlipProjector`
(`hadamardPair_conj_bitFlipProjector`).  Hence for
`σ_X := xBasisConjugate σ = H⊗H · σ · H⊗H`,
`bitFlipErrorRate σ_X = phaseFlipErrorRate σ`
(`xBasisConjugate_bitRate_eq_phaseRate`).

## Faithfulness notes (Renner §6.5)

* **Two bases only (Z, X).**  Renner §6.5 as written is the six-state protocol
  (x, y, z); BB84 drops the circular/`Y` basis.
* **The X-POVM is fixed to `H ⊗ H`,** never an arbitrary unitary: only `H ⊗ H`
  makes the `X`-mismatch projector equal `phaseFlipProjector` exactly.

## Main definitions and results

* `hadamardPair` — the `H ⊗ H` basis-rotation unitary on `Op signalDim`.
* `hadamardPair_conj_bitFlipProjector` — the Hadamard pair
  exchanges the bit-flip and phase-flip projectors.
* `xBasisConjugate` — the X-basis conjugate component `H⊗H · σ · H⊗H`.
* `xBasisConjugate_bitRate_eq_phaseRate` — phase observability: the X-basis bit
  rate of `σ` equals its phase rate.

## References

Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 / `lem:PEsec`
(`main.tex:7527`, `main.tex:9131–9180`).
-/

open Quantum.Operators Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open scoped Kronecker BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-- The local Hadamard basis change on Alice's and Bob's bit registers. -/
def hadamardPair : Op Signal :=
  reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard ⊗ₖ
    reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard

/-- The two local Hadamards are Hermitian. -/
theorem conjTranspose_hadamardPair : hadamardPairᴴ = hadamardPair := by
  simp only [hadamardPair, conjTranspose_kronecker, reindex_apply,
    conjTranspose_submatrix, Quantum.Gates.isHermitian_hadamard.eq]

/-- Applying both local Hadamards twice restores the input. -/
theorem hadamardPair_mul_self : hadamardPair * hadamardPair = (1 : Op Signal) := by
  simp only [hadamardPair, ← mul_kronecker_mul, reindex_apply, submatrix_mul_equiv,
    Quantum.Gates.hadamard_sq, submatrix_one_equiv, one_kronecker_one]

/-- Each Hadamard-pair entry is the product of its two local signs, divided by two. -/
lemma hadamardPair_eq_matrix :
    hadamardPair = fun i j : Signal =>
      (1 / 2 : ℂ) * (if i.1 = 1 ∧ j.1 = 1 then -1 else 1) *
        (if i.2 = 1 ∧ j.2 = 1 then -1 else 1) := by
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 :=
    Complex.inv_sqrt_two_mul_self
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [hadamardPair, Quantum.Gates.hadamard, reindex_apply,
      submatrix_apply, kroneckerMap_apply, finTwoEquiv] <;> simp [hs]

/-- The bit-error projector selects precisely the two unequal classical bit pairs. -/
lemma bitFlipProjector_eq_matrix :
    bitFlipProjector = fun i j : Signal =>
      if i = j ∧ i.1 ≠ i.2 then (1 : ℂ) else 0 := by
  have hs := Complex.inv_sqrt_two_mul_self
  ext ⟨i, j⟩ ⟨k, l⟩
  change (bellLabelKet 1).vec (finTwoEquiv i, finTwoEquiv j) *
      star ((bellLabelKet 1).vec (finTwoEquiv k, finTwoEquiv l)) +
    (bellLabelKet 3).vec (finTwoEquiv i, finTwoEquiv j) *
      star ((bellLabelKet 3).vec (finTwoEquiv k, finTwoEquiv l)) = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bellLabelKet, bellKet, finTwoEquiv] <;> linear_combination 2 * hs

/-- Local X-basis measurements exchange the bit-error and phase-error observables. -/
theorem hadamardPair_conj_bitFlipProjector :
    hadamardPair * bitFlipProjector * hadamardPair = phaseFlipProjector := by
  have hb (p b : Fin 2) := Quantum.Gates.hadamard_kronecker_mul_bellKet p b
  have hproj (p b : Fin 2) :
      hadamardPair *
        ((bellLabelKet (finProdFinEquiv (p, b))).reindex
          (qubitEquiv.prodCongr qubitEquiv)).projector * hadamardPair =
        ((bellLabelKet (finProdFinEquiv (b, p))).reindex
          (qubitEquiv.prodCongr qubitEquiv)).projector := by
    calc
      _ = (hadamardPair * ((bellLabelKet (finProdFinEquiv (p, b))).reindex
          (qubitEquiv.prodCongr qubitEquiv))).projector := by
        rw [Ket.projector_mul, conjTranspose_hadamardPair]
      _ = _ := by
        have hb' := hb p b
        change hadamardPair * (_ : Ket Signal) = (_ : Ket Signal) at hb'
        rw [hb']
        change ((if p = 1 ∧ b = 1 then (-1 : ℂ) else 1) •
          ((bellLabelKet (finProdFinEquiv (b, p))).reindex
            (qubitEquiv.prodCongr qubitEquiv))).projector = _
        split_ifs <;> ext i j <;>
          change ((_ : ℂ) * _) * star ((_ : ℂ) * _) = (_ : ℂ) * star _ <;> simp
  change hadamardPair *
    (((bellLabelKet 1).reindex (qubitEquiv.prodCongr qubitEquiv)).projector +
      ((bellLabelKet 3).reindex (qubitEquiv.prodCongr qubitEquiv)).projector) *
      hadamardPair = _
  have h01 := hproj 0 1
  have h11 := hproj 1 1
  norm_num [finProdFinEquiv] at h01 h11
  rw [mul_add, add_mul, h01, h11]
  rfl

/-- The density operator obtained by measuring both qubits in the X frame. -/
def xBasisConjugate (σ : DensityOp Signal) : DensityOp Signal where
  toOp := hadamardPair * σ.toOp * hadamardPair
  posSemidef := by
    simpa only [conjTranspose_hadamardPair] using
      σ.posSemidef.mul_mul_conjTranspose_same hadamardPair
  trace_one := by
    rw [trace_mul_cycle, hadamardPair_mul_self, one_mul, σ.trace_one]

/-- The X-frame density has the expected conjugation formula. -/
@[simp]
theorem xBasisConjugate_toOp (σ : DensityOp Signal) :
    (xBasisConjugate σ).toOp = hadamardPair * σ.toOp * hadamardPair := rfl

/-- Conjugation by the fixed local basis change is continuous. -/
theorem continuous_xBasisConjugate : Continuous xBasisConjugate := by
  apply continuous_induced_rng.mpr
  exact (continuous_const.matrix_mul DensityOp.continuous_toOp).matrix_mul continuous_const

/-- The bit-error probability in the X frame equals the original phase-error probability. -/
theorem xBasisConjugate_bitRate_eq_phaseRate (σ : DensityOp Signal) :
    bitFlipErrorRate (xBasisConjugate σ) = phaseFlipErrorRate σ := by
  unfold bitFlipErrorRate phaseFlipErrorRate
  rw [xBasisConjugate_toOp]
  congr 1
  calc
    (bitFlipProjector * (hadamardPair * σ.toOp * hadamardPair)).trace =
        (hadamardPair * bitFlipProjector * hadamardPair * σ.toOp).trace := by
      rw [← mul_assoc, trace_mul_comm]
      simp only [mul_assoc]
    _ = _ := by rw [hadamardPair_conj_bitFlipProjector]

end QKD.BB84.Model
