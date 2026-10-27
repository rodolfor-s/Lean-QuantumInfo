import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Quantum.Operators.Basic

/-! # Computational Measurement -/


open scoped Matrix BigOperators
open Quantum.Operators

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

namespace Instrument

/-- Computational-basis measurement that retains the measured register.

Its outcome-`a` Kraus operator is the projector onto the basis vector `a`, giving a local
instrument as in Chitambar et al., arXiv:1210.4583, Section II. -/
def computationalMeasurement (A : Type) [Fintype A] [DecidableEq A] :
    Instrument A A A :=
  Instrument.nondemolitionReadout id

end Instrument

namespace PrivateAction

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Apply `Instrument.computationalMeasurement` privately to party `i`, retaining every register
type and exposing no measurement outcome to public control flow. -/
def computationalMeasurement
    (R : MultipartiteSystem P) (i : P) :
    PrivateAction R :=
  PrivateAction.ofInstrument i
    (Instrument.computationalMeasurement (R.reg i))

/-- A computational measurement retains the input multipartite system. -/
@[simp] theorem computationalMeasurement_out
    (R : MultipartiteSystem P) (i : P) :
    (computationalMeasurement R i).out = R :=
  R.set_self i

/-- Exact branch operation of a private computational measurement, in the input coordinates.

The output coordinate is obtained by the canonical splitting of the computed output system.
Only the actor's row and column coordinates must equal the observed value. -/
theorem computationalMeasurement_liftedOperation_apply
    (R : MultipartiteSystem P) (i : P)
    (o : R.reg i) (rho : Quantum.Operators.Op R.total) (q q' : R.total) :
    ((computationalMeasurement R i).liftedOperation o rho)
        ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q))
        ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q')) =
      if ((R.splitAt i) q).1 = o ∧ ((R.splitAt i) q').1 = o then rho q q' else 0 := by
  change (((Instrument.computationalMeasurement (R.reg i)).liftAt R i).operation o rho)
      ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q))
      ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q')) = _
  rw [Instrument.liftAt_operation_apply (R := R) i
    (Instrument.computationalMeasurement (R.reg i)) o rho]
  simp only [Equiv.apply_symm_apply, Instrument.computationalMeasurement,
    Instrument.nondemolitionReadout_operation_apply, id_eq, Matrix.submatrix_apply,
    Prod.eta, Equiv.symm_apply_apply]

/-- The private computational-measurement channel dephases only the acting party's coordinate.

The acting-party row and column must agree, while distinct spectator row and column coordinates
are retained. This is an arbitrary-operator tensor-with-identity statement for the local
measurement node of Chitambar et al., arXiv:1210.4583, Section II. -/
theorem computationalMeasurement_liftedChannel_apply
    (R : MultipartiteSystem P) (i : P)
    (rho : Quantum.Operators.Op R.total) (q q' : R.total) :
    ((∑ o : R.reg i,
        (computationalMeasurement R i).liftedOperation o) rho)
        ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q))
        ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q')) =
      if ((R.splitAt i) q).1 = ((R.splitAt i) q').1 then rho q q' else 0 := by
  classical
  let L : R.reg i → Quantum.Operators.Op R.total →ₗ[ℂ] Quantum.Operators.Op
    (computationalMeasurement R
    i).out.total :=
    fun o => (computationalMeasurement R i).liftedOperation o
  change (∑ o, L o) rho ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q))
    ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q')) = _
  rw [LinearMap.sum_apply]
  refine (Matrix.sum_apply _ _ Finset.univ (fun o => L o rho)).trans ?_
  have hL (o : R.reg i) : L o rho
      ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q))
      ((R.splitAtSet i (R.reg i)).symm (R.splitAt i q')) =
      if ((R.splitAt i) q).1 = o ∧ ((R.splitAt i) q').1 = o then rho q q' else 0 :=
    computationalMeasurement_liftedOperation_apply R i o rho q q'
  refine (Finset.sum_congr rfl (fun o _ => hL o)).trans ?_
  by_cases h : ((R.splitAt i) q).1 = ((R.splitAt i) q').1
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro o _
    rw [ite_eq_right]
    intro ho
    exact h (ho.1.trans ho.2.symm)

end PrivateAction

end LOCC
