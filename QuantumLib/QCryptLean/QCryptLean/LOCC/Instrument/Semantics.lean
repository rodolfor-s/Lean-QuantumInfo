import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Semantics -/


open scoped Matrix BigOperators Kronecker
open Matrix

namespace LOCC
open Quantum.Operators (Op)
open Quantum.Channels

section

variable {A B HH Outcome : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype HH] [DecidableEq HH] [Fintype Outcome]

/-- **The completely positive operation at one observed outcome.** Its internal Kraus fibre is
summed out here and is never returned as classical data. -/
noncomputable def Instrument.operation
    (J : Instrument A B Outcome) (o : Outcome) :
    Op A →ₗ[ℂ] Op B :=
  krausMap (J.kraus o)

/-- Keeping an instrument outcome stores that outcome in the second output factor and has no
matrix entries in any other outcome block. This is the operation-level form of the observed
classical record in the instrument-tree model of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
@[simp] theorem Instrument.keeping_operation_apply
    [DecidableEq Outcome]
    (I : Instrument A HH Outcome) (o : Outcome) (rho : Op A)
    (h h' : HH) (y z : Outcome) :
    ((I.keeping.operation o) rho) (h, y) (h', z) =
      if y = o ∧ z = o then (I.operation o rho) h h' else 0 := by
  simp only [Instrument.operation, krausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Instrument.keeping, Matrix.sum_apply]
  by_cases hy : y = o
  · subst y
    by_cases hz : z = o
    · subst z
      rw [ite_eq_left ⟨rfl, rfl⟩]
      apply Finset.sum_congr rfl
      intro r _
      simp [Matrix.mul_apply]
    · simp [hz, Matrix.mul_apply]
  · simp [hy, Matrix.mul_apply]

/-- **The channel a certified instrument denotes.** First sum the internal Kraus fibre of each
observed outcome, then sum the observed operations. `Instrument.complete` certifies trace
preservation of this total map. -/
noncomputable def Instrument.channel
    (J : Instrument A B Outcome) : Op A →ₗ[ℂ] Op B :=
  krausMap J.flatKraus

/-- Summing the observed operations gives the complete instrument channel. -/
theorem Instrument.channel_eq_sum
    (I : Instrument A B Outcome) : I.channel = ∑ o, I.operation o := by
  simp only [Instrument.channel, Instrument.operation, krausMap_eq_sum_conjLinearMap,
    Fintype.sum_sigma, Instrument.flatKraus]

/-- Every observed instrument operation is completely positive. -/
theorem Instrument.isCompletelyPositive_operation
    (I : Instrument A B Outcome) (o : Outcome) : IsCompletelyPositive (I.operation o) :=
  isCompletelyPositive_krausMap _

/-- Kraus completeness directly certifies an instrument as a channel. -/
theorem Instrument.isChannel_channel
    (I : Instrument A B Outcome) : IsChannel I.channel := by
  refine ⟨isCompletelyPositive_krausMap _, (isTracePreserving_krausMap_iff _).mpr ?_⟩
  ext a b
  have h := congrFun (congrFun I.complete a) b
  by_cases hab : a = b <;>
    simpa only [Fintype.sum_sigma, Instrument.flatKraus, Matrix.sum_apply,
      Matrix.one_apply, ite_eq_left, ite_eq_right, hab] using h

namespace Instrument

/-- Entrywise operation of an instrument lifted at one party.

The local input operator is the two-sided slice of `rho` selected by the spectator coordinate of
`q` on rows and the independently selected spectator coordinate of `q'` on columns. The theorem
holds for every operator and every observed outcome, with no positivity, trace, self-adjointness,
or equality assumption on the two spectator coordinates. It is the coordinate form of extending
a local CP operation by identities on the spectator registers. -/
theorem liftAt_operation_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} (i : P)
    (I : Instrument (R.reg i) HH Outcome)
    (o : Outcome) (rho : Op R.total) (q q' : (R.set i HH).total) :
    ((I.liftAt R i).operation o rho) q q' =
    (I.operation o
    (rho.submatrix
    (fun x =>
    (R.splitAt i).symm
    (x, ((R.splitAtSet i HH) q).2))
    (fun y =>
    (R.splitAt i).symm
    (y, ((R.splitAtSet i HH) q').2))))
    ((R.splitAtSet i HH) q).1
    ((R.splitAtSet i HH) q').1 := by
  have hsum (f : R.total → ℂ) :
    (∑ x, f x) =
        ∑ p : R.reg i × R.rest i, f ((R.splitAt i).symm p) := by
    exact (Equiv.sum_comp (R.splitAt i).symm f).symm
  simp only [Instrument.operation, krausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Instrument.liftAt,
    Matrix.sum_apply, Matrix.mul_apply, localKrausLift_apply, ite_mul,
    zero_mul, Matrix.conjTranspose_apply, RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Matrix.submatrix_apply]
  rfl

end Instrument

end

end LOCC
