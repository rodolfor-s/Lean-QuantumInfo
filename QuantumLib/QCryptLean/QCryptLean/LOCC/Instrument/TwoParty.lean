import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty
import QCryptLean.Quantum.Operators.Basic

/-! # Two Party -/


noncomputable section

open Quantum.Operators (Op)

namespace LOCC

open TwoParty

variable {HH Outcome : Type} [Fintype HH] [DecidableEq HH] [Fintype Outcome]

/-- Alice's lifted Kraus matrix is supported on equal Bob coordinates. -/
theorem localKrausLift_alice_apply (R : MultipartiteSystem Party)
    (K : Matrix HH (R.reg .alice) ℂ) (a : HH) (b b' : R.reg .bob) (a' : R.reg .alice) :
    localKrausLift R .alice HH K ((R.set .alice HH).pairEquiv.symm (a, b))
        (R.pairEquiv.symm (a', b')) = if b = b' then K a a' else 0 := by
  rw [localKrausLift_apply]
  have hr : ((R.splitAtSet .alice HH) ((R.set .alice HH).pairEquiv.symm (a, b))).2 =
      ((R.splitAt .alice) (R.pairEquiv.symm (a', b'))).2 ↔ b = b' := by
    constructor
    · intro h
      exact congrFun h ⟨.bob, by decide⟩
    · intro h
      subst b'
      funext j
      rcases j with ⟨j, hj⟩
      cases j with
      | alice => exact (hj rfl).elim
      | bob => rfl
  rw [if_congr hr rfl rfl]
  rfl

/-- Bob's lifted Kraus matrix is supported on equal Alice coordinates. -/
theorem localKrausLift_bob_apply (R : MultipartiteSystem Party)
    (K : Matrix HH (R.reg .bob) ℂ) (a a' : R.reg .alice) (b : HH) (b' : R.reg .bob) :
    localKrausLift R .bob HH K ((R.set .bob HH).pairEquiv.symm (a, b))
        (R.pairEquiv.symm (a', b')) = if a = a' then K b b' else 0 := by
  rw [localKrausLift_apply]
  have hr : ((R.splitAtSet .bob HH) ((R.set .bob HH).pairEquiv.symm (a, b))).2 =
      ((R.splitAt .bob) (R.pairEquiv.symm (a', b'))).2 ↔ a = a' := by
    constructor
    · intro h
      exact congrFun h ⟨.alice, by decide⟩
    · intro h
      subst a'
      funext j
      rcases j with ⟨j, hj⟩
      cases j with
      | alice => rfl
      | bob => exact (hj rfl).elim
  rw [if_congr hr rfl rfl]
  rfl

namespace Instrument

/-- Alice's lifted operation preserves Bob's independent row and column coordinates. -/
theorem liftAt_alice_operation_apply (R : MultipartiteSystem Party)
    (I : Instrument (R.reg .alice) HH Outcome) (o : Outcome) (rho : Op R.total)
    (a a' : HH) (b b' : R.reg .bob) :
    (I.liftAt R .alice).operation o rho
        ((R.set .alice HH).pairEquiv.symm (a, b))
        ((R.set .alice HH).pairEquiv.symm (a', b')) =
      I.operation o (rho.submatrix (fun x => R.pairEquiv.symm (x, b))
        (fun x => R.pairEquiv.symm (x, b'))) a a' := by
  rw [liftAt_operation_apply]
  simp only [MultipartiteSystem.splitAtSet_apply, MultipartiteSystem.pairEquiv_symm_apply_alice]
  apply congrArg (fun sigma => I.operation o sigma a a')
  congr 1 <;> funext x j <;> cases j <;>
    simp [MultipartiteSystem.splitAt, MultipartiteSystem.pairEquiv] <;> rfl

/-- Bob's lifted operation preserves Alice's independent row and column coordinates. -/
theorem liftAt_bob_operation_apply (R : MultipartiteSystem Party)
    (I : Instrument (R.reg .bob) HH Outcome) (o : Outcome) (rho : Op R.total)
    (a a' : R.reg .alice) (b b' : HH) :
    (I.liftAt R .bob).operation o rho
        ((R.set .bob HH).pairEquiv.symm (a, b))
        ((R.set .bob HH).pairEquiv.symm (a', b')) =
      I.operation o (rho.submatrix (fun x => R.pairEquiv.symm (a, x))
        (fun x => R.pairEquiv.symm (a', x))) b b' := by
  rw [liftAt_operation_apply]
  simp only [MultipartiteSystem.splitAtSet_apply, MultipartiteSystem.pairEquiv_symm_apply_bob]
  apply congrArg (fun sigma => I.operation o sigma b b')
  congr 1 <;> funext x j <;> cases j <;>
    simp [MultipartiteSystem.splitAt, MultipartiteSystem.pairEquiv] <;> rfl

end Instrument

end LOCC
