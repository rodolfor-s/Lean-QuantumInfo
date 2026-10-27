import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-!
# Local actions with public and private outcomes

Each action carries its actor and the output register of its instrument. Its output system replaces
that actor's input register. Announced actions have one output register per public value; only the
public value selects a continuation, while raw outcomes and Kraus indices remain private.
-/

open Quantum.Channels (
  krausMap)

open scoped Matrix BigOperators
open Matrix

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A local quantum action with a coarse public outcome and a public-value-dependent output
register. All spectator registers are preserved by construction. -/
structure AnnouncedAction (R : MultipartiteSystem P) (Public : Type)
    [Fintype Public] [DecidableEq Public] where
  /-- The party applying the local instrument. -/
  actor : P
  /-- The actor's output register on each public branch. -/
  Output : Public → Type
  [finOutput : ∀ y, Fintype (Output y)]
  [decOutput : ∀ y, DecidableEq (Output y)]
  /-- The finite raw outcome type of the local instrument. -/
  Outcome : Type
  [finOutcome : Fintype Outcome]
  /-- Coarse-grain a raw outcome to the value made public. -/
  announce : Outcome → Public
  /-- Internal Kraus multiplicity in the CP map for a raw outcome. -/
  krausIndex : Outcome → Type
  [finKrausIndex : ∀ o, Fintype (krausIndex o)]
  /-- A party-local Kraus matrix with announcement-dependent codomain. -/
  kraus : ∀ o, krausIndex o → Matrix (Output (announce o)) (R.reg actor) ℂ
  /-- Trace-preserving completeness over raw outcomes and their Kraus fibres. -/
  complete : ∑ o, ∑ r, (kraus o r)ᴴ * kraus o r = 1

attribute [instance] AnnouncedAction.finOutput
  AnnouncedAction.decOutput AnnouncedAction.finOutcome AnnouncedAction.finKrausIndex

namespace AnnouncedAction

variable {Output Outcome : Type} [Fintype Output] [DecidableEq Output] [Fintype Outcome]

variable {R : MultipartiteSystem P} {Public : Type} [Fintype Public] [DecidableEq Public]

/-- The output system after the action announces `y`. -/
@[reducible] def out (A : AnnouncedAction R Public) (y : Public) : MultipartiteSystem P :=
  R.set A.actor (A.Output y)

/-- The actor's register is the local instrument's output register. -/
theorem out_reg_actor (A : AnnouncedAction R Public) (y : Public) :
    (A.out y).reg A.actor = A.Output y := R.set_reg_self _ _

/-- Every other party retains its input register. -/
theorem out_reg_of_ne (A : AnnouncedAction R Public) (y : Public)
    {j : P} (h : j ≠ A.actor) : (A.out y).reg j = R.reg j := R.set_reg_of_ne _ _ h

/-- An announced action preserves all registers away from its actor. -/
theorem agreesOff (A : AnnouncedAction R Public) (y : Public) :
    R.AgreesOff (A.out y) A.actor := R.set_agreesOff _ _

/-- Regard a fixed-output instrument as an announced action, coarse-graining its raw outcomes. -/
@[implicit_reducible] def ofInstrument (actor : P)
    (I : Instrument (R.reg actor) Output Outcome) (announce : Outcome → Public) :
    AnnouncedAction R Public where
  actor := actor
  Output := fun _ => Output
  Outcome := Outcome
  announce := announce
  krausIndex := I.krausIndex
  kraus := I.kraus
  complete := I.complete

/-- The output of an instrument announcement replaces its actor's register. -/
@[simp] theorem out_ofInstrument (i : P)
    (I : Instrument (R.reg i) Output Outcome)
    (announce : Outcome → Public) (y : Public) :
    (ofInstrument i I announce).out y = R.set i Output := rfl

/-- Announcing an instrument that retains its register preserves the input system. -/
theorem out_ofInstrument_self (i : P)
    (I : Instrument (R.reg i) (R.reg i) Outcome) (announce : Outcome → Public) (y : Public) :
    (ofInstrument i I announce).out y = R := R.set_self i

/-- The branch-dependent output boundary obtained by running one announced action. -/
def boundary (A : AnnouncedAction R Public) : Boundary P :=
  .announce Public fun y => .leaf (A.out y)

/-- Lift one raw Kraus matrix to the joint register, leaving spectator coordinates unchanged. -/
def liftedKraus (A : AnnouncedAction R Public) (o : A.Outcome)
    (r : A.krausIndex o) : Matrix (A.out (A.announce o)).total R.total ℂ :=
  localKrausLift R A.actor (A.Output (A.announce o)) (A.kraus o r)

/-- The completely positive joint-register operation at one raw outcome, summing its Kraus fibre. -/
noncomputable def liftedOperation (A : AnnouncedAction R Public) (o : A.Outcome) :
    Op R.total →ₗ[ℂ] Op (A.out (A.announce o)).total :=
  krausMap (A.liftedKraus o)

/-- The joint-register Kraus entry vanishes unless all spectator coordinates agree. -/
@[simp] theorem liftedKraus_apply (A : AnnouncedAction R Public) (o : A.Outcome)
    (r : A.krausIndex o) (a : (A.out (A.announce o)).total) (b : R.total) :
    A.liftedKraus o r a b =
      if ((R.splitAtSet A.actor (A.Output (A.announce o))) a).2 =
          ((R.splitAt A.actor) b).2 then
        A.kraus o r ((R.splitAtSet A.actor (A.Output (A.announce o))) a).1
          ((R.splitAt A.actor) b).1
      else 0 :=
  localKrausLift_apply R A.actor (A.Output (A.announce o)) (A.kraus o r) a b

/-- The joint-register Kraus matrices are complete over all raw outcomes and Kraus fibres. -/
theorem liftedKraus_complete (A : AnnouncedAction R Public) :
    ∑ o, ∑ r, (A.liftedKraus o r)ᴴ * A.liftedKraus o r = 1 := by
  let X := Σ o : A.Outcome, A.krausIndex o
  let K : ∀ x : X, Matrix (A.Output (A.announce x.1)) (R.reg A.actor) ℂ :=
    fun x => A.kraus x.1 x.2
  have hK : ∑ x : X, (K x)ᴴ * K x = 1 := by
    simpa only [X, K, Fintype.sum_sigma] using A.complete
  have hLift := localKrausLift_complete_dependent R A.actor
    (fun x : X => A.Output (A.announce x.1)) K hK
  simpa only [X, K, Fintype.sum_sigma, liftedKraus] using hLift

/-- Packaging an instrument as an announced action preserves each lifted raw-outcome operation. -/
theorem liftedOperation_ofInstrument_eq_liftAt_operation
    (i : P)
    (I : Instrument (R.reg i) Output Outcome) (announce : Outcome → Public) (o : Outcome) :
    (ofInstrument i I announce).liftedOperation o = (I.liftAt R i).operation o := rfl

end AnnouncedAction

/-- A local instrument whose physical outcome remains private. The output system replaces only
its actor's register with the instrument's output register. -/
structure PrivateAction (R : MultipartiteSystem P) where
  /-- The party applying the local instrument. -/
  actor : P
  /-- The actor's output register. -/
  Output : Type
  [finOutput : Fintype Output]
  [decOutput : DecidableEq Output]
  /-- The finite private outcome type of the instrument. -/
  Outcome : Type
  [finOutcome : Fintype Outcome]
  /-- The local instrument whose outcome remains private. -/
  instrument : Instrument (R.reg actor) Output Outcome

attribute [instance] PrivateAction.finOutput
  PrivateAction.decOutput PrivateAction.finOutcome

namespace PrivateAction

variable {Output Outcome : Type} [Fintype Output] [DecidableEq Output] [Fintype Outcome]

variable {R : MultipartiteSystem P}

/-- The output system obtained by replacing the actor's register. -/
@[reducible] def out (A : PrivateAction R) : MultipartiteSystem P := R.set A.actor A.Output

/-- The actor's register is the local instrument's output register. -/
theorem out_reg_actor (A : PrivateAction R) : A.out.reg A.actor = A.Output :=
  R.set_reg_self _ _

/-- Every other party retains its input register. -/
theorem out_reg_of_ne (A : PrivateAction R) {j : P} (h : j ≠ A.actor) :
    A.out.reg j = R.reg j := R.set_reg_of_ne _ _ h

/-- A private action preserves all registers away from its actor. -/
theorem agreesOff (A : PrivateAction R) : R.AgreesOff A.out A.actor := R.set_agreesOff _ _

/-- Package an existing local instrument as a private action. -/
@[implicit_reducible] def ofInstrument (actor : P)
    (I : Instrument (R.reg actor) Output Outcome) : PrivateAction R where
  actor := actor
  Output := Output
  Outcome := Outcome
  instrument := I

/-- The output of a private instrument replaces its actor's register. -/
@[simp] theorem out_ofInstrument (i : P)
    (I : Instrument (R.reg i) Output Outcome) :
    (ofInstrument i I).out = R.set i Output := rfl

/-- A private instrument that retains its register preserves the input system. -/
theorem out_ofInstrument_self (i : P)
    (I : Instrument (R.reg i) (R.reg i) Outcome) :
    (ofInstrument i I).out = R := R.set_self i

/-- Lift one private Kraus matrix to the joint register, preserving every spectator coordinate. -/
def liftedKraus (A : PrivateAction R) (o : A.Outcome)
    (r : A.instrument.krausIndex o) : Matrix A.out.total R.total ℂ :=
  localKrausLift R A.actor A.Output (A.instrument.kraus o r)

/-- The completely positive joint-register operation at one private outcome. -/
noncomputable def liftedOperation (A : PrivateAction R) (o : A.Outcome) :
    Op R.total →ₗ[ℂ] Op A.out.total :=
  krausMap (A.liftedKraus o)

/-- The joint-register Kraus matrices of a private action are complete. -/
theorem liftedKraus_complete (A : PrivateAction R) :
    ∑ o, ∑ r, (A.liftedKraus o r)ᴴ * A.liftedKraus o r = 1 := by
  let X := Σ o : A.Outcome, A.instrument.krausIndex o
  let K : X → Matrix A.Output (R.reg A.actor) ℂ := fun x => A.instrument.kraus x.1 x.2
  have hK : ∑ x : X, (K x)ᴴ * K x = 1 := by
    simpa only [X, K, Fintype.sum_sigma] using A.instrument.complete
  have hLift := localKrausLift_complete_dependent R A.actor (fun _ : X => A.Output) K hK
  simpa only [X, K, Fintype.sum_sigma, liftedKraus] using hLift

/-- Packaging an instrument as a private action preserves each lifted raw-outcome operation. -/
theorem liftedOperation_ofInstrument_eq_liftAt_operation
    (i : P)
    (I : Instrument (R.reg i) Output Outcome) (o : Outcome) :
    (ofInstrument i I).liftedOperation o = (I.liftAt R i).operation o := rfl

end PrivateAction
end LOCC
