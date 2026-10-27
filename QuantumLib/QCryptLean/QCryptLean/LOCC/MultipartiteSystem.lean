import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import QCryptLean.Quantum.Operators.Basic

/-!
# Finite-party multipartite systems

This module defines a party-indexed family of register types (`MultipartiteSystem`), the joint and
spectator registers, agreement away from one party (`MultipartiteSystem.AgreesOff`), register
updates (`MultipartiteSystem.set`), and the splitting equivalences used by local protocol steps.
-/

open Quantum.Operators (Op)

namespace LOCC

/-! ## The multipartite system: parties are a named finite type -/

/-- A finite register-index type for each party.

The finite party type `P` may have named constructors, such as `alice` and `bob` in
`TwoParty.Party`. Register indices label basis vectors, not arbitrary quantum states. -/
structure MultipartiteSystem (P : Type) [Fintype P] [DecidableEq P] where
  /-- The basis-index type of party `i`'s register. -/
  reg : P → Type
  [finReg : ∀ i, Fintype (reg i)]
  [decReg : ∀ i, DecidableEq (reg i)]

attribute [instance] MultipartiteSystem.finReg MultipartiteSystem.decReg

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The joint register's basis-index type: one local register index for each party. -/
abbrev MultipartiteSystem.total (R : MultipartiteSystem P) : Type := ∀ i, R.reg i

instance (R : MultipartiteSystem P) : Fintype R.total := Pi.instFintype
instance (R : MultipartiteSystem P) : DecidableEq R.total := Fintype.decidablePiFintype

/-! ### Agreement and register updates -/

/-- The multipartite systems have equal register types at every party other than `i`.

This is equality of types, not a chosen equivalence. -/
@[reducible] def MultipartiteSystem.AgreesOff (R R' : MultipartiteSystem P) (i : P) : Prop :=
  ∀ j, j ≠ i → R'.reg j = R.reg j

/-- A multipartite system agrees with itself away from every party. -/
theorem MultipartiteSystem.agreesOff_self (R : MultipartiteSystem P) (i : P) :
    R.AgreesOff R i := fun _ _ => rfl

/-- Two multipartite systems with the same family of register types are equal; the associated
instance fields are subsingletons. -/
theorem MultipartiteSystem.ext' {R R' : MultipartiteSystem P} (h : R.reg = R'.reg) : R = R' := by
  cases R; cases R'
  subst h
  congr 1 <;> exact Subsingleton.elim _ _

section

variable (R : MultipartiteSystem P) (i : P) (HH : Type) [Fintype HH] [DecidableEq HH]

/-- Replace party `i`'s register by `HH`, leaving every other register unchanged. -/
def MultipartiteSystem.set : MultipartiteSystem P where
  reg := Function.update R.reg i HH
  -- a `dite`, not `rcases`: these fields are DATA, so the case split must eliminate into `Type`
  finReg j :=
    if h : j = i then by subst h; rw [Function.update_self]; infer_instance
    else by rw [Function.update_of_ne h]; infer_instance
  decReg j :=
    if h : j = i then by subst h; rw [Function.update_self]; infer_instance
    else by rw [Function.update_of_ne h]; infer_instance

/-- Replacing party `i`'s register gives `HH` at that party. -/
@[simp] theorem MultipartiteSystem.set_reg_self :
    (R.set i HH).reg i = HH := Function.update_self _ _ _

/-- Replacing party `i`'s register leaves every distinct party's register unchanged. -/
@[simp] theorem MultipartiteSystem.set_reg_of_ne
    {j : P} (h : j ≠ i) : (R.set i HH).reg j = R.reg j := Function.update_of_ne h _ _

/-- Replacing party `i`'s register preserves the register types at all other parties. -/
theorem MultipartiteSystem.set_agreesOff :
    R.AgreesOff (R.set i HH) i := fun _ h => Function.update_of_ne h _ _

end

/-- Updating a register with its current type leaves the multipartite system unchanged. -/
@[simp] theorem MultipartiteSystem.set_self (R : MultipartiteSystem P) (i : P) :
    R.set i (R.reg i) = R :=
  MultipartiteSystem.ext' (Function.update_eq_self i R.reg)

/-- The other parties' registers, as seen from slot `i`. -/
abbrev MultipartiteSystem.rest (R : MultipartiteSystem P) (i : P) : Type :=
  ∀ j : {j // j ≠ i}, R.reg j

instance (R : MultipartiteSystem P) (i : P) : Fintype (R.rest i) := Pi.instFintype
instance (R : MultipartiteSystem P) (i : P) : DecidableEq (R.rest i) := Fintype.decidablePiFintype

/-- Split a joint register index into party `i`'s index and the spectators' indices. -/
def MultipartiteSystem.splitAt (R : MultipartiteSystem P) (i : P) : R.total ≃ R.reg i × R.rest i :=
  Equiv.piSplitAt i R.reg

section

variable (R : MultipartiteSystem P) (i : P) (HH : Type) [Fintype HH] [DecidableEq HH]

/-- Split the updated joint register into the replacement register and the original spectators. -/
def MultipartiteSystem.splitAtSet :
    (R.set i HH).total ≃ HH × R.rest i :=
  (Equiv.piSplitAt i (R.set i HH).reg).trans
    (Equiv.prodCongr (Equiv.cast (R.set_reg_self i HH))
      (Equiv.piCongrRight fun j => Equiv.cast (R.set_reg_of_ne i HH j.2)))

/-- Coordinates of the updated joint register transported to the replacement and spectators. -/
@[simp] theorem MultipartiteSystem.splitAtSet_apply (a : (R.set i HH).total) :
    R.splitAtSet i HH a =
      (cast (R.set_reg_self i HH) (a i),
        fun j : {j // j ≠ i} => cast (R.set_reg_of_ne i HH j.2) (a j)) := rfl

end

/-- Transport of a joint coordinate acts locally by the induced register type equalities. -/
@[simp] theorem MultipartiteSystem.cast_total_apply {R S : MultipartiteSystem P} (h : R = S)
    (q : R.total) (i : P) :
    (cast (congrArg MultipartiteSystem.total h) q) i =
      cast (congrArg (fun T => T.reg i) h) (q i) := by
  cases h
  rfl

/-- A register-preserving update's splitting transports joint coordinates by `set_self`. -/
@[simp] theorem MultipartiteSystem.splitAtSet_self_symm (R : MultipartiteSystem P) (i : P)
    (q : R.total) :
    (R.splitAtSet i (R.reg i)).symm (R.splitAt i q) =
      cast (congrArg MultipartiteSystem.total (R.set_self i).symm) q := by
  apply (R.splitAtSet i (R.reg i)).injective
  simp [MultipartiteSystem.splitAtSet_apply, MultipartiteSystem.splitAt]

end LOCC
