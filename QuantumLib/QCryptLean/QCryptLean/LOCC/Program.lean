import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.SystemPresentation

/-!
# Local protocols and their public outputs

`Program R` computes its public boundary from its actions and continuations. Terminal values
belong to a family indexed by the actual final system; the default family is trivial. Successor
presentations are selected in the constructors, so no transport obstructs boundary computation.

## Writing a protocol

Open `LOCC`; let `ask` and `discard` be direct instrument actions at `system Bool Bool`,
announcing Alice's bit and discarding her register, respectively:

```lean
def tail : Program (system Bool Bool) := .done
def conversation : Program (system Bool Bool) :=
  ask.then fun bit =>
    if bit = true then tail
    else discard.then .done
```

Use ordinary recursive functions in continuation-passing style for loops. For symbolic public
branches, boundary equations follow by cases on the announced value; concrete branches compute.
-/

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]

/-- Recursive protocol syntax with a fixed terminal family and a varying start system. -/
inductive Program.Syntax (End : MultipartiteSystem P → Type 1) : MultipartiteSystem P → Type 1
  /-- Terminate with a value checked against the current system. -/
  | done {R} (value : End R) : Program.Syntax End R
  /-- Execute a private action without exposing its outcome. -/
  | priv {R} (a : PrivateAction R)
      (k : Program.Syntax End (SystemPresentation.update R a.actor a.Output)) : Program.Syntax End R
  /-- Execute an announced action and continue using its public value. -/
  | announced {R Y} [Fintype Y] [DecidableEq Y] (a : AnnouncedAction R Y)
      (k : ∀ y, Program.Syntax End (SystemPresentation.update R a.actor (a.Output y))) :
        Program.Syntax End R

/-- A local protocol with an optional terminal family, trivial for ordinary LOCC programs. -/
abbrev Program (R : MultipartiteSystem P)
    (End : MultipartiteSystem P → Type 1 := fun _ => PUnit) : Type 1 := Program.Syntax End R

namespace Program

variable {R : MultipartiteSystem P} {End : MultipartiteSystem P → Type 1}

/-- Terminate with a value from the terminal family at the current system. For the default
trivial family the value is filled in automatically, so an ordinary program writes `.done`. -/
@[match_pattern] abbrev done
    (value : End R := by
      first
      | exact PUnit.unit
      | fail "no terminal value: give one explicitly, or check that this continuation starts at \
          the system left by the previous action") :
    Program R End :=
  Syntax.done value

/-- Execute a private action and continue at its successor system. -/
@[match_pattern] abbrev priv (a : PrivateAction R)
    (k : Program (SystemPresentation.update R a.actor a.Output) End) : Program R End :=
  Syntax.priv a k

/-- Execute an announcement and continue using its public value. -/
@[match_pattern] abbrev announced {Y : Type} [Fintype Y] [DecidableEq Y]
    (a : AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R a.actor (a.Output y)) End) : Program R End :=
  Syntax.announced a k

/-- The output boundary computed from the program's public branches. -/
@[reducible] noncomputable def boundary {R : MultipartiteSystem P}
    (p : Program R End) : Boundary P :=
  Syntax.rec (motive := fun _ _ => Boundary P)
    (fun {R} _ => Boundary.leaf R)
    (fun _ _ result => result)
    (fun {_ Y} [Fintype Y] [DecidableEq Y] _ _ result => Boundary.announce Y result) p

/-- Read the terminal value at a complete public exit. -/
noncomputable def terminal {R : MultipartiteSystem P} (p : Program R End) :
    ∀ e, End (p.boundary.system e) :=
  -- Primitive recursion keeps dependent lookups from expanding course-of-values tables.
  Syntax.rec (motive := fun _ p => ∀ e, End ((boundary p).system e))
    (fun value _ => value)
    (fun _ _ result => result)
    (fun _ k result e => by
      change (Σ y, (boundary (k y)).Exit) at e
      exact result e.1 e.2) p

end Program

/-- Continue after a private action at its computational successor presentation. -/
abbrev PrivateAction.then {R : MultipartiteSystem P} {End : MultipartiteSystem P → Type 1}
    (a : LOCC.PrivateAction R) (k : Program (SystemPresentation.update R a.actor a.Output) End) :
    Program R End := .priv a k

/-- Continue after an announcement using only its public value. -/
abbrev AnnouncedAction.then {R : MultipartiteSystem P}
    {End : MultipartiteSystem P → Type 1}
    {Y : Type} [Fintype Y] [DecidableEq Y] (a : LOCC.AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R a.actor (a.Output y)) End) : Program R End :=
  .announced a k

end LOCC
