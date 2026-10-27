import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

/-! # Transcript -/


namespace LOCC


/-- A list of announced outcome alphabets, each carrying its own finiteness.

`Transcript` turns the word into its product register, and `Fintype.card` gives that register's
numeric dimension. -/
inductive TList : Type 1
  /-- The empty transcript. -/
  | nil : TList
  /-- One announced alphabet followed by a transcript. -/
  | cons (XX : Type) [Fintype XX] [DecidableEq XX] (T : TList) : TList

/-- Chronological concatenation of transcript words. -/
def TList.append (T U : TList) : TList :=
  match T with
  | .nil => U
  | @TList.cons XX fX dX tail => @TList.cons XX fX dX (tail.append U)

/-- Concatenating after a transcript head preserves that head. -/
@[simp] theorem TList.cons_append (XX : Type) [Fintype XX] [DecidableEq XX] (T U : TList) :
    TList.append (.cons XX T) U = .cons XX (TList.append T U) := rfl

/-- **The transcript register** that a list of alphabets denotes. -/
def Transcript (T : TList) : Type :=
  match T with
  | .nil => Unit
  | @TList.cons XX _ _ tail => XX × Transcript tail

instance instFintypeTranscript (T : TList) : Fintype (Transcript T) :=
  match T with
  | .nil => inferInstanceAs (Fintype Unit)
  | @TList.cons XX fX _ tail =>
      letI := fX
      letI := instFintypeTranscript tail
      inferInstanceAs (Fintype (XX × Transcript tail))

instance instDecEqTranscript (T : TList) : DecidableEq (Transcript T) :=
  match T with
  | .nil => inferInstanceAs (DecidableEq Unit)
  | @TList.cons XX _ dX tail =>
      letI := dX
      letI := instDecEqTranscript tail
      inferInstanceAs (DecidableEq (XX × Transcript tail))

/-- The transcript register of a concatenation splits into its two component registers. -/
def Transcript.appendEquiv (T U : TList) :
    Transcript (TList.append T U) ≃ Transcript T × Transcript U :=
  match T with
  | .nil => (Equiv.punitProd _).symm
  | @TList.cons XX _ _ tail =>
      (Equiv.prodCongrRight fun _ => Transcript.appendEquiv tail U).trans
        (Equiv.prodAssoc XX (Transcript tail) (Transcript U)).symm

/-- Move the final transcript factor to the front. -/
noncomputable def Transcript.lastFactorToFront (T : TList) (α : Type)
    [Fintype α] [DecidableEq α] :
    Transcript (TList.append T (.cons α .nil)) ≃ α × Transcript T :=
  (Transcript.appendEquiv T (.cons α .nil)).trans
    ((Equiv.prodCongr (Equiv.refl (Transcript T)) (Equiv.prodPUnit α)).trans
      (Equiv.prodComm (Transcript T) α))

/-- Transport through a transcript-tail equality commutes with two leading cells. -/
theorem Transcript.cast_two_cons
    (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {T U : TList} (h : T = U) (x : α) (y : β) (t : Transcript T) :
    Equiv.cast (congrArg Transcript
        (congrArg (fun V : TList => TList.cons α (TList.cons β V)) h))
        (x, (y, t)) =
      (x, (y, Equiv.cast (congrArg Transcript h) t)) := by
  cases h
  rfl

end LOCC
