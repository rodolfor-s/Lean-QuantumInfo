import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Quantum.Channels.KrausAlgebra

/-! # Instrument -/


open scoped Matrix BigOperators Kronecker
open Matrix

namespace LOCC
open Quantum.Operators (Op)
variable {P : Type} [Fintype P] [DecidableEq P]


/-- **A quantum instrument with physical outcomes separated from Kraus multiplicity.**

`Outcome` is the value that the acting laboratory observes. The dependent fibre
`krausIndex o` is an internal index for a Kraus representation of the completely positive map at
that outcome. Packaging an instrument as an `AnnouncedAction` may expose only a chosen
coarse-graining of `Outcome`; packaging it as a `PrivateAction` exposes no outcome to the
continuation. Neither form exposes `krausIndex o` to program control flow.

This is the instrument-tree object of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2: an observed branch is a CP map and therefore may contain more than one
Kraus operator. Completeness is the double sum over observed outcomes and their internal Kraus
fibres. -/
structure Instrument (Hin Hout : Type) [Fintype Hin] [DecidableEq Hin]
    [Fintype Hout] [DecidableEq Hout] (Outcome : Type) [Fintype Outcome] where
  /-- The internal Kraus-index fibre of an observed outcome. -/
  krausIndex : Outcome → Type
  [finKrausIndex : ∀ o, Fintype (krausIndex o)]
  /-- A Kraus operator internal to the CP map of outcome `o`. -/
  kraus : ∀ o, krausIndex o → Matrix Hout Hin ℂ
  /-- Completeness over observed outcomes and internal Kraus indices. -/
  complete : ∑ o, ∑ r, (kraus o r)ᴴ * kraus o r = 1

attribute [instance] Instrument.finKrausIndex

section

variable {Hin Hout Outcome : Type} [Fintype Hin] [DecidableEq Hin] [Fintype Hout] [DecidableEq Hout]
  [Fintype Outcome]

/-- A flattened branch is a physical outcome paired with one element of its internal Kraus
fibre. It is algebraic bookkeeping and is not an observable protocol value. -/
abbrev Instrument.Branch
    (I : Instrument Hin Hout Outcome) : Type := Σ o, I.krausIndex o

/-- Read the Kraus operator at a flattened algebraic branch. -/
def Instrument.flatKraus
    (I : Instrument Hin Hout Outcome) (b : I.Branch) : Matrix Hout Hin ℂ :=
  I.kraus b.1 b.2

/-- Regard a fine family with one Kraus operator per observed outcome as an instrument. The
internal fibre is `Unit`, so this conversion never creates a hidden operational value. -/
def Instrument.ofFine
    (K : Outcome → Matrix Hout Hin ℂ) (hK : ∑ o, (K o)ᴴ * K o = 1) :
    Instrument Hin Hout Outcome where
  krausIndex _ := Unit
  kraus o _ := K o
  complete := by simpa using hK

end

/-- **Keep the observed outcome and nothing from the internal Kraus fibre.** In the output
ordering `HH × Outcome`, the Kraus operators are `Kₒ,ᵣ ⊗ |o⟩`. It respects equality of the CP
operation at each observed outcome (`Instrument.OperationallyEquivalent.keeping`); it does not
assert invariance under an arbitrary refinement of a Kraus fibre. -/
def Instrument.keeping {A HH Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype HH] [DecidableEq HH] [Fintype Outcome] [DecidableEq Outcome]
    (I : Instrument A HH Outcome) : Instrument A (HH × Outcome) Outcome where
  krausIndex := I.krausIndex
  kraus o r := Matrix.of fun p a => if p.2 = o then I.kraus o r p.1 a else 0
  complete := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    have key : ∀ (o : Outcome) (r : I.krausIndex o),
        (∑ h : HH, ∑ y : Outcome, star (if y = o then I.kraus o r h a else 0) *
            (if y = o then I.kraus o r h b else 0))
          = ∑ h : HH, star (I.kraus o r h a) * I.kraus o r h b := by
      intro o r
      refine Finset.sum_congr rfl fun h _ => ?_
      simp [Finset.sum_ite_eq']
    rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun r _ => key o r]
    have := congrFun (congrFun I.complete a) b
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using this


section

variable (R : MultipartiteSystem P) (i : P) (HH : Type) [Fintype HH] [DecidableEq HH]

/-- Lift a matrix acting on party `i` to the joint register, replacing that party's register
by `HH` and acting as the identity on every spectator register. -/
def localKrausLift
    (K : Matrix HH (R.reg i) ℂ) : Matrix (R.set i HH).total R.total ℂ :=
  (K ⊗ₖ (1 : Matrix (R.rest i) (R.rest i) ℂ)).submatrix
    (R.splitAtSet i HH) (R.splitAt i)

/-- The local matrix entry is multiplied by the indicator that all spectator coordinates agree. -/
@[simp] theorem localKrausLift_apply
    (K : Matrix HH (R.reg i) ℂ)
    (a : (R.set i HH).total) (b : R.total) :
    localKrausLift R i HH K a b =
      if ((R.splitAtSet i HH) a).2 = ((R.splitAt i) b).2 then
        K ((R.splitAtSet i HH) a).1 ((R.splitAt i) b).1
      else 0 := by
  simp only [localKrausLift, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- A local lift's Gram matrix is the local Gram matrix tensored with spectator identities. -/
theorem localKrausLift_conjTranspose_mul_self
    (K : Matrix HH (R.reg i) ℂ) :
    (localKrausLift R i HH K)ᴴ * localKrausLift R i HH K =
      ((Kᴴ * K) ⊗ₖ (1 : Matrix (R.rest i) (R.rest i) ℂ)).submatrix
        (R.splitAt i) (R.splitAt i) := by
  rw [localKrausLift, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]

end

/-- Complete local Kraus families remain complete after extension by spectator identities,
including families whose output register depends on the outcome. -/
theorem localKrausLift_complete_dependent {X : Type} [Fintype X]
    (R : MultipartiteSystem P) (i : P) (HH : X → Type)
    [∀ x, Fintype (HH x)] [∀ x, DecidableEq (HH x)]
    (K : ∀ x, Matrix (HH x) (R.reg i) ℂ)
    (hK : ∑ x, (K x)ᴴ * K x = 1) :
    ∑ x, (localKrausLift R i (HH x) (K x))ᴴ *
      localKrausLift R i (HH x) (K x) = 1 := by
  simp only [localKrausLift_conjTranspose_mul_self]
  ext a b
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ← Finset.sum_mul]
  have hc := congrFun (congrFun hK ((R.splitAt i) a).1) ((R.splitAt i) b).1
  simp only [Matrix.sum_apply] at hc
  rw [hc]
  by_cases hab : a = b
  · subst hab
    simp
  · have hne : (R.splitAt i) a ≠ (R.splitAt i) b := fun h =>
      hab ((R.splitAt i).injective h)
    by_cases h1 : ((R.splitAt i) a).1 = ((R.splitAt i) b).1
    · have h2 : ((R.splitAt i) a).2 ≠ ((R.splitAt i) b).2 := fun h2 =>
        hne (Prod.ext_iff.mpr ⟨h1, h2⟩)
      rw [ite_eq_right h2, ite_eq_right hab, mul_zero]
    · rw [ite_eq_right hab, Matrix.one_apply_ne h1]
      simp

/-- Lift an instrument to the joint register, replacing only its actor's register. -/
def Instrument.liftAt (R : MultipartiteSystem P) (i : P) {HH : Type}
    [Fintype HH] [DecidableEq HH] {Outcome : Type} [Fintype Outcome]
    (I : Instrument (R.reg i) HH Outcome) :
    Instrument R.total (R.set i HH).total Outcome where
  krausIndex := I.krausIndex
  kraus o r := localKrausLift R i HH (I.kraus o r)
  complete := by
    have hflat : ∑ b : I.Branch, (I.flatKraus b)ᴴ * I.flatKraus b = 1 := by
      simpa only [Fintype.sum_sigma, Instrument.flatKraus] using I.complete
    have hlift := localKrausLift_complete_dependent R i (fun _ : I.Branch => HH)
      I.flatKraus hflat
    simpa only [Fintype.sum_sigma, Instrument.flatKraus] using hlift

end LOCC
