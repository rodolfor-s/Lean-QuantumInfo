import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Discard -/


open Quantum.Channels (
  krausMap)

open scoped Matrix BigOperators
open Matrix

open Quantum.Operators (Op)

namespace LOCC

variable (K : Type) [Fintype K] [DecidableEq K]

/-- **Discard a finite local register to the trivial register.**

The observed outcome is `Unit`. The input basis `K` is instead the hidden Kraus fibre, with
Kraus matrices `⟨k|`. Thus the total operation is the partial trace to a one-dimensional
factor. This is the local discard operation used in the instrument trees of
Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
def Instrument.discardToUnit :
    Instrument K Unit Unit where
  krausIndex _ := K
  kraus _ k := Matrix.of fun _ x => if x = k then 1 else 0
  complete := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply, Finset.univ_unique, Finset.sum_singleton,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq Finset.univ x (fun k => if y = k then (1 : ℂ) else 0)]
    simp only [Finset.mem_univ, ite_true]
    exact if_congr eq_comm rfl rfl

/-- The individual hidden Kraus matrices of `discardToUnit` are the basis bras. -/
@[simp] theorem Instrument.discardToUnit_kraus_apply
    (k x : K) :
    (Instrument.discardToUnit K).kraus () k () x =
      if x = k then 1 else 0 := rfl

/-- Distinct input and hidden-basis indices give a zero entry. In particular, on every basis of
cardinality greater than one, `discardToUnit` is not represented by a one-row all-ones Kraus
matrix. -/
theorem Instrument.discardToUnit_kraus_apply_of_ne
    (k x : K) (h : x ≠ k) :
    (Instrument.discardToUnit K).kraus () k () x = 0 := by
  simp [Instrument.discardToUnit_kraus_apply, h]

/-- The hidden basis-bra Kraus family satisfies the resolution of the identity. -/
theorem Instrument.discardToUnit_complete :
    ∑ k : K, ((Instrument.discardToUnit K).kraus () k)ᴴ *
      (Instrument.discardToUnit K).kraus () k = 1 := by
  have h := (Instrument.discardToUnit K).complete
  rw [Fintype.sum_unique] at h
  exact h

/-- The unique observed operation of `discardToUnit` returns the trace of the input matrix. -/
@[simp] theorem Instrument.discardToUnit_operation_apply
    (rho : Op K) :
    ((Instrument.discardToUnit K).operation () rho) () () = ∑ x : K, rho x x := by
  simp only [Instrument.operation, krausMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Instrument.discardToUnit]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply]

/-- The total channel of `discardToUnit` is its unique operation and returns the matrix trace. -/
@[simp] theorem Instrument.discardToUnit_channel_apply
    (rho : Op K) :
    ((Instrument.discardToUnit K).channel rho) () () = ∑ x : K, rho x x := by
  simp [Instrument.channel_eq_sum, Instrument.discardToUnit_operation_apply]

end LOCC
