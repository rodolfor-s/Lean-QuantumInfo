import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus

/-! # Coherent records of Kraus outcomes on natural product registers -/

noncomputable section

namespace Quantum.Channels

open Matrix

variable {X Y I : Type*}

/-- Stack a Kraus family into a coherent outcome register. -/
def recordKraus (K : I → Matrix Y X ℂ) : Matrix (Y × I) X ℂ :=
  fun p x => K p.2 p.1 x

/-- Completeness makes the coherent record an isometry, including empty registers. -/
theorem recordKraus_conjTranspose_mul_self [Fintype Y] [Fintype I] [DecidableEq X]
    (K : I → Matrix Y X ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (recordKraus K)ᴴ * recordKraus K = 1 := by
  rw [← hK]
  ext x y
  simp only [mul_apply, conjTranspose_apply, recordKraus, Matrix.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The isometric channel coherently retains the Kraus outcome. -/
theorem isChannel_recordKraus [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X]
    (K : I → Matrix Y X ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    IsChannel (krausMap (fun _ : Unit => recordKraus K)) := by
  refine ⟨isCompletelyPositive_krausMap _, ?_⟩
  intro A
  rw [trace_krausMap, Fintype.sum_unique, recordKraus_conjTranspose_mul_self K hK,
    Matrix.one_mul]

/-- The Kraus matrix that inserts a fixed classical value between two retained registers. -/
def writeKraus {A B : Type*} [DecidableEq A] [DecidableEq B]
    (X : Type*) [DecidableEq X] (x : X) : Matrix (A × X × B) (A × B) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = x ∧ p.2.2 = q.2 then 1 else 0

end Quantum.Channels
