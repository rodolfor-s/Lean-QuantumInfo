import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-!
# Classical processing and quantum register relabelling

Classical processing measures the input basis and prepares the function value.
Quantum relabelling preserves every matrix entry, including off-diagonal entries.
-/

noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Relabelling a quantum register is a channel on the full operator space. -/
theorem isChannel_reindex (e : X ≃ Y) :
    IsChannel (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap := by
  refine ⟨isCompletelyPositive_of_mapTensorId_posSemidef _ ?_, ?_⟩
  · intro A hA
    exact hA.submatrix (fun p : Y × X => (e.symm p.1, p.2))
  · intro A
    exact Matrix.reindex_trace e A

variable [DecidableEq X] [DecidableEq Y]

/-- Measure a classical input label and prepare its image under a function. -/
def classicalMap (f : X → Y) : Operation X Y :=
  krausMap (fun x => Matrix.single (f x) x 1)

omit [Fintype Y] in
/-- Classical processing discards off-diagonal input entries. -/
theorem classicalMap_apply (f : X → Y) (A : Op X) :
    classicalMap f A = ∑ x, Matrix.single (f x) (f x) (A x x) := by
  ext i j
  simp [classicalMap, krausMap]

/-- A deterministic function on classical labels defines a channel. -/
theorem isChannel_classicalMap (f : X → Y) : IsChannel (classicalMap f) := by
  refine ⟨isCompletelyPositive_krausMap _, ?_⟩
  intro A
  rw [classicalMap_apply, Matrix.trace_sum]
  simp [Matrix.trace]

/-- Recording retains the measured label together with its classical function value. -/
def recordingMap (f : X → Y) : Operation X (X × Y) :=
  classicalMap (fun x => (x, f x))

/-- Recording a function of a measured label is trace preserving and completely positive. -/
theorem isChannel_recordingMap (f : X → Y) : IsChannel (recordingMap f) :=
  isChannel_classicalMap _

omit [Fintype Y] [DecidableEq Y] in
/-- Dephasing commutes with a unitary that permutes the coordinate projectors. -/
theorem classicalMap_id_conj_of_permutes_single (U : Op X) (π : Equiv.Perm X)
    (hU : Uᴴ * U = 1)
    (hperm : ∀ x, U * single x x 1 * Uᴴ = single (π x) (π x) 1) (A : Op X) :
    classicalMap id (U * A * Uᴴ) = U * classicalMap id A * Uᴴ := by
  have hPU (x : X) : single (π x) (π x) 1 * U = U * single x x 1 := by
    rw [← hperm, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hUP (x : X) : Uᴴ * single (π x) (π x) 1 = single x x 1 * Uᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_single, star_one, conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose (hPU x)
  change (∑ x, single x x 1 * (U * A * Uᴴ) * (single x x 1)ᴴ) =
    U * (∑ x, single x x 1 * A * (single x x 1)ᴴ) * Uᴴ
  simp only [conjTranspose_single, star_one]
  rw [Matrix.mul_sum, Matrix.sum_mul,
    ← Equiv.sum_comp π (fun x => single x x 1 * (U * A * Uᴴ) * single x x 1)]
  apply Finset.sum_congr rfl
  intro x _
  calc _ = (single (π x) (π x) 1 * U) * A * (Uᴴ * single (π x) (π x) 1) := by
             simp only [Matrix.mul_assoc]
       _ = U * (single x x 1 * A * single x x 1) * Uᴴ := by
             rw [hPU, hUP]
             simp only [Matrix.mul_assoc]

end Quantum.Channels
