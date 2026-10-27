import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Embedded maximally entangled vectors without dimension inequalities -/
noncomputable section
namespace Quantum.Operators
open Matrix
variable {X Y : Type*} [DecidableEq Y]

/-- The unnormalized maximally entangled vector along a specified register embedding. -/
def embeddedMaxEntangled (e : X ↪ Y) : Ket (X × Y) :=
  Ket.vectorize ((1 : Op Y).submatrix e id)

/-- Tracing out the larger register leaves the identity on the embedded register. -/
theorem partialTraceRight_embeddedMaxEntangled [Fintype Y] [DecidableEq X] (e : X ↪ Y) :
    Matrix.partialTraceRight (embeddedMaxEntangled e).projector = (1 : Op X) := by
  rw [embeddedMaxEntangled, Ket.partialTraceRight_vectorize, conjTranspose_submatrix,
    conjTranspose_one]
  change (1 : Op Y).submatrix e (Equiv.refl Y) * (1 : Op Y).submatrix (Equiv.refl Y) e = _
  rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_one_embedding]

end Quantum.Operators

namespace Quantum.Symmetry
open Matrix Quantum.Operators
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {k : ℕ}

/-- Embedded maximally entangled tensor vectors are fixed by simultaneous permutations. -/
theorem pairedProjectorOf_mulVec_embeddedMaxEntangled (e : X ↪ Y) :
    pairedProjectorOf X Y k *ᵥ (embeddedMaxEntangled
      (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).vec =
      (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).vec := by
  let v := (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).vec
  have hv : symmetricProjector (X × Y) k *ᵥ (v ∘ pairFunctions X Y k) =
      v ∘ pairFunctions X Y k := by
    apply (symmetricProjector_mulVec_eq_iff _).mpr
    intro σ a
    change (if (fun i => e ((a (σ i)).1)) = (fun i => (a (σ i)).2) then (1 : ℂ) else 0) =
      if (fun i => e (a i).1) = (fun i => (a i).2) then (1 : ℂ) else 0
    have he : (fun i => e ((a (σ i)).1)) = (fun i => (a (σ i)).2) ↔
        (fun i => e (a i).1) = (fun i => (a i).2) := by
      constructor
      · intro h
        funext i
        simpa only [Equiv.apply_symm_apply] using congrFun h (σ.symm i)
      · intro h
        funext i
        exact congrFun h (σ i)
    simp only [he]
  change (symmetricProjector (X × Y) k).submatrix
    (pairFunctions X Y k).symm (pairFunctions X Y k).symm *ᵥ v = v
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, hv]
  exact funext fun p => congrArg v ((pairFunctions X Y k).apply_symm_apply p)

/-- The embedded entangled projector is supported on the bipartite symmetric subspace. -/
theorem pairedProjectorOf_mul_embeddedMaxEntangled (e : X ↪ Y) :
    pairedProjectorOf X Y k * (embeddedMaxEntangled
      (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector =
      (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector := by
  change _ * vecMulVec _ _ = _
  rw [Matrix.mul_vecMulVec, pairedProjectorOf_mulVec_embeddedMaxEntangled]
  rfl

end Quantum.Symmetry
