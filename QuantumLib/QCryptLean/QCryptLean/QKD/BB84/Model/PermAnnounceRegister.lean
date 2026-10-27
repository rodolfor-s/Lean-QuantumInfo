import QCryptLean.Math.LinearAlgebra.PermutationMatrix
import QCryptLean.Quantum.Operators.Basic

/-! # Perm Announce Register -/


open Quantum.Operators Matrix

noncomputable section

namespace QKD.BB84.Model

/-- The projector recording the announced permutation. -/
def permAnnounceProjector (n : ℕ) (perm : Equiv.Perm (Fin n)) :
    Op (Equiv.Perm (Fin n)) :=
  Matrix.single perm perm 1

/-- Right multiplication on the public permutation-announcement label. -/
def permAnnounceRightMulEquiv (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
  Equiv.mulRight π

/-- Relabel the announcement register by right multiplication. -/
def permAnnounceRightMulUnitary (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Op (Equiv.Perm (Fin n)) :=
  Equiv.Perm.permMatrix ℂ (permAnnounceRightMulEquiv n π).symm

/-- Right multiplication sends the projector for `perm` to the projector for `perm * π`. -/
theorem permAnnounceRightMulUnitary_projector (n : ℕ) (π perm : Equiv.Perm (Fin n)) :
    permAnnounceRightMulUnitary n π * permAnnounceProjector n perm *
        (permAnnounceRightMulUnitary n π)ᴴ = permAnnounceProjector n (perm * π) :=
  Equiv.Perm.permMatrix_conj_single (permAnnounceRightMulEquiv n π) perm

end QKD.BB84.Model
