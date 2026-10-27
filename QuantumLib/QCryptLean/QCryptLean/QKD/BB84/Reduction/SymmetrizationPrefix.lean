import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.Quantum.Operators.Basic

/-!
# Local actions for the retained comparison experiment

Alice announces a uniformly sampled inner permutation and both parties apply its sift operators.
Bob retains the analytical model's singleton public cell. The retained comparison experiment
chains these actions before the same `classicalTail` used by the physical construction; that
tail's kernel reads the raw diagonal.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open LOCC QKD.BB84 Measurement
open LOCC.TwoParty
open QKD.BB84.FiniteKey

/-! ## Communicated uniform permutation -/

/-- The one-outcome instrument for one party's BB84 sift/permutation operator.

The matrix is the explicit `QKD.BB84.Model.siftPermHalf` operator. Its completeness proof is the
already-proved unitary law for that operator. The random choice is introduced separately below,
so this definition contains no shared-randomness input and no sampling scalar. -/
def siftPermutationInstrument
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    Instrument (Bits n) (Bits n) Unit :=
  Instrument.ofFine (fun _ => QKD.BB84.Model.siftPermHalf n peSel xSel π) (by
    simp only [Fintype.sum_unique, QKD.BB84.Model.siftPermHalf_unitary])

/-- Alice's uniform permutation instrument.

The observed physical outcome is `(π, ())`. The only randomness is the explicit finite-uniform
choice made by `Instrument.uniformChoice`; at a fixed `π` its operation has weight
`1 / Fintype.card (Equiv.Perm (Fin n))`. -/
noncomputable def alicePermutationInstrument
    (n : ℕ) (peSel xSel : Fin n → Bool) :
    Instrument (Bits n) (Bits n) (Equiv.Perm (Fin n) × Unit) :=
  Instrument.uniformChoice
    (fun π : Equiv.Perm (Fin n) => siftPermutationInstrument n peSel xSel π)

/-- Alice samples and applies her sift operator and announces the sampled permutation. -/
def alicePermutationAnnouncement
    (n : ℕ) (peSel xSel : Fin n → Bool) :
    AnnouncedAction (FinalStage.rawSystem n) (Equiv.Perm (Fin n)) :=
  AnnouncedAction.ofInstrument .alice (alicePermutationInstrument n peSel xSel) Prod.fst

/-- Bob applies the sift operator selected by Alice and announces the singleton cell. -/
def bobSiftUnitAnnouncement
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    AnnouncedAction (FinalStage.rawSystem n) Unit :=
  AnnouncedAction.ofInstrument .bob (siftPermutationInstrument n peSel xSel π) id

/-- Alice's action exposes exactly the sampled permutation to public control flow. -/
@[simp] theorem alicePermutationAnnouncement_announce
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (alicePermutationAnnouncement n peSel xSel).announce (π, ()) = π := by
  rfl

/-- Exact joint-register operation of Alice's uniformly sampled permutation branch.

The formula holds for every operator and independent output row and column coordinates. The local
lift tensors Alice's matrix with the spectator identity; no equality between Bob's row and column
coordinates is assumed. -/
theorem alicePermutationAnnouncement_liftedOperation_apply
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : ((alicePermutationAnnouncement n peSel xSel).out π).total) :
    ((alicePermutationAnnouncement n peSel xSel).liftedOperation (π, ()) rho) q q' =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
        (Matrix.conjLinearMap
          (localKrausLift (FinalStage.rawSystem n) .alice (Bits n)
            (QKD.BB84.Model.siftPermHalf n peSel xSel π)) rho) q q' := by
  change ((alicePermutationInstrument n peSel xSel).liftAt
    (FinalStage.rawSystem n) .alice).operation (π, ()) rho q q' = _
  refine (Instrument.liftAt_operation_apply (R := FinalStage.rawSystem n) .alice
    (alicePermutationInstrument n peSel xSel) (π, ()) rho q q').trans ?_
  unfold alicePermutationInstrument
  refine (congrFun (congrFun (LinearMap.congr_fun
    (Instrument.uniformChoice_operation (fun π => siftPermutationInstrument n peSel xSel π)
      π ()) _) _) _).trans ?_
  change (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
    (siftPermutationInstrument n peSel xSel π).operation () _ _ _ = _
  apply congrArg (fun z : ℂ => (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * z)
  calc
    _ = ((siftPermutationInstrument n peSel xSel π).liftAt
        (FinalStage.rawSystem n) .alice).operation () rho q q' :=
      (Instrument.liftAt_operation_apply .alice
        (siftPermutationInstrument n peSel xSel π) () rho q q').symm
    _ = _ := by
      let K := localKrausLift (FinalStage.rawSystem n) .alice (Bits n)
        (QKD.BB84.Model.siftPermHalf n peSel xSel π)
      change ((∑ _ : Unit, Matrix.conjLinearMap K) rho) q q' = _
      rw [Fintype.sum_unique]

/-- Bob's action contributes exactly the unique public value. -/
@[simp] theorem bobSiftUnitAnnouncement_announce
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (bobSiftUnitAnnouncement n peSel xSel π).announce () = () := by
  rfl

/-- Exact joint-register operation of Bob's sift/permutation branch.

The formula holds for every operator and independent output row and column coordinates. Bob's
local lift acts as the identity on Alice's two independent spectator coordinates. -/
theorem bobSiftUnitAnnouncement_liftedOperation_apply
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : ((bobSiftUnitAnnouncement n peSel xSel π).out ()).total) :
    ((bobSiftUnitAnnouncement n peSel xSel π).liftedOperation () rho) q q' =
      (Matrix.conjLinearMap
        (localKrausLift (FinalStage.rawSystem n) .bob (Bits n)
          (QKD.BB84.Model.siftPermHalf n peSel xSel π)) rho) q q' := by
  change ((siftPermutationInstrument n peSel xSel π).liftAt
    (FinalStage.rawSystem n) .bob).operation () rho q q' = _
  let K := localKrausLift (FinalStage.rawSystem n) .bob
    (Bits n) (QKD.BB84.Model.siftPermHalf n peSel xSel π)
  change ((∑ _ : Unit, Matrix.conjLinearMap K) rho) q q' = _
  rw [Fintype.sum_unique]

end QKD.BB84.Reduction
