import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct

/-! # Product Kraus -/


open scoped Matrix BigOperators

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Reindexing a joint product along a system equality reindexes each party factor. -/
theorem famKraus_submatrix_cast {R S T : MultipartiteSystem P} (h : S = T)
    (K : ∀ i, Matrix (T.reg i) (R.reg i) ℂ) :
    (Matrix.piTensorProduct K).submatrix (Equiv.cast (congrArg MultipartiteSystem.total h)) id =
      Matrix.piTensorProduct (fun i => (K i).submatrix (Equiv.cast (congrArg (fun U => U.reg i) h))
        id) := by
  subst T
  rfl

/-- The local matrix family with `M` at the actor and identities at all spectators. -/
def MultipartiteSystem.localFam (R : MultipartiteSystem P) (i : P) (HH : Type)
    [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) (j : P) : Matrix ((R.set i HH).reg j) (R.reg j) ℂ :=
  if hj : j = i then
    M.submatrix (Equiv.cast ((congrArg (R.set i HH).reg hj).trans (R.set_reg_self i
      HH)))
      (Equiv.cast (congrArg R.reg hj))
  else
    (1 : Matrix (R.reg j) (R.reg j) ℂ).submatrix
      (Equiv.cast (R.set_reg_of_ne i HH hj)) id

/-- The local family at its actor is the supplied matrix with its output index transported. -/
@[simp] theorem MultipartiteSystem.localFam_apply_self (R : MultipartiteSystem P) (i : P)
    (HH : Type) [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) (a : (R.set i HH).reg i) (b : R.reg i) :
    R.localFam i HH M i a b = M (cast (R.set_reg_self i HH) a) b := by
  simp [MultipartiteSystem.localFam]

/-- The local family is the transported identity at every spectator. -/
theorem MultipartiteSystem.localFam_apply_of_ne (R : MultipartiteSystem P) (i : P)
    (HH : Type) [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) {j : P} (hj : j ≠ i)
    (a : (R.set i HH).reg j) (b : R.reg j) :
    R.localFam i HH M j a b = if cast (R.set_reg_of_ne i HH hj) a = b then 1 else 0 := by
  simp only [MultipartiteSystem.localFam, dite_eq_right hj]
  rfl

/-- Componentwise coordinates for splitting off one party. -/
theorem MultipartiteSystem.splitAt_apply (R : MultipartiteSystem P) (i : P) (b : R.total) :
    R.splitAt i b = (b i, fun j : {j // j ≠ i} => b j) :=
  rfl

/-- A lifted local Kraus matrix is the product matrix with the local action at its actor and
identity factors at every spectator.

This is the single-node product-operator property used in the finite LOCC instrument tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
theorem localKrausLift_eq_famKraus (R : MultipartiteSystem P) (i : P) (HH : Type)
    [Fintype HH] [DecidableEq HH] (M : Matrix HH (R.reg i) ℂ) :
    localKrausLift R i HH M = Matrix.piTensorProduct (R.localFam i HH M) := by
  ext a b
  have hL : localKrausLift R i HH M a b =
      M (cast (R.set_reg_self i HH) (a i)) (b i) *
        (1 : Matrix (R.rest i) (R.rest i) ℂ)
          (fun j => cast (R.set_reg_of_ne i HH j.2) (a j)) (fun j => b j) := by
    simp only [localKrausLift, Matrix.submatrix_apply, Matrix.kroneckerMap, Matrix.of_apply,
      MultipartiteSystem.splitAt_apply, MultipartiteSystem.splitAtSet_apply]
  rw [hL]
  simp only [Matrix.piTensorProduct, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), R.localFam_apply_self]
  congr 1
  by_cases hfg : (fun j : {j // j ≠ i} => cast (R.set_reg_of_ne i HH j.2) (a j)) =
      (fun j : {j // j ≠ i} => b j)
  · rw [hfg, Matrix.one_apply_eq]
    refine (Finset.prod_eq_one fun j hj => ?_).symm
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [R.localFam_apply_of_ne _ _ _ hji, ite_eq_left (congrFun hfg ⟨j, hji⟩)]
  · rw [Matrix.one_apply_ne hfg]
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hfg
    refine (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨j0.2, Finset.mem_univ _⟩) ?_).symm
    rw [R.localFam_apply_of_ne _ _ _ j0.2, ite_eq_right hj0]

/-- Every lifted Kraus matrix of an announced local action is a party-product matrix. -/
theorem AnnouncedAction.liftedKraus_eq_famKraus {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y)
    (o : A.Outcome) (r : A.krausIndex o) :
    A.liftedKraus o r =
      Matrix.piTensorProduct (R.localFam A.actor (A.Output (A.announce o)) (A.kraus o r)) := by
  exact localKrausLift_eq_famKraus R A.actor (A.Output (A.announce o)) (A.kraus o r)

/-- Every lifted Kraus matrix of a private local action is a party-product matrix. -/
theorem PrivateAction.liftedKraus_eq_famKraus {R : MultipartiteSystem P} (A : PrivateAction R)
    (o : A.Outcome) (r : A.instrument.krausIndex o) :
    A.liftedKraus o r =
      Matrix.piTensorProduct (R.localFam A.actor A.Output (A.instrument.kraus o r)) := by
  exact localKrausLift_eq_famKraus R A.actor A.Output (A.instrument.kraus o r)

end LOCC
