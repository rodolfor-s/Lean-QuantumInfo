import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Relabelling local symmetric registers and regrouping three tensor components -/
namespace Quantum.Symmetry
open Matrix Quantum.Operators
variable {X Y A B E : Type*}

/-- Relabelling the local basis transports the symmetric projector sitewise. -/
theorem reindex_symmetricProjector [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (k : ℕ) :
    reindex (Equiv.piCongrRight fun _ : Fin k => e) (Equiv.piCongrRight fun _ : Fin k => e)
      (symmetricProjector X k) = symmetricProjector Y k := by
  let f := reindexLinearEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin k => e)
    (Equiv.piCongrRight fun _ : Fin k => e)
  change f ((1 / (k.factorial : ℂ)) • ∑ σ : Equiv.Perm (Fin k),
    permutationRepresentation (X := X) σ) = _
  rw [map_smul, map_sum]
  apply congrArg ((1 / (k.factorial : ℂ)) • ·)
  apply Finset.sum_congr rfl
  intro σ _
  exact reindex_tensorPermutation e σ

/-- Regroup three repeated components from `(A B) E` to `A (B E)`. -/
def regroupTriple (A B E : Type*) (k : ℕ) :
    ((Fin k → A × B) × (Fin k → E)) ≃ ((Fin k → A) × (Fin k → B × E)) :=
  (pairFunctions (A × B) E k).symm |>.trans
    ((Equiv.piCongrRight fun _ : Fin k => Equiv.prodAssoc A B E).trans
      (pairFunctions A (B × E) k))

/-- Regrouping three tensor components transports their simultaneous symmetric projector. -/
theorem reindex_pairedProjectorOf_regroupTriple
    [DecidableEq A] [DecidableEq B] [DecidableEq E] (k : ℕ) :
    reindex (regroupTriple A B E k) (regroupTriple A B E k)
      (pairedProjectorOf (A × B) E k) = pairedProjectorOf A (B × E) k := by
  change reindex (pairFunctions A (B × E) k) (pairFunctions A (B × E) k)
    (reindex (Equiv.piCongrRight fun _ : Fin k => Equiv.prodAssoc A B E)
      (Equiv.piCongrRight fun _ : Fin k => Equiv.prodAssoc A B E)
      (symmetricProjector ((A × B) × E) k)) = _
  rw [reindex_symmetricProjector]
  rfl

/-- The Alice marginal is unchanged by regrouping Bob and the environment. -/
theorem partialTraceRight_regroupTriple [Fintype B] [Fintype E] (k : ℕ)
    (M : Op ((Fin k → A × B) × (Fin k → E))) :
    partialTraceRight (reindex (regroupTriple A B E k) (regroupTriple A B E k) M) =
      partialTraceRight (reindex (pairFunctions A B k) (pairFunctions A B k)
        (partialTraceRight M)) := by
  classical
  ext x y
  change (∑ r : Fin k → B × E, M ((fun t => (x t, (r t).1)), fun t => (r t).2)
    ((fun t => (y t, (r t).1)), fun t => (r t).2)) =
    ∑ b : Fin k → B, ∑ e : Fin k → E, M ((fun t => (x t, b t)), e)
      ((fun t => (y t, b t)), e)
  simpa only [Fintype.sum_prod_type, pairFunctions,
    Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk] using
    (Equiv.sum_comp (pairFunctions B E k) (fun p =>
    M ((fun t => (x t, p.1 t)), p.2) ((fun t => (y t, p.1 t)), p.2)))

end Quantum.Symmetry
