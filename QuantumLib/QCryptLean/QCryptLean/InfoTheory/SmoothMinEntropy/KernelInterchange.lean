import QCryptLean.InfoTheory.Renyi.PetzTensor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Relabel
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Tensor marginals and structural interchange for announcement kernels -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped Kronecker

variable {C D F Q R S : Type*} [Fintype C] [Fintype D] [Fintype F]
  [Fintype Q] [Fintype R] [Fintype S]

/-- Quantum relabelling transports the complete classical marginal sum. -/
theorem CQState.quantumMarginal_reindex (ρ : CQState C Q) (e : Q ≃ R) :
    (ρ.reindex e).quantumMarginal = ρ.quantumMarginal.reindex e := by
  apply SubDensityOp.ext
  ext i j
  simp only [CQState.quantumMarginal, CQState.reindex, SubDensityOp.reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

/-- A bijection of classical labels leaves the quantum marginal unchanged. -/
theorem CQState.quantumMarginal_relabel (ρ : CQState C Q) (e : C ≃ D) :
    (ρ.relabel e).quantumMarginal = ρ.quantumMarginal := by
  apply SubDensityOp.ext
  exact Equiv.sum_comp e.symm (fun c => (ρ.stateMap c).toOp)

/-- Successive deterministic coarsenings compose as functions. -/
theorem CQState.coarsen_coarsen [DecidableEq D] [DecidableEq F]
    (ρ : CQState C Q) (f : C → D) (g : D → F) :
    (ρ.coarsen f).coarsen g = ρ.coarsen (g ∘ f) := by
  apply CQState.ext
  funext z
  apply SubDensityOp.ext
  change (∑ d, if g d = z then ∑ c, if f c = d then (ρ.stateMap c).toOp else 0 else 0) = _
  have hi (d : D) :
      (if g d = z then ∑ c, if f c = d then (ρ.stateMap c).toOp else 0 else 0) =
        ∑ c, if f c = d then if g d = z then (ρ.stateMap c).toOp else 0 else 0 := by
    by_cases h : g d = z <;> simp [h]
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- An equivalence of coarsened labels can be moved outside the coarsening. -/
theorem CQState.coarsen_eq_relabel_coarsen [DecidableEq D] [DecidableEq F]
    (e : D ≃ F) (g : C → D) (h : C → F) (he : ∀ c, e (g c) = h c)
    (ρ : CQState C Q) : ρ.coarsen g = (ρ.coarsen h).relabel e.symm := by
  ext d i j
  change (∑ c, if g c = d then (ρ.stateMap c).toOp else 0) i j =
    (∑ c, if h c = e d then (ρ.stateMap c).toOp else 0) i j
  simp only [← he, Equiv.apply_eq_iff_eq]

/-- Relabelling the quantum factor commutes with an untouched left kernel. -/
theorem CQState.reindex_tensorRightCongr_tensorLeftKernel
    (e : Q ≃ S) (ρ : CQState C Q) (K : C → SubDensityOp R) :
    (ρ.tensorLeftKernel K).reindex ((Equiv.refl R).prodCongr e) =
      (ρ.reindex e).tensorLeftKernel K := by
  ext c i j
  rfl

/-- Move a leading announcement past the two original factors. -/
def rotateAnnouncement (R Q S : Type*) : R × (Q × S) ≃ Q × (S × R) where
  toFun p := (p.2.1, p.2.2, p.1)
  invFun p := (p.2.2, p.1, p.2.1)

/-- Coarsening a product to its first label leaves one independent announced ancilla. -/
theorem reindex_coarsen_tensorLeftKernel_tensor [DecidableEq C]
    (ρ : CQState C Q) (σ : CQState D S) (K : D → SubDensityOp R) :
    (((ρ.tensor σ).tensorLeftKernel (fun p => K p.2)).coarsen Prod.fst).reindex
        (rotateAnnouncement R Q S) =
      ρ.tensorRightKernel (fun _ => (σ.tensorRightKernel K).quantumMarginal) := by
  ext c i j
  simp [CQState.reindex, SubDensityOp.reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, CQState.coarsen, CQState.ofBlocks,
    CQState.tensorLeftKernel, CQState.tensorRightKernel, CQState.tensor,
    CQState.quantumMarginal, SubDensityOp.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Fintype.sum_prod_type, rotateAnnouncement,
    Finset.mul_sum, mul_left_comm, mul_comm]

end InfoTheory.SmoothMinEntropy
