import QCryptLean.InfoTheory.Postselection.FixedMarginalMoment
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.FixedMarginalProjection
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BipartiteCommutant
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.HaarFlatten
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Projected
import QCryptLean.Quantum.Symmetry.RegisterRegroup
import QCryptLean.Quantum.Symmetry.SymmetricMarginal

/-! # Native fixed-marginal domination of symmetric purifications -/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti
  Quantum.Symmetry Math.Combinatorics
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A] [Nonempty B] [Nonempty E]

/-- A symmetric purification with a faithful fixed marginal is dominated by the Haar reference. -/
theorem le_fixedMarginalReference (σA : DensityOp A) (hσA : σA.toOp.PosDef)
    (e : A ↪ B × E) (k : ℕ) (Ψ : DensityOp ((Fin k → A × B) × (Fin k → E)))
    (hsupp : pairedProjectorOf (A × B) E k * Ψ.toOp = Ψ.toOp)
    (hmarg : partialTraceRight (reindex (pairFunctions A B k) (pairFunctions A B k)
      (partialTraceRight Ψ.toOp)) = (σA.tensorPow k).toOp) :
    Ψ.toOp ≤ (deFinettiPrefactor (Fintype.card A * Fintype.card B * Fintype.card E) k : ℂ) •
      fixedMarginalReference σA e k := by
  let f := reindexAlgEquiv ℂ ℂ (regroupTriple A B E k)
  let P := pairedProjectorOf A (B × E) k
  have hP : P.PosSemidef := pairedProjectorOf_posSemidef _ _ _
  have hΨ : (f Ψ.toOp).PosSemidef := Ψ.posSemidef.reindex _
  have hs : P * f Ψ.toOp = f Ψ.toOp := by
    change pairedProjectorOf A (B × E) k * f Ψ.toOp = f Ψ.toOp
    rw [← reindex_pairedProjectorOf_regroupTriple k]
    change f _ * f _ = _
    rw [← map_mul, hsupp]
  have hm : partialTraceRight (f Ψ.toOp) = (σA.tensorPow k).toOp := by
    rw [show f Ψ.toOp = reindex (regroupTriple A B E k)
      (regroupTriple A B E k) Ψ.toOp from rfl, partialTraceRight_regroupTriple]
    exact hmarg
  have hM : (σA.tensorPow k).toOp.PosDef := PosDef.piTensorProduct (fun _ => hσA)
  have hMP : Commute ((σA.tensorPow k).toOp ⊗ₖ (1 : Op (Fin k → B × E))) P :=
    commute_kronecker_one_pairedProjectorOf _
      (fun σ => tensorPow_commute_permutationRepresentation σA.toOp σ)
  have hΩP : Commute (partialTraceRight P ⊗ₖ (1 : Op (Fin k → B × E))) P :=
    commute_kronecker_one_pairedProjectorOf _
      (fun σ => (permutationRepresentation_commute_partialTraceRight_pairedProjectorOf σ).symm)
  have h := hΨ.le_fixedMarginal_projection hM hP.isHermitian pairedProjectorOf_mul_self hs hm
    (posDef_partialTraceRight_pairedProjectorOf e) hMP hΩP
  have href : f (fixedMarginalReference σA e k) =
      (CFC.sqrt (σA.tensorPow k).toOp ⊗ₖ (1 : Op (Fin k → B × E))) *
        ((partialTraceRight P)⁻¹ ⊗ₖ (1 : Op (Fin k → B × E))) * P *
        (CFC.sqrt (σA.tensorPow k).toOp ⊗ₖ (1 : Op (Fin k → B × E)))ᴴ := by
    rw [show f (fixedMarginalReference σA e k) = reindex (regroupTriple A B E k)
      (regroupTriple A B E k) (fixedMarginalReference σA e k) from rfl,
      reindex_fixedMarginalReference, unitaryHaarAverage_embeddedMaxEntangled_eq e]
    simp only [P, Matrix.mul_assoc]
  have ht : P.trace.re =
      (deFinettiPrefactor (Fintype.card A * Fintype.card B * Fintype.card E) k : ℝ) := by
    change (reindex (pairFunctions A (B × E) k) (pairFunctions A (B × E) k)
      (symmetricProjector (A × (B × E)) k)).trace.re = _
    rw [reindex_trace, symmetricSubspace_dim]
    simp only [Fintype.card_prod, mul_assoc, deFinettiPrefactor]
  rw [← href, ht] at h
  apply Matrix.le_iff.mpr
  have hr := (Matrix.le_iff.mp h).reindex (regroupTriple A B E k).symm
  have he : reindex (regroupTriple A B E k).symm (regroupTriple A B E k).symm
      ((deFinettiPrefactor (Fintype.card A * Fintype.card B * Fintype.card E) k : ℂ) •
        f (fixedMarginalReference σA e k) - f Ψ.toOp) =
      (deFinettiPrefactor (Fintype.card A * Fintype.card B * Fintype.card E) k : ℂ) •
        fixedMarginalReference σA e k - Ψ.toOp := by
    ext i j
    simp only [f, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.smul_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  simp only [Complex.ofReal_natCast] at hr
  rw [he] at hr
  exact hr

end InfoTheory.Postselection
