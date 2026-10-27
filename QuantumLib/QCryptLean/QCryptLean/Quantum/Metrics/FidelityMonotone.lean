import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceDuality
import QCryptLean.Quantum.Metrics.Uhlmann
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Native fidelity monotonicity under discarding a register

Purifications are regrouped on product types. The overlap bound uses rectangular
polar factors and does not enumerate either the system or the environment.
-/

noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators

variable {X R : Type*} [Fintype X] [Fintype R]

/-- Discarding a finite environment increases the fidelity of positive operators. -/
theorem fidelity_le_partialTraceRight [Nonempty X]
    (A B : PosSemidefOp (X × R)) :
    fidelity A B ≤ fidelity A.partialTraceRight B.partialTraceRight := by
  obtain ⟨w, hw, ho⟩ := exists_purification_overlap_re_eq_fidelity A B
  let v' : Ket (X × (R × (X × R))) := ⟨fun p => A.purificationKet.vec ((p.1, p.2.1), p.2.2)⟩
  let w' : Ket (X × (R × (X × R))) := ⟨fun p => w.vec ((p.1, p.2.1), p.2.2)⟩
  have hm (v : Ket ((X × R) × (X × R))) :
      partialTraceRight (⟨fun p : X × (R × (X × R)) =>
        v.vec ((p.1, p.2.1), p.2.2)⟩ : Ket _).projector =
        partialTraceRight (partialTraceRight v.projector) := by
    ext i j
    exact Fintype.sum_prod_type _
  have hv' : partialTraceRight v'.projector = A.partialTraceRight.val := by
    rw [hm, A.partialTraceRight_purificationKet]
    rfl
  have hw' : partialTraceRight w'.projector = B.partialTraceRight.val := by
    rw [hm, hw]
    rfl
  have hi : (v'.dag * w' : ℂ) = (A.purificationKet.dag * w : ℂ) := by
    change (∑ p : X × (R × (X × R)),
      star (A.purificationKet.vec ((p.1, p.2.1), p.2.2)) * w.vec ((p.1, p.2.1), p.2.2)) = _
    change _ = ∑ p : (X × R) × (X × R), star (A.purificationKet.vec p) * w.vec p
    simp only [Fintype.sum_prod_type]
  calc
    fidelity A B = (v'.dag * w' : ℂ).re := by rw [hi, ho]
    _ ≤ ‖(v'.dag * w' : ℂ)‖ := Complex.re_le_norm _
    _ ≤ fidelity A.partialTraceRight B.partialTraceRight :=
      norm_overlap_le_fidelity A.partialTraceRight B.partialTraceRight v' w' hv' hw'

end Quantum.Metrics
