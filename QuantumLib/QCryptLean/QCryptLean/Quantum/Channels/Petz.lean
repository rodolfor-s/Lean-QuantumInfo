import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Purification

/-! # Petz -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]

/-- The partial-trace Petz map, with the reference marginal supplied explicitly. -/
def petzTranspose (ρ : Op (X × R)) (σ : Op X) : Operation X (X × R) where
  toFun A := CFC.sqrt ρ * ((CFC.sqrt σ⁻¹ * A * CFC.sqrt σ⁻¹) ⊗ₖ (1 : Op R)) * CFC.sqrt ρ
  map_add' A B := by
    simp only [mul_add, add_mul, add_kronecker]
  map_smul' c A := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_kronecker, RingHom.id_apply]

/-- Nonlinear marginal transport by the square root of the requested marginal. -/
def marginalTransport (ρ : Op (X × R)) (σ : Op X) (W : UnitaryOp X) (A : Op X) :
    Op (X × R) :=
  let V := (CFC.sqrt A * W.val * CFC.sqrt σ⁻¹) ⊗ₖ (1 : Op R)
  V * ρ * Vᴴ

/-- Marginal transport preserves positivity of the reference. -/
theorem posSemidef_marginalTransport {ρ : Op (X × R)} (hρ : ρ.PosSemidef)
    (σ : Op X) (W : UnitaryOp X) (A : Op X) : (marginalTransport ρ σ W A).PosSemidef :=
  hρ.mul_mul_conjTranspose_same _

/-- The Petz sandwich is positive on positive inputs. -/
theorem posSemidef_petzTranspose (ρ : Op (X × R)) (σ : Op X) {A : Op X}
    (hA : A.PosSemidef) : (petzTranspose ρ σ A).PosSemidef := by
  have hσ : (CFC.sqrt σ⁻¹).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ⁻¹)).isHermitian
  have hρ : (CFC.sqrt ρ).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian
  change (CFC.sqrt ρ * ((CFC.sqrt σ⁻¹ * A * CFC.sqrt σ⁻¹) ⊗ₖ 1) * CFC.sqrt ρ).PosSemidef
  simpa only [hσ.eq, hρ.eq] using
    (((hA.conjTranspose_mul_mul_same (CFC.sqrt σ⁻¹)).kronecker
      (Matrix.PosSemidef.one (n := R))).conjTranspose_mul_mul_same (CFC.sqrt ρ))

end Quantum.Channels
