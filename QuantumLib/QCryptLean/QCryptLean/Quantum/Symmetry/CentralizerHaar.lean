import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.JointAction
import QCryptLean.Quantum.Symmetry.LocalCommutantTwirl

/-! # Centralizer Haar -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators MeasureTheory

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G]

/-- The unitary operators commuting with a representation form a subgroup. -/
def unitaryCentralizer (ρ : G →* Op X) : Subgroup (Matrix.unitaryGroup X ℂ) where
  carrier := {U | ∀ g, Commute (ρ g) (U : Op X)}
  one_mem' := fun _ => Commute.one_right _
  mul_mem' hU hV g := (hU g).mul_right (hV g)
  inv_mem' {U} hU g := (hU g).units_inv_right (u := Unitary.toUnits U)

/-- The unitary centralizer is closed in the ordinary matrix topology. -/
theorem isClosed_unitaryCentralizer (ρ : G →* Op X) :
    IsClosed (unitaryCentralizer ρ : Set (Matrix.unitaryGroup X ℂ)) := by
  change IsClosed (Set.ofPred fun U : Matrix.unitaryGroup X ℂ => ∀ g,
    ρ g * (U : Op X) = (U : Op X) * ρ g)
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.matrix_mul continuous_subtype_val)
      (continuous_subtype_val.matrix_mul continuous_const)

/-- A closed subgroup of the finite unitary group is compact. -/
instance unitaryCentralizer_compactSpace (ρ : G →* Op X) : CompactSpace (unitaryCentralizer ρ) :=
  isCompact_iff_compactSpace.mp (isClosed_unitaryCentralizer ρ).isCompact

/-- Probability Haar measure on the actual centralizer subgroup. -/
def unitaryCentralizerHaar (ρ : G →* Op X) : Measure (unitaryCentralizer ρ) :=
  ((Measure.haar : Measure (unitaryCentralizer ρ)) Set.univ)⁻¹ • Measure.haar

/-- The normalized centralizer Haar measure has total mass one. -/
instance isProbabilityMeasure_unitaryCentralizerHaar (ρ : G →* Op X) :
    IsProbabilityMeasure (unitaryCentralizerHaar ρ) := by
  constructor
  simp only [unitaryCentralizerHaar, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.IsOpenPosMeasure.open_pos _ isOpen_univ Set.univ_nonempty)
    (ne_of_lt (IsCompact.measure_lt_top isCompact_univ))

/-- Normalization retains Haar left invariance. -/
instance isMulLeftInvariant_unitaryCentralizerHaar (ρ : G →* Op X) :
    (unitaryCentralizerHaar ρ).IsMulLeftInvariant := by
  unfold unitaryCentralizerHaar
  infer_instance

/-- The centralizer acts unitarily on each function-register tensor power. -/
def unitaryCentralizerTensorPower (ρ : G →* Op X) (k : ℕ) :
    unitaryCentralizer ρ →* Matrix.unitaryGroup (Fin k → X) ℂ where
  toFun U := ⟨Op.tensorPow U.val.val k, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (piTensorProduct (fun _ => U.val.val))ᴴ * piTensorProduct (fun _ => U.val.val) = 1
    rw [conjTranspose_piTensorProduct, piTensorProduct_mul]
    have hU : U.val.valᴴ * U.val.val = 1 := (mem_unitaryGroup_iff').mp U.val.property
    simp only [hU, piTensorProduct_one]⟩
  map_one' := Subtype.ext (by exact piTensorProduct_one)
  map_mul' U V := Subtype.ext (by exact (piTensorProduct_mul _ _).symm)

/-- Tensor-power centralizer actions are continuous in every matrix entry. -/
theorem continuous_unitaryCentralizerTensorPower (ρ : G →* Op X) (k : ℕ) :
    Continuous (unitaryCentralizerTensorPower ρ k) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun U : unitaryCentralizer ρ => ∏ t : Fin k, U.val.val (i t) (j t))
  exact continuous_finsetProd _ fun t _ =>
    (continuous_apply (j t)).comp ((continuous_apply (i t)).comp
      ((continuous_subtype_val : Continuous
        (Subtype.val : Matrix.unitaryGroup X ℂ → Op X)).comp
        (continuous_subtype_val : Continuous
          (Subtype.val : unitaryCentralizer ρ → Matrix.unitaryGroup X ℂ))))

end Quantum.Symmetry
