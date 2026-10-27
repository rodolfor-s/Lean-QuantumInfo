import Mathlib.Probability.Distributions.Uniform
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.KrausAlgebra

/-!
# PMF-weighted finite choices of instruments

This module constructs the finite mixture of a family of certified quantum instruments using an
arbitrary probability mass function on the seed type. The observed outcome is the seed paired with
the member instrument's outcome, while the hidden Kraus fibre is unchanged.

The construction is the finite-instrument mixture described by
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. The operation and channel
formulas below specialize that mixture to finite PMF weights. No support, strict-positivity, or
inhabitance premise is imposed beyond the supplied PMF and certified instruments.
-/

open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC.Instrument

variable {A B R Y : Type}

/-- Kraus-amplitude scale associated with one PMF seed. -/
def weightedChoiceScale (p : PMF R) (r : R) : ℂ :=
  (Real.sqrt (p r).toReal : ℂ)

/-- Squaring the real nonnegative Kraus amplitude recovers the seed probability. -/
theorem weightedChoiceScale_star_mul (p : PMF R) (r : R) :
    star (weightedChoiceScale p r) * weightedChoiceScale p r =
      ((p r).toReal : ℂ) := by
  rw [weightedChoiceScale]
  rw [show star ((Real.sqrt (p r).toReal : ℂ)) =
      (Real.sqrt (p r).toReal : ℂ) by
        rw [Complex.star_def, Complex.conj_ofReal]]
  norm_cast
  exact Real.mul_self_sqrt ENNReal.toReal_nonneg

/-- The finite real seed weights sum to one after embedding in `ℂ`. -/
theorem weightedChoiceProbability_sum [Fintype R] (p : PMF R) :
    ∑ r : R, ((p r).toReal : ℂ) = 1 := by
  norm_cast
  rw [← ENNReal.toReal_sum (fun r _ => p.apply_ne_top r),
    ← tsum_fintype (L := SummationFilter.unconditional _), p.tsum_coe]
  simp

section

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype Y]

/-- The Kraus matrix in seed branch `r`, outcome `y`, and original hidden fibre `t`. -/
def weightedChoiceKraus
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) : Matrix B A ℂ :=
  weightedChoiceScale p r • (I r).kraus y t

variable [Fintype R]

/-- The PMF-scaled dependent Kraus family is complete.

For each seed, the member instrument supplies its own completeness certificate. The remaining
normalization is exactly `weightedChoiceProbability_sum`; zero-probability seeds contribute zero.
This is the finite-mixture completeness equation from arXiv:1210.4583, Section 2. -/
theorem weightedChoiceKraus_complete
    (p : PMF R) (I : R → Instrument A B Y) :
    ∑ ry : R × Y, ∑ t : (I ry.1).krausIndex ry.2,
        (weightedChoiceKraus p I ry.1 ry.2 t)ᴴ *
          weightedChoiceKraus p I ry.1 ry.2 t =
      1 := by
  have hscaled : ∀ (r : R) (y : Y) (t : (I r).krausIndex y),
      (weightedChoiceKraus p I r y t)ᴴ * weightedChoiceKraus p I r y t =
        (((p r).toReal : ℂ) • ((I r).kraus y t)ᴴ) * (I r).kraus y t := by
    intro r y t
    rw [weightedChoiceKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, weightedChoiceScale_star_mul,
      Matrix.smul_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [hscaled, Matrix.smul_mul, ← Finset.smul_sum]
  simp_rw [(I _).complete]
  rw [← Finset.sum_smul, weightedChoiceProbability_sum, one_smul]

/-- Choose a seed according to `p`, run its certified instrument, and retain `(seed, outcome)`.

The hidden fibre at `(r,y)` is definitionally the hidden fibre of `I r` at `y`; it is neither
coarse-grained nor exposed as an observed value. -/
def weightedChoice
    (p : PMF R) (I : R → Instrument A B Y) : Instrument A B (R × Y) where
  krausIndex ry := (I ry.1).krausIndex ry.2
  kraus ry t := weightedChoiceKraus p I ry.1 ry.2 t
  complete := weightedChoiceKraus_complete p I

/-- The weighted-choice instrument exposes exactly the explicitly scaled Kraus matrix. -/
@[simp] theorem weightedChoice_kraus
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) :
    (weightedChoice p I).kraus (r, y) t = weightedChoiceKraus p I r y t := by
  rfl

omit [Fintype R] in
/-- A zero-mass seed has the zero Kraus matrix in every observed and hidden branch. -/
@[simp] theorem weightedChoiceKraus_of_eq_zero
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) (hr : p r = 0) :
    weightedChoiceKraus p I r y t = 0 := by
  simp [weightedChoiceKraus, weightedChoiceScale, hr]

/-- Exact CP operation at an observed weighted branch.

This equality is between linear maps on all operators. It is the finite PMF-weighted branch
operation associated with the instrument mixture of arXiv:1210.4583, Section 2. -/
theorem weightedChoice_operation
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y) :
    (weightedChoice p I).operation (r, y) =
      ((p r).toReal : ℂ) • (I r).operation y := by
  simp only [Instrument.operation, krausMap_eq_sum_conjLinearMap]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply LinearMap.ext
  intro rho
  ext b b'
  simp only [weightedChoice, weightedChoiceKraus, Matrix.conjLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [weightedChoiceScale_star_mul]

/-- A zero-mass seed contributes the zero operation at every member outcome. -/
@[simp] theorem weightedChoice_operation_of_eq_zero
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y)
    (hr : p r = 0) :
    (weightedChoice p I).operation (r, y) = 0 := by
  rw [weightedChoice_operation]
  simp [hr]

/-- The total channel is the PMF-weighted sum of the member channels.

The paired observed outcome is summed out by `Instrument.channel`; the theorem makes no assertion
about publication of that outcome. -/
theorem weightedChoice_channel
    (p : PMF R) (I : R → Instrument A B Y) :
    (weightedChoice p I).channel =
      ∑ r : R, ((p r).toReal : ℂ) • (I r).channel := by
  simp only [Instrument.channel_eq_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact weightedChoice_operation p I r y

section

variable [Nonempty R]

/-- With the uniform PMF, weighted and existing uniform choice have equal branch operations.

This is operational compatibility only; it does not identify the two `Instrument` structures. -/
theorem weightedChoice_uniform_operation
    (I : R → Instrument A B Y) (r : R) (y : Y) :
    (weightedChoice (PMF.uniformOfFintype R) I).operation (r, y) =
      (uniformChoice I).operation (r, y) := by
  rw [weightedChoice_operation, uniformChoice_operation,
    PMF.uniformOfFintype_apply]
  simp

/-- With the uniform PMF, weighted and existing uniform choice have equal total channels.

This is channel compatibility only; no structural equality of instruments is claimed. -/
theorem weightedChoice_uniform_channel
    (I : R → Instrument A B Y) :
    (weightedChoice (PMF.uniformOfFintype R) I).channel =
      (uniformChoice I).channel := by
  rw [weightedChoice_channel, uniformChoice_channel]
  simp_rw [PMF.uniformOfFintype_apply]
  simp [← Finset.smul_sum]

/-! ## Definition-driven probes -/

end

/-- The weighted constructor preserves each member instrument's hidden Kraus fibre exactly. -/
theorem weightedChoice_krausIndex
    (p : PMF R) (I : R → Instrument A B Y) (r : R) (y : Y) :
    (weightedChoice p I).krausIndex (r, y) = (I r).krausIndex y := by
  rfl
end

end LOCC.Instrument
