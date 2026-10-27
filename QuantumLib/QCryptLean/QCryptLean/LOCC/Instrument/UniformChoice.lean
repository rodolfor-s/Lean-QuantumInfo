import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.KrausAlgebra

/-! # Uniform Choice -/


open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators
open Matrix

open Quantum.Operators (Op)

namespace LOCC
namespace Instrument

variable {A B R Y : Type} [Fintype R]

/-- The Kraus-amplitude normalization for a uniform choice from `R`. -/
noncomputable def uniformChoiceScale : ℂ :=
  (1 : ℂ) / (Real.sqrt (Fintype.card R : ℝ) : ℂ)

/-- Squaring the uniform Kraus amplitude gives the probability `1 / |R|`.

The `Nonempty R` hypothesis is exactly what makes the finite cardinality in the denominator
nonzero. -/
theorem uniformChoiceScale_star_mul [Nonempty R] :
    star (uniformChoiceScale (R := R)) * uniformChoiceScale (R := R) =
      (Fintype.card R : ℂ)⁻¹ := by
  have hcard : 0 < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [uniformChoiceScale, star_div₀, star_one]
  rw [show star ((Real.sqrt (Fintype.card R : ℝ) : ℂ)) =
      (Real.sqrt (Fintype.card R : ℝ) : ℂ) by
        rw [Complex.star_def, Complex.conj_ofReal]]
  rw [one_div, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hcard.le]
  congr 2

section

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype Y]

/-- The explicit Kraus matrix for observed branch `(r, y)` and hidden Kraus index `t`.

It is the corresponding Kraus matrix of `I r`, scaled by the square root of the uniform
probability on `R`. -/
noncomputable def uniformChoiceKraus
    (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) : Matrix B A ℂ :=
  uniformChoiceScale (R := R) • (I r).kraus y t

variable [Nonempty R]

/-- The uniformly scaled dependent Kraus family is complete.

For each fixed seed `r`, this uses the completeness certificate of `I r`; summing the identical
identity contribution with weight `1 / |R|` over the nonempty finite type `R` gives the identity.
This is the trace-preserving normalization required of the finite instrument mixture in
arXiv:1210.4583, Section 2. -/
theorem uniformChoiceKraus_complete
    (I : R → Instrument A B Y) :
    ∑ ry : R × Y, ∑ t : (I ry.1).krausIndex ry.2,
        (uniformChoiceKraus I ry.1 ry.2 t)ᴴ *
          uniformChoiceKraus I ry.1 ry.2 t =
      1 := by
  classical
  have hscaled : ∀ (r : R) (y : Y) (t : (I r).krausIndex y),
      (uniformChoiceKraus I r y t)ᴴ * uniformChoiceKraus I r y t =
        ((Fintype.card R : ℂ)⁻¹ • ((I r).kraus y t)ᴴ) *
          (I r).kraus y t := by
    intro r y t
    rw [uniformChoiceKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, uniformChoiceScale_star_mul,
      Matrix.smul_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [hscaled, Matrix.smul_mul, ← Finset.smul_sum]
  simp_rw [(I _).complete]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  simp [Fintype.card_ne_zero]

/-- Choose a seed uniformly, run the corresponding certified instrument, and retain the seed
together with its observed local outcome as the instrument outcome.

The outcome type is `R × Y`; the hidden fibre at `(r, y)` is `(I r).krausIndex y`. Publication
is a separate choice made by the announcement function of an enclosing `AnnouncedAction`; no
hidden Kraus representative is exposed in either case. -/
noncomputable def uniformChoice
    (I : R → Instrument A B Y) : Instrument A B (R × Y) where
  krausIndex ry := (I ry.1).krausIndex ry.2
  kraus ry t := uniformChoiceKraus I ry.1 ry.2 t
  complete := uniformChoiceKraus_complete I

/-- The certified uniform-choice instrument exposes exactly its explicitly scaled Kraus matrix. -/
@[simp] theorem uniformChoice_kraus
    (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) :
    (uniformChoice I).kraus (r, y) t = uniformChoiceKraus I r y t := by
  rfl

/-- Exact CP operation at the observed branch `(r, y)`.

The equality holds as linear maps on all operators: a fixed branch is the operation of `I r` at
`y`, multiplied by the uniform probability `1 / |R|`. -/
theorem uniformChoice_operation
    (I : R → Instrument A B Y) (r : R) (y : Y) :
    (uniformChoice I).operation (r, y) =
      (Fintype.card R : ℂ)⁻¹ • (I r).operation y := by
  simp only [Instrument.operation, krausMap_eq_sum_conjLinearMap]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply LinearMap.ext
  intro rho
  ext b b'
  simp only [uniformChoice, uniformChoiceKraus, Matrix.conjLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [uniformChoiceScale_star_mul]

/-- The total channel is the uniform average of the channels in the supplied family.

The observed pair `(r, y)` is summed out in `Instrument.channel`; the instrument itself retains
that pair as its outcome. -/
theorem uniformChoice_channel
    (I : R → Instrument A B Y) :
    (uniformChoice I).channel =
      (Fintype.card R : ℂ)⁻¹ • ∑ r : R, (I r).channel := by
  simp only [Instrument.channel_eq_sum]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact uniformChoice_operation I r y

end

end Instrument

end LOCC

open scoped BigOperators Matrix
namespace LOCC.Instrument
variable (A R : Type) [Fintype A] [DecidableEq A] [Fintype R] [Nonempty R]

/-- Sample a uniform finite outcome while preserving the quantum register. -/
noncomputable def uniformSample : Instrument A A R :=
  Instrument.ofFine (fun _ => uniformChoiceScale (R := R) • (1 : Matrix A A ℂ)) (by
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [mul_comm (uniformChoiceScale (R := R)), uniformChoiceScale_star_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul])

/-- Each sampled outcome preserves every matrix entry with its uniform probability. -/
theorem uniformSample_operation (r : R) :
    (uniformSample A R).operation r = (Fintype.card R : ℂ)⁻¹ • LinearMap.id := by
  rw [operation, Quantum.Channels.krausMap_eq_sum_conjLinearMap]
  change (∑ _ : Unit, Matrix.conjLinearMap
    (uniformChoiceScale (R := R) • (1 : Matrix A A ℂ))) = _
  rw [Fintype.sum_unique]
  ext M a b
  simp only [Matrix.conjLinearMap_apply, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul, uniformChoiceScale_star_mul, LinearMap.smul_apply,
    LinearMap.id_apply]

end LOCC.Instrument
