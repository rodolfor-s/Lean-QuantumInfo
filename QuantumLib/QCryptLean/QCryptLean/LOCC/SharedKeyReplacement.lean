import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Shared Key Replacement -/


open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators

open Matrix

open Quantum.Operators (Op)

namespace LOCC.SharedKeyReplacement

/-- The amplitude of each branch of uniform shared-key replacement. -/
noncomputable def weight (K : Type) [Fintype K] : ℂ :=
  (((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℝ) : ℂ)

private theorem weight_mul_self (K : Type) [Fintype K] [Nonempty K] :
    weight K * weight K = (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [weight, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]

@[simp] private theorem star_weight (K : Type) [Fintype K] :
    star (weight K) = weight K := by
  simp [weight]

variable {K R : Type} [Fintype K] [DecidableEq K] [DecidableEq R]

/-- One shared-key-replacement Kraus matrix.

The index is `(fresh, oldAlice, oldBob)`. The output keys are both `fresh`, the two input keys
are discarded, and the residual coordinate is copied unchanged. -/
noncomputable def kraus
    (r : K × K × K) : Op (K × K × R) :=
  weight K • Matrix.of fun out input =>
    if out.1 = r.1 ∧ out.2.1 = r.1 ∧ input.1 = r.2.1 ∧
        input.2.1 = r.2.2 ∧ out.2.2 = input.2.2 then 1 else 0

/-- Exact support and normalization of one replacement Kraus matrix. -/
@[simp] theorem kraus_apply
    (r : K × K × K) (out input : K × K × R) :
    kraus (R := R) r out input =
      weight K * if out.1 = r.1 ∧ out.2.1 = r.1 ∧ input.1 = r.2.1 ∧
          input.2.1 = r.2.2 ∧ out.2.2 = input.2.2 then 1 else 0 := by
  simp [kraus]

section

variable [Nonempty K] [Fintype R]

/-- Coordinate formula for the Gram matrix of one replacement Kraus operator. -/
theorem kraus_conjTranspose_mul_self_apply
    (fresh oldAlice oldBob : K)
    (i j : K × K × R) :
    ((kraus (R := R) (fresh, oldAlice, oldBob))ᴴ *
        kraus (R := R) (fresh, oldAlice, oldBob)) i j =
      if i.1 = oldAlice ∧ i.2.1 = oldBob ∧ j.1 = oldAlice ∧ j.2.1 = oldBob ∧
          i.2.2 = j.2.2
      then (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : i.1 = oldAlice ∧ i.2.1 = oldBob ∧ j.1 = oldAlice ∧
      j.2.1 = oldBob ∧ i.2.2 = j.2.2
  · rw [ite_eq_left h]
    let out : K × K × R := (fresh, fresh, i.2.2)
    rw [Finset.sum_eq_single out]
    · simpa [out, kraus, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
          h.2.2.2.2] using weight_mul_self K
    · intro other _ hne
      have hzero : kraus (R := R) (fresh, oldAlice, oldBob) other i = 0 := by
        simp only [kraus, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        by_cases ho : other.1 = fresh ∧ other.2.1 = fresh ∧ i.1 = oldAlice ∧
            i.2.1 = oldBob ∧ other.2.2 = i.2.2
        · exfalso
          apply hne
          apply Prod.ext ho.1
          exact Prod.ext ho.2.1 ho.2.2.2.2
        · simp [ho]
      rw [Matrix.conjTranspose_apply, hzero, star_zero, zero_mul]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro out _
    simp only [Matrix.conjTranspose_apply, kraus, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    split_ifs with hi hj
    · exfalso
      apply h
      rcases hi with ⟨_, _, hiA, hiB, hiR⟩
      rcases hj with ⟨_, _, hjA, hjB, hjR⟩
      exact ⟨hiA, hiB, hjA, hjB, hiR.symm.trans hjR⟩
    all_goals simp

/-- The replacement Kraus family is complete.

This is the trace-preservation criterion from
arXiv:1504.00233, `prelim.tex:879-894`; the sum over fresh keys cancels the squared
`1 / sqrt (card K)` normalization. -/
theorem kraus_complete :
    ∑ r : K × K × K, (kraus (R := R) r)ᴴ * kraus (R := R) r = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [kraus_conjTranspose_mul_self_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply, ite_eq_left rfl]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_eq_single i.1]
    · rw [Finset.sum_eq_single i.2.1]
      · simp
      · intro oldBob _ hne
        have hne' : i.2.1 ≠ oldBob := fun h => hne h.symm
        simp [hne']
      · simp
    · intro oldAlice _ hne
      have hne' : i.1 ≠ oldAlice := fun h => hne h.symm
      simp [hne']
    · simp
  · rw [Matrix.one_apply, ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro fresh _
    apply Finset.sum_eq_zero
    intro oldAlice _
    apply Finset.sum_eq_zero
    intro oldBob _
    rw [ite_eq_right]
    intro h
    apply hij
    exact Prod.ext (h.1.trans h.2.2.1.symm)
      (Prod.ext (h.2.1.trans h.2.2.2.1.symm) h.2.2.2.2)

omit [Nonempty K] [Fintype R] in
/-- The rows of one replacement Kraus matrix: a row with both output keys `fresh` reads the old
keys `(oldAlice, oldBob)` and copies the residual, with amplitude `weight K`; every other row
vanishes. -/
private theorem kraus_row
    (fresh oldAlice oldBob a b : K) (u : R) :
    kraus (R := R) (fresh, oldAlice, oldBob) (a, b, u) =
      if a = fresh ∧ b = fresh then Pi.single (oldAlice, oldBob, u) (weight K) else 0 := by
  funext input
  rw [kraus_apply]
  by_cases hab : a = fresh ∧ b = fresh
  · rw [ite_eq_left hab, Pi.single_apply, mul_ite, mul_one, mul_zero]
    refine if_congr ?_ rfl rfl
    obtain ⟨x, y, w⟩ := input
    simp only [hab, Prod.mk.injEq, true_and, eq_comm (a := u)]
  · rw [ite_eq_right hab, ite_eq_right fun h => hab ⟨h.1, h.2.1⟩, mul_zero, Pi.zero_apply]

/-- One replacement Kraus sandwich in explicit key and residual coordinates. -/
theorem kraus_sandwich_apply
    (rho : Op (K × K × R)) (fresh oldAlice oldBob a b a' b' : K) (u v : R) :
    (kraus (R := R) (fresh, oldAlice, oldBob) * rho *
        (kraus (R := R) (fresh, oldAlice, oldBob))ᴴ)
        (a, b, u) (a', b', v) =
      if a = fresh ∧ b = fresh ∧ a' = fresh ∧ b' = fresh then
        (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) *
          rho (oldAlice, oldBob, u) (oldAlice, oldBob, v)
      else 0 := by
  change Matrix.conjLinearMap (kraus (R := R) (fresh, oldAlice, oldBob)) rho (a, b, u) (a', b', v) =
    _
  by_cases h : a = fresh ∧ b = fresh ∧ a' = fresh ∧ b' = fresh
  · -- Both rows are fresh-key rows: the entry is `weight² · ρ`.
    rw [ite_eq_left h, Matrix.conjLinearMap_apply_of_row_eq_single _ _
      ((kraus_row _ _ _ _ _ u).trans (ite_eq_left ⟨h.1, h.2.1⟩))
      ((kraus_row _ _ _ _ _ v).trans (ite_eq_left h.2.2)), star_weight, mul_right_comm,
      weight_mul_self]
  · rw [ite_eq_right h]
    by_cases hrow : a = fresh ∧ b = fresh
    · -- The column row is not a fresh-key row, so it vanishes.
      exact Matrix.conjLinearMap_apply_eq_zero_of_row_right _ _ _
        ((kraus_row _ _ _ _ _ v).trans (ite_eq_right fun hcol => h ⟨hrow.1, hrow.2, hcol⟩))
    · exact Matrix.conjLinearMap_apply_eq_zero_of_row_left _ _
        ((kraus_row _ _ _ _ _ u).trans (ite_eq_right hrow)) _

variable (K R)

/-- Shared-key replacement as a one-outcome finite Kraus instrument. -/
noncomputable def instrument : Instrument (K × K × R) (K × K × R) Unit where
  krausIndex _ := K × K × K
  kraus _ := kraus
  complete := by simpa only [Fintype.sum_unique] using (kraus_complete (K := K) (R := R))

/-- The uniform shared-key-replacement channel. -/
noncomputable def channel :
    Op (K × K × R) →ₗ[ℂ] Op (K × K × R) :=
  (instrument K R).channel

/-- The channel is the sum of conjugations by the replacement Kraus family. -/
theorem channel_eq_kraus_sum :
    channel K R = ∑ r : K × K × K, Matrix.conjLinearMap (kraus (R := R) r) := by
  simp only [channel, instrument, Instrument.channel_eq_sum, Instrument.operation,
    krausMap_eq_sum_conjLinearMap,
    Fintype.sum_unique]

/-- Exact coordinate action of uniform shared-key replacement.

The output has one classical shared key, both old keys are traced out with the same values in bra
and ket, and every residual coherence is preserved. -/
theorem channel_apply
    (rho : Op (K × K × R))
    (a b a' b' : K) (u v : R) :
    channel K R rho (a, b, u) (a', b', v) =
      if a = b ∧ a' = b' ∧ a = a' then
        (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ oldAlice, ∑ oldBob,
            rho (oldAlice, oldBob, u) (oldAlice, oldBob, v)
      else 0 := by
  rw [channel_eq_kraus_sum]
  simp only [LinearMap.sum_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [kraus_sandwich_apply]
  by_cases h : a = b ∧ a' = b' ∧ a = a'
  · rcases h with ⟨rfl, rfl, rfl⟩
    rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
    simp only [and_self]
    rw [Finset.sum_eq_single a]
    · simp [Finset.mul_sum]
    · intro fresh _ hne
      have hne' : a ≠ fresh := fun h => hne h.symm
      simp [hne']
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro fresh _
    apply Finset.sum_eq_zero
    intro oldAlice _
    apply Finset.sum_eq_zero
    intro oldBob _
    rw [ite_eq_right]
    intro hf
    exact h ⟨hf.1.trans hf.2.1.symm, hf.2.2.1.trans hf.2.2.2.symm,
      hf.1.trans hf.2.2.1.symm⟩

end

end LOCC.SharedKeyReplacement
