import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.Instrument.OnFactor
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.Math.FiniteEmbedding
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-! # Selected Marginal -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

/-- Split a bit string into its values on an embedding and on the increasingly enumerated
complement of that embedding. -/
def selectedBitSplit {n N : ℕ} (f : Fin n ↪ Fin N) :
    (Fin N → Bit) ≃ (Fin n → Bit) × (Fin (N - n) → Bit) where
  toFun x :=
    (fun i => x (f i),
      fun j => x (Math.FiniteEmbedding.embeddingComplementEquiv f j))
  invFun q := fun i =>
    Sum.elim q.1 q.2 ((Math.FiniteEmbedding.embeddingSplitEquiv f).symm i)
  left_inv x := by
    funext i
    obtain ⟨s, rfl⟩ := (Math.FiniteEmbedding.embeddingSplitEquiv f).surjective i
    cases s with
    | inl k =>
        change Sum.elim (fun i => x (f i))
          (fun j => x (Math.FiniteEmbedding.embeddingComplementEquiv f j))
            ((Math.FiniteEmbedding.embeddingSplitEquiv f).symm
              (Math.FiniteEmbedding.embeddingSplitEquiv f (Sum.inl k))) =
          x (Math.FiniteEmbedding.embeddingSplitEquiv f (Sum.inl k))
        rw [Equiv.symm_apply_apply]
        exact congrArg x
          (Math.FiniteEmbedding.embeddingSplitEquiv_apply_range f k).symm
    | inr k =>
        change Sum.elim (fun i => x (f i))
          (fun j => x (Math.FiniteEmbedding.embeddingComplementEquiv f j))
            ((Math.FiniteEmbedding.embeddingSplitEquiv f).symm
              (Math.FiniteEmbedding.embeddingSplitEquiv f (Sum.inr k))) =
          x (Math.FiniteEmbedding.embeddingSplitEquiv f (Sum.inr k))
        rw [Equiv.symm_apply_apply]
        exact congrArg x
          (Math.FiniteEmbedding.embeddingSplitEquiv_apply_complement f k).symm
  right_inv q := by
    apply Prod.ext
    · funext i
      change Sum.elim q.1 q.2
        ((Math.FiniteEmbedding.embeddingSplitEquiv f).symm (f i)) = q.1 i
      rw [← Math.FiniteEmbedding.embeddingSplitEquiv_apply_range f i]
      simp
    · funext j
      change Sum.elim q.1 q.2
        ((Math.FiniteEmbedding.embeddingSplitEquiv f).symm
          (Math.FiniteEmbedding.embeddingComplementEquiv f j)) = q.2 j
      rw [← Math.FiniteEmbedding.embeddingSplitEquiv_apply_complement f j]
      simp

/-- Split Alice and Bob bit strings, grouping both selected strings before both complementary
strings. -/
def selectedPairBitSplit {n N : ℕ} (f : Fin n ↪ Fin N) :
    ((Fin N → Bit) × (Fin N → Bit)) ≃
      ((Fin n → Bit) × (Fin n → Bit)) ×
        ((Fin (N - n) → Bit) × (Fin (N - n) → Bit)) where
  toFun x :=
    (((selectedBitSplit f x.1).1, (selectedBitSplit f x.2).1),
      ((selectedBitSplit f x.1).2, (selectedBitSplit f x.2).2))
  invFun q :=
    ((selectedBitSplit f).symm (q.1.1, q.2.1),
      (selectedBitSplit f).symm (q.1.2, q.2.2))
  left_inv x := by
    apply Prod.ext
    · exact (selectedBitSplit f).symm_apply_apply x.1
    · exact (selectedBitSplit f).symm_apply_apply x.2
  right_inv q := by
    rcases q with ⟨⟨xA, xB⟩, ⟨uA, uB⟩⟩
    simp

/-- Certified partial trace that retains only the selected Alice and Bob input strings.

`selectedPairBitSplit` first groups selected and complementary strings; product commutation puts
the complementary pair in the acted-on factor of `discardToUnit`.  The selected pair is the
untouched spectator factor of `Instrument.onFactor`. -/
def selectedInputMarginalInstrument {n N : ℕ} (f : Fin n ↪ Fin N) :
    Instrument ((Fin N → Bit) × (Fin N → Bit))
      ((Fin n → Bit) × (Fin n → Bit)) Unit :=
  Instrument.onFactor
    ((selectedPairBitSplit f).trans (Equiv.prodComm _ _))
    (unitProdEquiv _).symm
    (Instrument.discardToUnit
      ((Fin (N - n) → Bit) × (Fin (N - n) → Bit)))

/-- Exact selected-input marginal formula for every complex input operator.

The selected row and column `x,x'` remain independent.  The complementary Alice/Bob string pair
is summed only on equal row and column coordinates.  The embedding supplies the size bound, so no
additional inequality, positivity, normalization, IID, support, or success premise is present. -/
theorem selectedInputMarginalInstrument_channel_apply
    {n N : ℕ} (f : Fin n ↪ Fin N)
    (rho : Op ((Fin N → Bit) × (Fin N → Bit)))
    (x x' : (Fin n → Bit) × (Fin n → Bit)) :
    (selectedInputMarginalInstrument f).channel rho x x' =
      ∑ u : (Fin (N - n) → Bit) × (Fin (N - n) → Bit),
        ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit f) (selectedPairBitSplit
          f)).toLinearMap rho) (x, u) (x', u) := by
  simp only [selectedInputMarginalInstrument, Instrument.channel_eq_sum,
    Fintype.sum_unique]
  rw [Instrument.onFactor_operation_apply,
    Instrument.discardToUnit_operation_apply]
  rfl

end QKD.BB84.Measurement
