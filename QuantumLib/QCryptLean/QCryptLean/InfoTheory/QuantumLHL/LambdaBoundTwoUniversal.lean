import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor

/-! # Lambda Bound Two Universal -/



noncomputable section

open scoped BigOperators

/-- `∑ s, (if P s then c else 0) = |{s : P s}| * c` (ℝ-valued). -/
lemma Finset.sum_ite_const_eq_filter_card_mul_real
    {S : Type*} [Fintype S] (P : S → Prop) [DecidablePred P] (c : ℝ) :
    (∑ s : S, (if P s then c else 0)) =
      ((Finset.univ.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

namespace InfoTheory.QuantumLHL

end InfoTheory.QuantumLHL

end -- noncomputable section
