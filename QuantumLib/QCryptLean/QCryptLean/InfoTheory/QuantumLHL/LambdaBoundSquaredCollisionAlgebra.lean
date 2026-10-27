import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundTwoUniversal
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2

/-! # Lambda Bound Squared Collision Algebra -/


open Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-- Seed-collision sums can be rewritten as pair sums with filter-card
coefficients. -/
private lemma seed_collision_sum_eq_filter_pair_sum
    {Seed X Z : Type*} [Fintype Seed] [Fintype X] [DecidableEq Z]
    (H : HashFamily Seed X Z) (K : X → X → ℝ) :
    (1 / (Fintype.card Seed : ℝ)) *
        ∑ s : Seed, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then K x x' else 0) =
      ∑ x : X, ∑ x' : X,
        ((1 / (Fintype.card Seed : ℝ)) *
          ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ)) *
        K x x' := by
  have hSwap :
      (∑ s : Seed, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then K x x' else 0)) =
      ∑ x : X, ∑ x' : X,
        ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) *
          K x x' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    exact Finset.sum_ite_const_eq_filter_card_mul_real
      (fun s : Seed => H.hash s x = H.hash s x') (K x x')
  rw [hSwap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end InfoTheory.QuantumLHL

end -- noncomputable section
