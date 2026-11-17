import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! # Walsh Hadamard -/


open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.Bases

variable {n : ℕ}


/-- **The Walsh character** `(-1)^{⟨x, y⟩}` of the group `(ℤ/2)ⁿ`, where `⟨x, y⟩` is the number of
coordinates on which `x` and `y` are both `true`.  It is written as a product over coordinates,
which is what makes the orthogonality relation a coordinatewise computation. -/
def walshSign (x y : Fin n → Bool) : ℂ :=
  ∏ i, if x i && y i then (-1 : ℂ) else 1

/-- The Walsh character is symmetric: `(-1)^{⟨x,y⟩} = (-1)^{⟨y,x⟩}`. -/
lemma walshSign_comm (x y : Fin n → Bool) : walshSign x y = walshSign y x := by
  unfold walshSign
  exact Finset.prod_congr rfl fun i _ => by rw [Bool.and_comm]

/-- The Walsh character is real: it is a product of `±1`. -/
@[simp] lemma conj_walshSign (x y : Fin n → Bool) : conj (walshSign x y) = walshSign x y := by
  unfold walshSign
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by split <;> simp

/-- The Walsh character has unit modulus. -/
@[simp] lemma normSq_walshSign (x y : Fin n → Bool) : Complex.normSq (walshSign x y) = 1 := by
  unfold walshSign
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => by split <;> simp

/-- **Walsh orthogonality.**  Summing the product of two Walsh characters over all bit strings
gives `2ⁿ` when the characters agree and `0` otherwise:

  `∑_{x} (-1)^{⟨y,x⟩} (-1)^{⟨z,x⟩} = 2ⁿ · [y = z]`.

Because the character is a product over coordinates, the sum factors into `n` independent
two-term sums `1 + (-1)^{y_i}(-1)^{z_i}`, each equal to `2` when `y_i = z_i` and to `0`
otherwise. -/
theorem sum_walshSign_mul (y z : Fin n → Bool) :
    (∑ x : Fin n → Bool, walshSign y x * walshSign z x) = if y = z then (2 : ℂ) ^ n else 0 := by
  classical
  -- Write the summand as a product over coordinates and exchange product and sum.
  have hterm : ∀ x : Fin n → Bool, walshSign y x * walshSign z x =
      ∏ i, ((if y i && x i then (-1 : ℂ) else 1) * (if z i && x i then (-1 : ℂ) else 1)) := by
    intro x
    unfold walshSign
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [← Fintype.prod_sum
    (f := fun (i : Fin n) (bi : Bool) =>
      (if y i && bi then (-1 : ℂ) else 1) * (if z i && bi then (-1 : ℂ) else 1))]
  -- Each coordinate contributes `2` if the two bits agree and `0` otherwise.
  have hcoord : ∀ i : Fin n,
      (∑ bi : Bool, (if y i && bi then (-1 : ℂ) else 1) * (if z i && bi then (-1 : ℂ) else 1)) =
        if y i = z i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hy : y i <;> cases hz : z i <;> norm_num
  rw [Finset.prod_congr rfl fun i _ => hcoord i]
  by_cases h : y = z
  · subst h
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := by
      by_contra hcon
      exact h (funext fun i => not_not.mp (fun hne => hcon ⟨i, hne⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)


/-- The normalization squares to `2ⁿ`. -/
lemma walsh_sqrt_mul_self (n : ℕ) :
    ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) = (2 : ℂ) ^ n := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The Walsh character is `(-1)^{|{i : xᵢ ∧ yᵢ}|}`: the product form is the usual sign of the
bitwise inner product. -/
lemma walshSign_eq_neg_one_pow (x y : Fin n → Bool) :
    walshSign x y = (-1 : ℂ) ^ (Finset.univ.filter fun i => x i && y i).card := by
  unfold walshSign
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ## The Walsh character sum (orthogonality) -/

/-- The normalization `√(2ⁿ)` is nonzero. -/
lemma walsh_sqrt_ne_zero (n : ℕ) : ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  exact Real.sqrt_ne_zero'.mpr (by positivity)

end Quantum.Bases

end
