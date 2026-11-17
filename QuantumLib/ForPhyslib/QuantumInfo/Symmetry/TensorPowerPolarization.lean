import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Perm

/-! # Tensor Power Polarization -/


noncomputable section

open scoped BigOperators

namespace Quantum.Symmetry


/-- **Scalar polarization / inclusion–exclusion identity.**

For a matrix `x : Fin n → Fin n → ℂ` (`x i k` = the `k`-th factor of the `i`-th operator),

  `∑_{S ⊆ [n]} (-1)^{n-|S|} ∏ₖ (∑_{i∈S} x i k) = ∑_{σ ∈ Sₙ} ∏ₖ x (σ k) k`.

Expanding each product of sums over functions `p : [n] → S`, the coefficient of
`∏ₖ x (p k) k` is `∑_{S ⊇ image p} (-1)^{n-|S|}`, which is `1` if `p` is surjective (a
permutation) and `0` otherwise, by the alternating-sign powerset sum. -/
private lemma scalar_polarization {n : ℕ} (x : Fin n → Fin n → ℂ) :
    (∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, ∑ i ∈ S, x i k)
      = ∑ σ : Equiv.Perm (Fin n), ∏ k : Fin n, x (σ k) k := by
  classical
  -- The complement involution on `Finset (Fin n)`.
  set cE : Finset (Fin n) ≃ Finset (Fin n) :=
    ⟨fun s => sᶜ, fun s => sᶜ, fun s => compl_compl s, fun s => compl_compl s⟩ with hcE
  -- Step 1: expand each product of sums over `p ∈ piFinset (const S)`.
  have hstep1 : ∀ S : Finset (Fin n),
      (∏ k : Fin n, ∑ i ∈ S, x i k)
        = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => S), ∏ k : Fin n, x (p k) k := by
    intro S
    exact Finset.prod_univ_sum (fun _ : Fin n => S) (fun k i => x i k)
  -- The inner-coefficient computation `∑_{S ⊇ image p} (-1)^{n-|S|} = [image p = univ]`.
  have hcoef : ∀ p : Fin n → Fin n,
      (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0)
        = if Finset.image p Finset.univ = Finset.univ then 1 else 0 := by
    intro p
    set R : Finset (Fin n) := Finset.image p Finset.univ with hR
    -- rewrite the condition `∀ k, p k ∈ S` as `R ⊆ S`, and `(-1)^{n-|S|}` as `(-1)^{|Sᶜ|}`.
    have hcond : ∀ S : Finset (Fin n), (∀ k, p k ∈ S) ↔ R ⊆ S := by
      intro S
      rw [hR, Finset.image_subset_iff]
      constructor
      · intro h k _; exact h k
      · intro h k; exact h k (Finset.mem_univ k)
    have hsign : ∀ S : Finset (Fin n),
        (-1 : ℂ) ^ (n - S.card) = (-1 : ℂ) ^ (Sᶜ.card) := by
      intro S
      rw [Finset.card_compl, Fintype.card_fin]
    calc (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0)
        = ∑ S : Finset (Fin n), if R ⊆ S then (-1 : ℂ) ^ (Sᶜ.card) else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [hsign S]; simp only [hcond S]
      _ = ∑ S : Finset (Fin n), if R ⊆ Sᶜ then (-1 : ℂ) ^ (S.card) else 0 := by
          rw [← Equiv.sum_comp cE
            (fun S => if R ⊆ Sᶜ then (-1 : ℂ) ^ (S.card) else 0)]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp only [hcE, Equiv.coe_fn_mk, compl_compl]
      _ = ∑ S ∈ Rᶜ.powerset, (-1 : ℂ) ^ (S.card) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext S
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
            Finset.subset_compl_comm]
      _ = if Rᶜ = ∅ then 1 else 0 := by
          have h := Finset.sum_powerset_neg_one_pow_card (x := Rᶜ)
          have hc := congrArg (fun z : ℤ => (z : ℂ)) h
          simp only [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one,
            apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero] at hc
          exact hc
      _ = if R = Finset.univ then 1 else 0 := by
          simp only [Finset.compl_eq_empty_iff]
  -- Step 2: substitute, swap the order of summation, and collapse the coefficient.
  calc (∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, ∑ i ∈ S, x i k)
      = ∑ S : Finset (Fin n), ∑ p : Fin n → Fin n,
          (if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, x (p k) k else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hstep1 S, Finset.mul_sum, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    _ = ∑ p : Fin n → Fin n, (∏ k : Fin n, x (p k) k) *
          (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases h : (∀ k, p k ∈ S) <;> simp [h, mul_comm]
    _ = ∑ p : Fin n → Fin n, (∏ k : Fin n, x (p k) k) *
          (if Finset.image p Finset.univ = Finset.univ then 1 else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hcoef p]
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ k : Fin n, x (σ k) k := by
        have hsurj : ∀ p : Fin n → Fin n,
            Finset.image p Finset.univ = Finset.univ ↔ Function.Surjective p := by
          intro p
          rw [Finset.eq_univ_iff_forall]
          constructor
          · intro h y
            have hy := h y
            rw [Finset.mem_image] at hy
            obtain ⟨a, _, ha⟩ := hy
            exact ⟨a, ha⟩
          · intro h y
            rw [Finset.mem_image]
            obtain ⟨a, ha⟩ := h y
            exact ⟨a, Finset.mem_univ a, ha⟩
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter]
        refine Finset.sum_bij'
          (fun p hp => Equiv.ofBijective p
            (Finite.injective_iff_bijective.mp
              (Finite.injective_iff_surjective.mpr
                ((hsurj p).mp (Finset.mem_filter.mp hp).2))))
          (fun σ _ => (⇑σ : Fin n → Fin n))
          (fun p _ => Finset.mem_univ _)
          (fun σ _ => ?_) (fun p _ => ?_) (fun σ _ => ?_) (fun p _ => ?_)
        · -- j σ ∈ filter-set: ⇑σ has full image
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hsurj _).mpr σ.surjective⟩
        · -- left inverse on the filter-set: `⇑(ofBijective p _) = p`
          rfl
        · -- right inverse on Perm: `ofBijective ⇑σ _ = σ`
          exact Equiv.ext (fun y => rfl)
        · -- the summands agree
          rfl


end Quantum.Symmetry
