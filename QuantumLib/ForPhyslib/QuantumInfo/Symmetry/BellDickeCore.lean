import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Multiset.Fintype
import Mathlib.Tactic

/-! # Bell Dicke Core -/


noncomputable section

open scoped BigOperators

namespace Quantum.Symmetry


/-- Mapping the universal multiset of `Fin n` by a permutation leaves it unchanged. -/
private lemma univ_val_map_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map ⇑σ = Finset.univ.val := by
  have h := congrArg Finset.val (Finset.map_univ_equiv σ)
  rwa [Finset.map_val, Equiv.coe_toEmbedding] at h

/-- Composing with a permutation on the domain preserves the value-multiset over `Fin n`. -/
private lemma univ_val_map_comp_perm {n : ℕ} (g : Fin n → Fin 4) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map (g ∘ ⇑σ) = Finset.univ.val.map g := by
  rw [← Multiset.map_map, univ_val_map_perm]

/-- Two functions on `Fin n` with the same value-multiset differ by a permutation of the domain. -/
private lemma exists_perm_comp_of_map_eq {n : ℕ} {f g : Fin n → Fin 4}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f := by
  classical
  have hcard : ∀ c : Fin 4, Fintype.card {x // f x = c} = Fintype.card {x // g x = c} := by
    intro c
    have hbridge : ∀ h2 : Fin n → Fin 4,
        Fintype.card {x // h2 x = c} = Multiset.count c (Finset.univ.val.map h2) := by
      intro h2
      rw [Multiset.count_map, Fintype.card_subtype]
      change (Multiset.filter (fun x => h2 x = c) Finset.univ.val).card
        = (Multiset.filter (fun a => c = h2 a) Finset.univ.val).card
      congr 1
      exact Multiset.filter_congr (fun x _ => eq_comm)
    rw [hbridge f, hbridge g, h]
  let φ : ∀ c : Fin 4, {x // f x = c} ≃ {x // g x = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
            ((Equiv.sigmaCongrRight φ).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  funext x
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  rw [(φ _ _).2, Equiv.sigmaFiberEquiv_symm_apply_fst]

/-- The fibers of `σ ↦ g ∘ σ` over any two functions reachable from `g` have equal cardinality
(a coset of the stabilizer under right multiplication by a fixed permutation). -/
private lemma fiber_card_const {n : ℕ} {g f f' : Fin n → Fin 4}
    (hf : ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f)
    (hf' : ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f') :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f')).card
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hf
  obtain ⟨σ', hσ'⟩ := hf'
  apply Finset.card_nbij' (fun σ => σ * σ'⁻¹ * σ₀) (fun σ => σ * σ₀⁻¹ * σ')
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
    funext y
    change g ((σ * σ'⁻¹ * σ₀) y) = f y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h1 : g (σ (σ'⁻¹ (σ₀ y))) = f' (σ'⁻¹ (σ₀ y)) := congrFun hσ _
    have h2 : f' (σ'⁻¹ (σ₀ y)) = g (σ₀ y) := by
      have hz := congrFun hσ' (σ'⁻¹ (σ₀ y))
      simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hz
      exact hz.symm
    rw [h1, h2]
    exact congrFun hσ₀ y
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
    funext y
    change g ((σ * σ₀⁻¹ * σ') y) = f' y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h1 : g (σ (σ₀⁻¹ (σ' y))) = f (σ₀⁻¹ (σ' y)) := congrFun hσ _
    have h2 : f (σ₀⁻¹ (σ' y)) = g (σ' y) := by
      have hz := congrFun hσ₀ (σ₀⁻¹ (σ' y))
      simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hz
      exact hz.symm
    rw [h1, h2]
    exact congrFun hσ' y
  · intro σ _; dsimp only; group
  · intro σ _; dsimp only; group

/-- Same value-multiset ⟹ the permutation count times the multiset-orbit size is `n!`
(orbit–stabilizer, via `Finset.card_eq_sum_card_fiberwise` and constant fiber cardinality). -/
lemma bellPerm_count_mul_orbit {n : ℕ} {f g : Fin n → Fin 4}
    (hfg : Finset.univ.val.map f = Finset.univ.val.map g) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card *
      (Finset.univ.filter (fun f' : Fin n → Fin 4 =>
        Finset.univ.val.map f' = Finset.univ.val.map g)).card
      = Nat.factorial n := by
  classical
  set orbit := Finset.univ.filter (fun f' : Fin n → Fin 4 =>
    Finset.univ.val.map f' = Finset.univ.val.map g) with horbit
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin n))) ↑orbit := by
    intro σ _
    simp only [horbit, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    exact univ_val_map_comp_perm g σ
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  have hconst : ∀ f' ∈ orbit,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f')).card
        = (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
    intro f' hf'
    rw [horbit, Finset.mem_filter] at hf'
    exact fiber_card_const (exists_perm_comp_of_map_eq hfg)
      (exists_perm_comp_of_map_eq hf'.2)
  have hsum2 : Nat.factorial n
      = ∑ _f' ∈ orbit, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
    rw [hsum]; exact Finset.sum_congr rfl hconst
  rw [Finset.sum_const, smul_eq_mul] at hsum2
  rw [mul_comm]; exact hsum2.symm

/-- Different value-multiset ⟹ no permutation relates the two Bell strings. -/
private lemma bellPerm_count_zero {n : ℕ} {f g : Fin n → Fin 4}
    (hfg : Finset.univ.val.map f ≠ Finset.univ.val.map g) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ heq
  exact hfg (by rw [← heq]; exact univ_val_map_comp_perm g σ)

end Quantum.Symmetry

end -- noncomputable section
