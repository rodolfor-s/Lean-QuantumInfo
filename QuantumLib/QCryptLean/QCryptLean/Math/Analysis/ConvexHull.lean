import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Compact convex hulls in finite-dimensional real spaces -/

open scoped BigOperators
noncomputable section

/-- Sum over a finite type of a function obtained by extending along an embedding `e : σ ↪ ι`,
where the extension vanishes off the range of `e`, equals the sum of the original function. -/
private lemma sum_eq_sum_of_embedding {σ ι : Type*} [Fintype σ] [Fintype ι] {M : Type*}
    [AddCommMonoid M] (e : σ ↪ ι) (g : ι → M) (gσ : σ → M)
    (hg1 : ∀ i, g (e i) = gσ i) (hg2 : ∀ j, (¬ ∃ i, e i = j) → g j = 0) :
    ∑ j, g j = ∑ i, gσ i := by
  classical
  have h2 : ∑ b ∈ Finset.univ.map e, g b = ∑ j, g j :=
    Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hg2 j (by
      rw [Finset.mem_map] at hj
      push Not at hj
      rintro ⟨i, rfl⟩
      exact hj i (Finset.mem_univ i) rfl))
  rw [← h2, Finset.sum_map Finset.univ e g]
  exact Finset.sum_congr rfl (fun i _ => hg1 i)


/-- **Finite-dimensional Carathéodory compactness.** In a finite-dimensional real normed space the
convex hull of a compact set is compact. The convex hull is realised as the continuous image of the
compact product of `Convexity.StdSimplex` and tuples of `d + 1` points in the set,
with `d = finrank`; the ⊆ direction is Carathéodory
(`eq_pos_convex_span_of_mem_convexHull`) padded to `d + 1` points. -/
theorem IsCompact.convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (_root_.convexHull ℝ s) := by
  classical
  set d := Module.finrank ℝ E with hd
  have hgcont : Continuous (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E) =>
      ∑ i, p.1 i • p.2 i) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd)
  let weights := Set.range (fun t : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
    (t.weights : Fin (d + 1) → ℝ))
  have hweights (w : Fin (d + 1) → ℝ) :
      w ∈ weights ↔ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
    simp only [weights, Convexity.StdSimplex.range_toFun_comp_weights,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  have hKcompact : IsCompact (weights ×ˢ
      (Set.univ.pi (fun _ : Fin (d + 1) => s))) :=
    (isCompact_range (continuous_pi (fun i =>
      Convexity.StdSimplex.continuous_weights_apply ℝ i))).prod (isCompact_univ_pi (fun _ => hs))
  have himg : _root_.convexHull ℝ s = (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E) =>
      ∑ i, p.1 i • p.2 i) '' (weights ×ˢ
        (Set.univ.pi (fun _ : Fin (d + 1) => s))) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨σ, hσfin, z, w, hzs, haff, hwpos, hwsum, hwcomb⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let : Fintype σ := hσfin
      have hσne : Nonempty σ := by
        rcases isEmpty_or_nonempty σ with hE | hN
        · exfalso
          rw [Finset.univ_eq_empty, Finset.sum_empty] at hwsum
          exact one_ne_zero hwsum.symm
        · exact hN
      have hcard : Fintype.card σ ≤ Fintype.card (Fin (d + 1)) := by
        rw [Fintype.card_fin]
        have h1 := AffineIndependent.card_le_finrank_succ haff
        have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ d := by
          have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
          rwa [← hd] at this
        omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      obtain ⟨i₀⟩ := hσne
      have hpad : z i₀ ∈ s := hzs ⟨i₀, rfl⟩
      set W : Fin (d + 1) → ℝ := Function.extend (⇑e) w (fun _ => 0) with hWdef
      set Z : Fin (d + 1) → E := Function.extend (⇑e) z (fun _ => z i₀) with hZdef
      have hWe : ∀ i, W (e i) = w i := fun i => by
        rw [hWdef]; exact e.injective.extend_apply w _ i
      have hZe : ∀ i, Z (e i) = z i := fun i => by
        rw [hZdef]; exact e.injective.extend_apply z _ i
      have hWout : ∀ j, (¬ ∃ i, e i = j) → W j = 0 := fun j hj => by
        rw [hWdef]; exact Function.extend_apply' _ _ j hj
      have hZout : ∀ j, (¬ ∃ i, e i = j) → Z j = z i₀ := fun j hj => by
        rw [hZdef]; exact Function.extend_apply' _ _ j hj
      have hWnonneg : ∀ j, 0 ≤ W j := by
        intro j
        rcases em (∃ i, e i = j) with ⟨i, rfl⟩ | hj
        · rw [hWe i]; exact (hwpos i).le
        · rw [hWout j hj]
      have hWsum : ∑ j, W j = 1 := by
        rw [sum_eq_sum_of_embedding e W w hWe hWout]; exact hwsum
      have hZmem : ∀ j, Z j ∈ s := by
        intro j
        rcases em (∃ i, e i = j) with ⟨i, rfl⟩ | hj
        · rw [hZe i]; exact hzs ⟨i, rfl⟩
        · rw [hZout j hj]; exact hpad
      have hgeq : (∑ i, W i • Z i) = x :=
        calc ∑ i, W i • Z i = ∑ i, w i • z i :=
              sum_eq_sum_of_embedding e (fun j => W j • Z j) (fun i => w i • z i)
                (fun i => by change W (e i) • Z (e i) = w i • z i; rw [hWe i, hZe i])
                (fun j hj => by change W j • Z j = 0; rw [hWout j hj, zero_smul])
          _ = x := hwcomb
      exact ⟨(W, Z), ⟨(hweights W).mpr ⟨hWnonneg, hWsum⟩,
        Set.mem_univ_pi.mpr hZmem⟩, hgeq⟩
    · rintro x ⟨⟨W, Z⟩, ⟨hW, hZ⟩, rfl⟩
      have hW := (hweights W).mp hW
      have hWsum : ∑ i, W i = 1 := hW.2
      have hZmem : ∀ i, Z i ∈ s := Set.mem_univ_pi.mp hZ
      have hcm : (∑ i, W i • Z i) = Finset.univ.centerMass W Z :=
        (Finset.centerMass_eq_of_sum_1 _ Z hWsum).symm
      change (∑ i, W i • Z i) ∈ _root_.convexHull ℝ s
      rw [hcm]
      exact Finset.centerMass_mem_convexHull _ (fun i _ => hW.1 i)
        (by rw [hWsum]; exact one_pos) (fun i _ => hZmem i)
  rw [himg]
  exact hKcompact.image hgcont


