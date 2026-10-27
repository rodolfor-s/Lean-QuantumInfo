import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Relabeling finite BB84 sampling controls

This module transports basis strings, matched-round shuffles, selected injections, and the
independent raw-control law along a permutation of physical round identifiers. Basis strings are
pulled back while matched identifiers and selected embeddings are pushed forward.

The late basis-comparison schedule follows Renner, arXiv:quant-ph/0512258v2, lines 673--736, and
the fixed-batch sampling conditions follow Pfister et al., arXiv:1506.07502v3, Sections IV--V.
-/

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- Pull a basis string back along a permutation of physical round identifiers. -/
def relabelBasis {N : ℕ} (τ : Fin N ≃ Fin N) (a : Fin N → Basis) : Fin N → Basis :=
  a ∘ τ.symm

/-- Sending an old matched identifier through `τ` gives exactly a matched identifier for the
relabeled basis strings. -/
def matchedRelabelEquiv {N : ℕ} (τ : Fin N ≃ Fin N) (a b : Fin N → Basis) :
    {i : Fin N // i ∈ Matched a b} ≃
      {j : Fin N // j ∈ Matched (relabelBasis τ a) (relabelBasis τ b)} where
  toFun i := ⟨τ i.1, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change a (τ.symm (τ i.1)) = b (τ.symm (τ i.1))
    rw [τ.symm_apply_apply]
    exact (Finset.mem_filter.mp i.2).2⟩
  invFun j := ⟨τ.symm j.1, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp j.2).2⟩
  left_inv i := Subtype.ext (τ.symm_apply_apply i.1)
  right_inv j := Subtype.ext (τ.apply_symm_apply j.1)

/-- Relabeling preserves the number of matched identifiers. -/
theorem matched_relabel_card {N : ℕ} (τ : Fin N ≃ Fin N) (a b : Fin N → Basis) :
    (Matched (relabelBasis τ a) (relabelBasis τ b)).card = (Matched a b).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (matchedRelabelEquiv τ a b)).symm

/-- Transport a matched-round ordering through the explicit matched-subtype equivalence. -/
def relabelOrder {N : ℕ} (τ : Fin N ≃ Fin N) (a b : Fin N → Basis)
    (order : Shuffle a b) : Shuffle (relabelBasis τ a) (relabelBasis τ b) :=
  ((finCongr (matched_relabel_card τ a b)).trans order).trans (matchedRelabelEquiv τ a b)

/-- Relabel both basis strings and every identifier in the stored matched-round ordering. -/
def relabelRaw {N : ℕ} (τ : Fin N ≃ Fin N) (omega : RawControl N) : RawControl N :=
  ⟨relabelBasis τ omega.a, relabelBasis τ omega.b,
    relabelOrder τ omega.a omega.b omega.order⟩

/-- Relabeling and relabeling back are inverse on the complete raw control.

The equality includes the dependent shuffle field. -/
theorem relabelRaw_inverse_laws {N : ℕ} (τ : Fin N ≃ Fin N) :
    (∀ omega : RawControl N, relabelRaw τ.symm (relabelRaw τ omega) = omega) ∧
      (∀ omega : RawControl N, relabelRaw τ (relabelRaw τ.symm omega) = omega) := by
  have equivHEq {α α' β β' : Type} (e : α ≃ β) (e' : α' ≃ β')
      (hα : α = α') (hβ : β = β')
      (happly : ∀ x x', x ≍ x' → e x ≍ e' x') : e ≍ e' := by
    cases hα
    cases hβ
    apply heq_of_eq
    apply Equiv.ext
    intro x
    exact eq_of_heq (happly x x HEq.rfl)
  constructor
  · intro omega
    rcases omega with ⟨a, b, order⟩
    simp only [relabelRaw, RawControl.mk.injEq]
    have ha : relabelBasis τ.symm (relabelBasis τ a) = a := by
      funext i
      simp [relabelBasis]
    have hb : relabelBasis τ.symm (relabelBasis τ b) = b := by
      funext i
      simp [relabelBasis]
    refine ⟨ha, hb, ?_⟩
    have hdom :
        Fin (Matched (relabelBasis τ.symm (relabelBasis τ a))
          (relabelBasis τ.symm (relabelBasis τ b))).card =
          Fin (Matched a b).card := by
      rw [ha, hb]
    have hcod :
        {i : Fin N // i ∈ Matched (relabelBasis τ.symm (relabelBasis τ a))
          (relabelBasis τ.symm (relabelBasis τ b))} =
          {i : Fin N // i ∈ Matched a b} := by
      rw [ha, hb]
    apply equivHEq _ _ hdom hcod
    intro i j hij
    refine (Subtype.heq_iff_coe_eq (fun x => ?_)).2 ?_
    · rw [ha, hb]
    · simp only [relabelOrder, Equiv.trans_apply, matchedRelabelEquiv,
        Equiv.coe_fn_mk]
      rw [τ.symm_apply_apply]
      apply congrArg (fun k => (order k).1)
      apply Fin.ext
      simpa using Fin.val_eq_val_of_heq hij
  · intro omega
    rcases omega with ⟨a, b, order⟩
    simp only [relabelRaw, RawControl.mk.injEq]
    have ha : relabelBasis τ (relabelBasis τ.symm a) = a := by
      funext i
      simp [relabelBasis]
    have hb : relabelBasis τ (relabelBasis τ.symm b) = b := by
      funext i
      simp [relabelBasis]
    refine ⟨ha, hb, ?_⟩
    have hdom :
        Fin (Matched (relabelBasis τ (relabelBasis τ.symm a))
          (relabelBasis τ (relabelBasis τ.symm b))).card =
          Fin (Matched a b).card := by
      rw [ha, hb]
    have hcod :
        {i : Fin N // i ∈ Matched (relabelBasis τ (relabelBasis τ.symm a))
          (relabelBasis τ (relabelBasis τ.symm b))} =
          {i : Fin N // i ∈ Matched a b} := by
      rw [ha, hb]
    apply equivHEq _ _ hdom hcod
    intro i j hij
    refine (Subtype.heq_iff_coe_eq (fun x => ?_)).2 ?_
    · rw [ha, hb]
    · simp only [relabelOrder, Equiv.trans_apply, matchedRelabelEquiv,
        Equiv.coe_fn_mk]
      rw [τ.apply_symm_apply]
      apply congrArg (fun k => (order k).1)
      apply Fin.ext
      simpa using Fin.val_eq_val_of_heq hij

/-- The explicit bijection of complete raw controls induced by a physical-index permutation. -/
def rawControlRelabel {N : ℕ} (τ : Fin N ≃ Fin N) : RawControl N ≃ RawControl N where
  toFun := relabelRaw τ
  invFun := relabelRaw τ.symm
  left_inv := (relabelRaw_inverse_laws τ).1
  right_inv := (relabelRaw_inverse_laws τ).2

/-- Matched, Z-filtered, and X-filtered lists retain their sampled order while every physical
identifier is sent through `τ`. -/
theorem basisOrders_relabel {N : ℕ} (τ : Fin N ≃ Fin N) (omega : RawControl N) :
    matchedOrder (rawControlRelabel τ omega) = (matchedOrder omega).map τ ∧
      zOrder (rawControlRelabel τ omega) = (zOrder omega).map τ ∧
      xOrder (rawControlRelabel τ omega) = (xOrder omega).map τ := by
  have hmatched :
      matchedOrder (rawControlRelabel τ omega) = (matchedOrder omega).map τ := by
    simp only [matchedOrder, rawControlRelabel, relabelRaw, relabelOrder,
      matchedRelabelEquiv, Equiv.coe_fn_mk, List.map_ofFn]
    apply List.ext_getElem
    · simpa using matched_relabel_card τ omega.a omega.b
    · intro n hn₁ hn₂
      simp
      rfl
  refine ⟨hmatched, ?_, ?_⟩
  · rw [zOrder, zOrder, hmatched, List.filter_map]
    simp [rawControlRelabel, relabelRaw, relabelBasis, Function.comp_def]
  · rw [xOrder, xOrder, hmatched, List.filter_map]
    simp [rawControlRelabel, relabelRaw, relabelBasis, Function.comp_def]

/-- Postcompose a selected injection with the physical-index relabeling. -/
def relabelEmbedding {N n : ℕ} (τ : Fin N ≃ Fin N) (f : Fin n ↪ Fin N) : Fin n ↪ Fin N :=
  f.trans τ.toEmbedding

/-- Fixed-quota selection commutes with physical-index relabeling.

The quotas, including zero quotas and shortages, are unchanged. -/
theorem select_relabel {N : ℕ} (τ : Fin N ≃ Fin N) (omega : RawControl N)
    (nK mZ mX : ℕ) :
    select nK mZ mX (rawControlRelabel τ omega) =
      (select nK mZ mX omega).map (relabelEmbedding τ) := by
  have horders := basisOrders_relabel τ omega
  have hzPrefix :
      zPrefix (nK := nK) (mZ := mZ) (rawControlRelabel τ omega) =
        (zPrefix (nK := nK) (mZ := mZ) omega).map τ := by
    unfold zPrefix
    rw [horders.2.1, ← List.map_take]
  have hxPrefix :
      xPrefix (mX := mX) (rawControlRelabel τ omega) =
        (xPrefix (mX := mX) omega).map τ := by
    unfold xPrefix
    rw [horders.2.2, ← List.map_take]
  have hquotas :
      HasQuotas nK mZ mX (rawControlRelabel τ omega) ↔
        HasQuotas nK mZ mX omega := by
    simp [HasQuotas, horders.2.1, horders.2.2]
  by_cases h : HasQuotas nK mZ mX omega
  · have hr : HasQuotas nK mZ mX (rawControlRelabel τ omega) := hquotas.mpr h
    simp only [select, hr, h, dite_eq_left, Option.map_some, Option.some.injEq]
    ext k
    simp only [selectedEmbedding, relabelEmbedding, Function.Embedding.coeFn_mk,
      Function.Embedding.coe_trans, Function.comp_apply]
    generalize (packedRoleEquiv nK mZ mX).symm k = role
    rcases role with (⟨key | z⟩ | x) <;>
      simp only [selectedRoleValue, hzPrefix, hxPrefix, List.get_eq_getElem, List.getElem_map]
      <;> rfl
  · have hr : ¬HasQuotas nK mZ mX (rawControlRelabel τ omega) :=
      fun hr => h (hquotas.mp hr)
    simp [select, hr, h]

/-- The independent raw-control point mass is invariant under relabeling physical rounds.

It holds for arbitrary fixed, possibly unequal or
degenerate one-round laws because the same law is used at every position. -/
theorem rawControlLaw_apply_relabel {N : ℕ} (τ : Fin N ≃ Fin N) (pA pB : PMF Basis)
    (omega : RawControl N) :
    rawControlLaw N pA pB (rawControlRelabel τ omega) = rawControlLaw N pA pB omega := by
  have hpA :
      (∏ i : Fin N, pA (relabelBasis τ omega.a i)) =
        ∏ i : Fin N, pA (omega.a i) := by
    simpa [relabelBasis, Function.comp_def] using
      τ.symm.prod_comp (fun i : Fin N => pA (omega.a i))
  have hpB :
      (∏ i : Fin N, pB (relabelBasis τ omega.b i)) =
        ∏ i : Fin N, pB (omega.b i) := by
    simpa [relabelBasis, Function.comp_def] using
      τ.symm.prod_comp (fun i : Fin N => pB (omega.b i))
  change rawControlLaw N pA pB (relabelRaw τ omega) = rawControlLaw N pA pB omega
  rw [rawControlLaw_apply, rawControlLaw_apply]
  simp only [relabelRaw]
  rw [hpA, hpB, matched_relabel_card]

/-! ## Relabeling formulas -/

/-- The pulled-back string reads the original value at the corresponding old identifier. -/
theorem relabelBasis_apply {N : ℕ} (τ : Fin N ≃ Fin N) (a : Fin N → Basis) (i : Fin N) :
    relabelBasis τ a (τ i) = a i := by
  simp [relabelBasis]

/-- The two stored basis strings of `relabelRaw` are definitionally the pulled-back strings. -/
theorem relabelRaw_basis_fields {N : ℕ} (τ : Fin N ≃ Fin N) (omega : RawControl N) :
    (relabelRaw τ omega).a = relabelBasis τ omega.a ∧
      (relabelRaw τ omega).b = relabelBasis τ omega.b := by
  exact ⟨rfl, rfl⟩

/-- The transported ordering sends an old ordered identifier through `τ`. -/
theorem relabelOrder_apply {N : ℕ} (τ : Fin N ≃ Fin N) (a b : Fin N → Basis)
    (order : Shuffle a b)
    (k : Fin (Matched (relabelBasis τ a) (relabelBasis τ b)).card) :
    (relabelOrder τ a b order k).1 =
      τ (order (finCongr (matched_relabel_card τ a b) k)).1 := by
  rfl

/-- Relabeling a selected injection sends its actual selected value through `τ`. -/
theorem relabelEmbedding_apply {N n : ℕ} (τ : Fin N ≃ Fin N) (f : Fin n ↪ Fin N)
    (k : Fin n) : relabelEmbedding τ f k = τ (f k) := by
  rfl

end QKD.BB84.Sampling
