import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Permutation Action -/


open Matrix
open scoped Matrix BigOperators ComplexConjugate

noncomputable section

namespace Math.RepresentationTheory


/-- Helper: (σ₁ * σ₂).symm x = σ₂.symm (σ₁.symm x) -/
private lemma perm_mul_symm_apply {α : Type*} (σ₁ σ₂ : Equiv.Perm α) (x : α) :
    (σ₁ * σ₂).symm x = σ₂.symm (σ₁.symm x) := by
  simp [Equiv.Perm.mul_def]

private lemma perm_inv_symm {α : Type*} (σ : Equiv.Perm α) :
    (σ⁻¹ : Equiv.Perm α).symm = σ := by
  ext x
  simp [Equiv.Perm.inv_def]

/-- Precomposing by the inverse of a product is the same as precomposing by
the two inverses in reverse order. -/
lemma comp_perm_mul_symm {α β : Type*} (f : α → β) (σ₁ σ₂ : Equiv.Perm α) :
    (f ∘ ⇑σ₂.symm) ∘ ⇑σ₁.symm = f ∘ ⇑(σ₁ * σ₂).symm := by
  funext x
  simp only [Function.comp_apply, perm_mul_symm_apply]

/-- Equality after precomposition with a permutation can be moved across the inverse
permutation. -/
lemma eq_comp_perm_symm_iff_comp_perm_eq {α β : Type*} (f g : α → β)
    (σ : Equiv.Perm α) :
    f = g ∘ ⇑σ.symm ↔ f ∘ ⇑σ = g := by
  constructor
  · intro h
    funext x
    have hx := congr_fun h (σ x)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hx
  · intro h
    funext x
    have hx := congr_fun h (σ.symm x)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx

/-- A Young diagram is a partition of n: a non-increasing sequence of
    positive integers summing to n.

    Example: For n=4, the partitions are:
    - [4]: single row of 4 boxes
    - [3,1]: row of 3 + row of 1
    - [2,2]: two rows of 2
    - [2,1,1]: row of 2 + two rows of 1
    - [1,1,1,1]: four rows of 1 -/
structure YoungDiagram (n : ℕ) where
  /-- The parts of the partition (row lengths). -/
  parts : List ℕ
  /-- All parts are positive. -/
  parts_pos : ∀ p ∈ parts, 0 < p
  /-- The parts sum to n. -/
  sum_eq : parts.sum = n
  /-- The parts are sorted in non-increasing order. -/
  parts_sorted : parts.Pairwise (· ≥ ·)

/-- Number of rows in the Young diagram. -/
def YoungDiagram.numRows {n : ℕ} (Y : YoungDiagram n) : ℕ := Y.parts.length

/-- Number of columns (length of first row, or 0 if empty). -/
def YoungDiagram.numCols {n : ℕ} (Y : YoungDiagram n) : ℕ :=
  match Y.parts with
  | [] => 0
  | p :: _ => p

/-- The trivial (single-row) partition [n]. This corresponds to the
    symmetric representation. -/
def YoungDiagram.trivial (n : ℕ) (hn : 0 < n) : YoungDiagram n where
  parts := [n]
  parts_pos := by simp [hn]
  sum_eq := by simp
  parts_sorted := by simp

/-- The sign (single-column) partition [1,1,...,1]. This corresponds to the
    antisymmetric representation. Only valid when d ≥ n (needs n boxes in one column). -/
def YoungDiagram.sign (n : ℕ) : YoungDiagram n where
  parts := List.replicate n 1
  parts_pos := by simp
  sum_eq := by simp [List.sum_replicate]
  parts_sorted := by
    induction n with
    | zero => simp
    | succ k ih =>
      simp only [List.replicate_succ]
      rw [List.pairwise_cons]
      constructor
      · intro b hb
        simp only [List.mem_replicate, ne_eq] at hb
        omega
      · exact ih


/-- Young diagrams with at most d rows (valid for GL(d) representations). -/
def YoungDiagram.IsValidForDim {n : ℕ} (Y : YoungDiagram n) (d : ℕ) : Prop :=
  Y.numRows ≤ d

/-- The symmetric subspace corresponds to the trivial Young diagram [n].
    This is the subspace of states invariant under all permutations. -/
def symmetricYoungDiagram (n : ℕ) (hn : 0 < n) : YoungDiagram n :=
  YoungDiagram.trivial n hn

/-- The symmetric power of `Fin d` has the stars-and-bars cardinality. -/
lemma card_sym_fin_eq_choose (d n : ℕ) [NeZero d] :
    Fintype.card (Sym (Fin d) n) = Nat.choose (n + d - 1) (d - 1) := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [show d + n - 1 = n + d - 1 from by omega]
  exact (Nat.choose_symm_of_eq_add (by omega)).symm

/-- The dimension of the symmetric subspace is C(n+d-1, d-1) = (n+d-1)!/(n!(d-1)!).
    This is the number of ways to distribute n indistinguishable balls into d bins,
    or equivalently, the number of homogeneous polynomials of degree n in d variables.

    Reference: "Stars and bars" combinatorics. -/
theorem symmetricSubspace_dimension (d n : ℕ) [NeZero d] :
    -- dim(Sym^n(ℂᵈ)) = C(n+d-1, d-1)
    -- The number of symmetric basis states equals the binomial coefficient
    let symDim := Nat.choose (n + d - 1) (d - 1)
    -- This equals the number of ways to choose occupation numbers
    -- (n₁,...,nₐ) with n₁ + ... + nₐ = n and all nᵢ ≥ 0
    symDim = Nat.card {f : Fin d → ℕ // ∑ i, f i = n} := by
  simp only
  have : Fintype {f : Fin d → ℕ // ∑ i, f i = n} :=
    Fintype.ofEquiv (Sym (Fin d) n) (Sym.equivNatSumOfFintype (Fin d) n)
  rw [Nat.card_eq_fintype_card,
      ← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin d) n),
      card_sym_fin_eq_choose]


/-- Conjugation by a fixed group element is a bijection. -/
lemma mul_conj_bijective {G : Type*} [Group G] (g : G) :
    Function.Bijective (fun x : G => g * x * g⁻¹) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h'
  · intro y
    refine ⟨g⁻¹ * y * g, ?_⟩
    simp [mul_assoc]

section PermFunctionAction

/-- The natural action of permutations on the finite set of tensor positions. -/
local instance permFinAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n) :=
  Equiv.Perm.applyMulAction _

/-- The induced action on finite-valued strings by permuting their positions. -/
local instance permFunAction (d n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n → Fin d) :=
  arrowAction

/-- Orbit equivalence of finite strings is decidable by enumerating position permutations. -/
local instance permFunOrbitRelDecidable (d n : ℕ) :
    DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r := by
  intro f g
  simp only [MulAction.orbitRel_apply]
  rw [MulAction.mem_orbit_iff]
  exact Fintype.decidableExistsFintype

/-- For the arrow action of permutations on functions, fixed points are exactly
functions satisfying `f ∘ σ = f`. -/
lemma mem_fixedBy_perm_arrow_iff (d n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin d) :
    f ∈ MulAction.fixedBy (Fin n → Fin d) σ ↔ f ∘ ⇑σ = f := by
  rw [MulAction.mem_fixedBy]
  constructor
  · intro hf
    funext k
    have h : f (σ.symm (σ k)) = f (σ k) := congr_fun hf (σ k)
    simp only [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro hf
    funext k
    change f (σ.symm k) = f k
    have h := congr_fun hf (σ.symm k)
    simp only [Function.comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- The fixed-point set of the arrow action has the same cardinality as the
explicit filter of functions satisfying `f ∘ σ = f`. -/
lemma card_fixedBy_perm_arrow_eq_filter_card (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (Fin n → Fin d) σ) =
      (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f)).card := by
  rw [← Fintype.card_coe (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f))]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_fixedBy_perm_arrow_iff d n σ f).mp hf⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact (mem_fixedBy_perm_arrow_iff d n σ f).mpr hf⟩
    left_inv := fun ⟨f, _⟩ => by simp
    right_inv := fun ⟨f, _⟩ => by simp
  }

/-- Two functions `Fin n → Fin d` with permutation-equivalent value lists lie
in the same orbit under permutations of the domain. -/
lemma permFun_orbitRel_of_list_ofFn_perm (f g : Fin n → Fin d)
    (hperm : (List.ofFn f).Perm (List.ofFn g)) :
    MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d) f g := by
  apply MulAction.orbitRel_apply.mpr
  rw [MulAction.mem_orbit_iff]
  let σf := Tuple.sort f
  let σg := Tuple.sort g
  have hfmon : Monotone (f ∘ σf) := Tuple.monotone_sort f
  have hgmon : Monotone (g ∘ σg) := Tuple.monotone_sort g
  have hperm2 : (List.ofFn (f ∘ σf)).Perm (List.ofFn (g ∘ σg)) :=
    (Equiv.Perm.ofFn_comp_perm σf f).trans
      (hperm.trans (Equiv.Perm.ofFn_comp_perm σg g).symm)
  have heq : f ∘ σf = g ∘ σg :=
    List.ofFn_injective
      (List.Perm.eq_of_sortedLE hfmon.sortedLE_ofFn hgmon.sortedLE_ofFn hperm2)
  refine ⟨σg.symm.trans σf, funext (fun k => ?_)⟩
  change g ((σg.symm.trans σf)⁻¹ • k) = f k
  rw [Equiv.Perm.smul_def, Equiv.Perm.coe_inv, Equiv.symm_trans_apply, Equiv.symm_symm]
  have h1 := congr_fun heq (σf.symm k)
  simp only [Function.comp, Equiv.apply_symm_apply] at h1
  exact h1.symm

/-- The symmetric multiset of values of a function is unchanged by permuting
the function's domain. -/
lemma sym_ofFn_smul_perm (f : Fin n → Fin d) (σ : Equiv.Perm (Fin n)) :
    (⟨Multiset.ofList (List.ofFn (σ • f)), by simp⟩ : Sym (Fin d) n) =
      ⟨Multiset.ofList (List.ofFn f), by simp⟩ := by
  apply Sym.ext
  simp only [Sym.coe_mk]
  exact Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm σ.symm f)

/-- Two functions lie in the same permutation orbit exactly when they determine
the same symmetric multiset of values. -/
lemma symOfFn_eq_iff_permFun_orbit_rel (f g : Fin n → Fin d) :
    (⟨Multiset.ofList (List.ofFn f), by simp⟩ : Sym (Fin d) n) =
      ⟨Multiset.ofList (List.ofFn g), by simp⟩ ↔
    MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d) f g := by
  constructor
  · intro h
    apply permFun_orbitRel_of_list_ofFn_perm
    have hmultiset :
        Multiset.ofList (List.ofFn f) = Multiset.ofList (List.ofFn g) := by
      simpa only [Sym.coe_mk] using congr_arg Sym.toMultiset h
    exact Multiset.coe_eq_coe.mp hmultiset
  · intro hfg
    have hfg' : f ∈ MulAction.orbit (Equiv.Perm (Fin n)) g :=
      MulAction.orbitRel_apply.mp hfg
    rw [MulAction.mem_orbit_iff] at hfg'
    obtain ⟨σ, hσ⟩ := hfg'
    rw [← hσ]
    exact sym_ofFn_smul_perm g σ

private lemma list_ofFn_get_of_length_eq {α : Type*} (l : List α) {n : ℕ}
    (h : l.length = n) :
    (List.ofFn fun i : Fin n => l.get ⟨i.val, by omega⟩) = l := by
  subst n
  simp

/-- A symmetric multiset is represented by reading off the elements of any
chosen list representative. -/
lemma symOfFn_getToList_eq {α : Type*} (s : Sym α n) :
    (⟨Multiset.ofList (List.ofFn fun i : Fin n => s.val.toList.get ⟨i.val, by
      have hlen : s.val.toList.length = n := by
        rw [Multiset.length_toList]
        exact_mod_cast s.2
      omega⟩), by simp⟩ : Sym α n) = s := by
  have hlen : s.val.toList.length = n := by
    rw [Multiset.length_toList]
    exact_mod_cast s.2
  apply Sym.ext
  simp only [Sym.coe_mk]
  rw [list_ofFn_get_of_length_eq s.val.toList hlen]
  exact Multiset.coe_toList s.val

/-- Orbits of functions `Fin n → Fin d` under domain permutations are the
same data as multisets of `n` elements of `Fin d`. -/
noncomputable def permFunOrbitsEquivSym (d n : ℕ) :
    Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)) ≃
      Sym (Fin d) n := by
  let toSymFn : (Fin n → Fin d) → Sym (Fin d) n :=
    fun f => ⟨Multiset.ofList (List.ofFn f), by simp⟩
  apply Equiv.ofBijective (Quotient.lift toSymFn (fun f g hfg => by
    exact (symOfFn_eq_iff_permFun_orbit_rel f g).mpr hfg))
  constructor
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn with | h f =>
    induction q₂ using Quotient.inductionOn with | h g =>
    apply Quotient.sound
    exact (symOfFn_eq_iff_permFun_orbit_rel f g).mp h
  · intro s
    use Quotient.mk _ (fun i : Fin n => s.val.toList.get ⟨i.val, by
      have hlen : s.val.toList.length = n := by
        rw [Multiset.length_toList]
        exact_mod_cast s.2
      omega⟩)
    exact symOfFn_getToList_eq s

/-- Orbits of functions `Fin n → Fin d` under domain permutations are classified
by multisets of length `n`, hence counted by stars and bars. -/
lemma card_permFunOrbits_eq_choose (d n : ℕ) [NeZero d]
    [DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r] :
    Fintype.card (Quotient (MulAction.orbitRel
      (Equiv.Perm (Fin n)) (Fin n → Fin d))) =
    Nat.choose (n + d - 1) (d - 1) := by
  rw [show Nat.choose (n + d - 1) (d - 1) = Fintype.card (Sym (Fin d) n) from
    (card_sym_fin_eq_choose d n).symm]
  exact Fintype.card_congr (permFunOrbitsEquivSym d n)

end PermFunctionAction

section PermFunctionActionGeneral

/-- The natural position-permutation action used for strings with arbitrary codomain. -/
local instance permFinAction' (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n) :=
  Equiv.Perm.applyMulAction _

/-- The action on functions with arbitrary codomain induced by permuting the finite domain. -/
local instance permFunAction' (β : Type*) (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n → β) :=
  arrowAction

/-- **Orbit count, arbitrary finite codomain** (generalizes `card_permFunOrbits_eq_choose`
from `Fin d` to any `Fintype β`): the orbits of `Sₙ` acting on `Fin n → β` by domain
permutation are counted by stars-and-bars on `Fintype.card β` symbols. Proved by transporting
through a chosen equivalence `β ≃ Fin (Fintype.card β)`, which is equivariant for the
domain-permutation (`arrowAction`) action since it only postcomposes the codomain. -/
lemma card_permFunOrbits_eq_choose_of_fintype {β : Type*} [Fintype β]
    (n : ℕ) [NeZero (Fintype.card β)]
    [DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β)).r] :
    Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β))) =
      Nat.choose (n + Fintype.card β - 1) (Fintype.card β - 1) := by
  set d := Fintype.card β with hd
  let e : β ≃ Fin d := Fintype.equivFin β
  let hdec : DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r :=
    permFunOrbitRelDecidable d n
  rw [← card_permFunOrbits_eq_choose d n]
  apply Fintype.card_congr
  apply Quotient.congr (Equiv.arrowCongr (Equiv.refl (Fin n)) e)
  intro f g
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, funext fun k => ?_⟩
    have hk : g (σ⁻¹ • k) = f k := congr_fun hσ k
    change e (g (σ⁻¹ • k)) = e (f k)
    rw [hk]
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, funext fun k => ?_⟩
    have hk : e (g (σ⁻¹ • k)) = e (f k) := congr_fun hσ k
    exact e.injective hk

/-- Generalization of `mem_fixedBy_perm_arrow_iff` to an arbitrary codomain `β`. -/
lemma mem_fixedBy_perm_arrow_iff' {β : Type*} (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → β) :
    f ∈ MulAction.fixedBy (Fin n → β) σ ↔ f ∘ ⇑σ = f := by
  rw [MulAction.mem_fixedBy]
  constructor
  · intro hf
    funext k
    have h : f (σ.symm (σ k)) = f (σ k) := congr_fun hf (σ k)
    simp only [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro hf
    funext k
    change f (σ.symm k) = f k
    have h := congr_fun hf (σ.symm k)
    simp only [Function.comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- Generalization of `card_fixedBy_perm_arrow_eq_filter_card` to an arbitrary finite
codomain `β`. -/
lemma card_fixedBy_perm_arrow_eq_filter_card' {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (Fin n → β) σ) =
      (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f)).card := by
  rw [← Fintype.card_coe (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f))]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_fixedBy_perm_arrow_iff' n σ f).mp hf⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact (mem_fixedBy_perm_arrow_iff' n σ f).mpr hf⟩
    left_inv := fun ⟨f, _⟩ => by simp
    right_inv := fun ⟨f, _⟩ => by simp
  }

/-- **Burnside sum, arbitrary finite codomain** (generalizes `sum_permRep_trace_eq`'s
combinatorial core to any `Fintype β`): the total number of `σ`-fixed functions
`Fin n → β`, summed over `σ ∈ Sₙ`, is `n! · C(n + |β| - 1, |β| - 1)`. -/
lemma sum_card_fixedBy_permFun_eq_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) [NeZero (Fintype.card β)] :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f)).card =
      n.factorial * Nat.choose (n + Fintype.card β - 1) (Fintype.card β - 1) := by
  let : DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β)).r := by
    intro f g
    simp only [MulAction.orbitRel_apply]
    rw [MulAction.mem_orbit_iff]
    exact Fintype.decidableExistsFintype
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin n)) (Fin n → β)
  rw [show Fintype.card (Equiv.Perm (Fin n)) = n.factorial from
    (Fintype.card_perm).trans (by simp [Fintype.card_fin])] at burnside
  simp_rw [← card_fixedBy_perm_arrow_eq_filter_card' n]
  rw [burnside, card_permFunOrbits_eq_choose_of_fintype n, mul_comm]

end PermFunctionActionGeneral

end Math.RepresentationTheory

end
