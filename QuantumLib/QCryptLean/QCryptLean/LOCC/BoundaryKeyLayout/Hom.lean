import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Hom -/


open scoped Matrix BigOperators

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace BoundaryKeyLayout

/-- A **morphism of boundary key layouts** from `L₂` to `L₁`.

It is a map of complete output spaces together with an injective renaming of complete public
exits, one common bijection of the key alphabet applied to both of Alice's and Bob's key
coordinates, and an arbitrary map of retained coordinates, such that the output map acts on the
explicit layout coordinates as these three maps. -/
structure Hom {B₂ B₁ : Boundary P} (L₂ : BoundaryKeyLayout B₂) (L₁ : BoundaryKeyLayout B₁) where
  /-- The underlying map of complete output spaces. -/
  toFun : B₂.space → B₁.space
  /-- The renaming of complete public exits. -/
  exit : B₂.Exit → B₁.Exit
  /-- Distinct complete public exits stay distinct. -/
  exit_injective : Function.Injective exit
  /-- The common relabelling of both key coordinates at each exit. -/
  key : ∀ e, (L₂.disposition e).Key ≃ (L₁.disposition (exit e)).Key
  /-- The map of retained coordinates at each exit. -/
  residual : ∀ e, L₂.Residual e → L₁.Residual (exit e)
  /-- In the explicit coordinates the output map renames the exit and applies `key`, `key` and
  `residual` to the three output coordinates. -/
  apply_coordinates_symm' : ∀ (e : B₂.Exit)
      (c : (L₂.disposition e).Key × (L₂.disposition e).Key × L₂.Residual e),
    toFun ⟨e, (L₂.coordinates e).symm c⟩ =
      ⟨exit e, (L₁.coordinates (exit e)).symm (key e c.1, key e c.2.1, residual e c.2.2)⟩

namespace Hom

variable {B₁ B₂ B₃ : Boundary P} {L₁ : BoundaryKeyLayout B₁} {L₂ : BoundaryKeyLayout B₂}
  {L₃ : BoundaryKeyLayout B₃}

instance : CoeFun (Hom L₂ L₁) fun _ => B₂.space → B₁.space :=
  ⟨Hom.toFun⟩

/-- The coordinate formula of a morphism, in the coercion form. -/
theorem apply_coordinates_symm (φ : Hom L₂ L₁) (e : B₂.Exit)
    (c : (L₂.disposition e).Key × (L₂.disposition e).Key × L₂.Residual e) :
    φ ⟨e, (L₂.coordinates e).symm c⟩ =
      ⟨φ.exit e, (L₁.coordinates (φ.exit e)).symm
        (φ.key e c.1, φ.key e c.2.1, φ.residual e c.2.2)⟩ :=
  φ.apply_coordinates_symm' e c

/-- A morphism maps each complete output to the renamed exit. -/
theorem apply_fst (φ : Hom L₂ L₁) (x : B₂.space) : (φ x).1 = φ.exit x.1 := by
  obtain ⟨e, q⟩ := x
  have h := φ.apply_coordinates_symm e (L₂.coordinates e q)
  rw [Equiv.symm_apply_apply] at h
  rw [h]

/-- The forward coordinate formula: the layout coordinates of an image point are the relabelled
coordinates of the source point. -/
theorem spaceCoordinates_apply (φ : Hom L₂ L₁) (x : B₂.space) :
    L₁.spaceCoordinates (φ x) =
      ⟨φ.exit x.1, (φ.key x.1 (L₂.coordinates x.1 x.2).1,
        φ.key x.1 (L₂.coordinates x.1 x.2).2.1, φ.residual x.1 (L₂.coordinates x.1 x.2).2.2)⟩ := by
  obtain ⟨e, q⟩ := x
  have h := φ.apply_coordinates_symm e (L₂.coordinates e q)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  simp only [BoundaryKeyLayout.spaceCoordinates_apply, Equiv.apply_symm_apply]

/-- The identity morphism of a boundary key layout. -/
protected def id (L : BoundaryKeyLayout B₁) : Hom L L where
  toFun := id
  exit := id
  exit_injective := Function.injective_id
  key _ := Equiv.refl _
  residual _ := id
  apply_coordinates_symm' _ _ := rfl

@[simp] theorem coe_id (L : BoundaryKeyLayout B₁) : ⇑(Hom.id L) = id := rfl

/-- Composition of morphisms of boundary key layouts. -/
def comp (φ : Hom L₂ L₁) (ψ : Hom L₃ L₂) : Hom L₃ L₁ where
  toFun x := φ (ψ x)
  exit e := φ.exit (ψ.exit e)
  exit_injective := φ.exit_injective.comp ψ.exit_injective
  key e := (ψ.key e).trans (φ.key (ψ.exit e))
  residual e u := φ.residual (ψ.exit e) (ψ.residual e u)
  apply_coordinates_symm' e c := by
    rw [ψ.apply_coordinates_symm, φ.apply_coordinates_symm]
    rfl

@[simp] theorem coe_comp (φ : Hom L₂ L₁) (ψ : Hom L₃ L₂) : ⇑(φ.comp ψ) = φ ∘ ψ := rfl

theorem comp_apply (φ : Hom L₂ L₁) (ψ : Hom L₃ L₂) (x : B₃.space) :
    φ.comp ψ x = φ (ψ x) := rfl


/-- **The ideal key resource is natural along morphisms**, entrywise.

Every complete public exit, both ordered keys and the retained coordinate are kept; no state,
positivity or reachability hypothesis is used. -/
theorem ideal_apply (φ : Hom L₂ L₁) (ρ : Op B₁.space) (x y : B₂.space) :
    L₁.ideal ρ (φ x) (φ y) = L₂.ideal (ρ.submatrix φ φ) x y := by
  obtain ⟨e, p⟩ := x
  obtain ⟨f, q⟩ := y
  rcases hp : L₂.coordinates e p with ⟨a, b, u⟩
  rcases hq : L₂.coordinates f q with ⟨a', b', v⟩
  obtain rfl : p = (L₂.coordinates e).symm (a, b, u) := by
    rw [← hp, Equiv.symm_apply_apply]
  obtain rfl : q = (L₂.coordinates f).symm (a', b', v) := by
    rw [← hq, Equiv.symm_apply_apply]
  rw [φ.apply_coordinates_symm, φ.apply_coordinates_symm]
  by_cases hef : e = f
  · subst hef
    rw [L₁.ideal_coordinate_entry, L₂.ideal_coordinate_entry,
      Fintype.card_congr (φ.key e)]
    simp only [(φ.key e).apply_eq_iff_eq]
    split_ifs
    · refine congrArg _ ((Fintype.sum_equiv (φ.key e) _ _ fun oldA => ?_).symm)
      refine Fintype.sum_equiv (φ.key e) _ _ fun oldB => ?_
      rw [Matrix.submatrix_apply, φ.apply_coordinates_symm, φ.apply_coordinates_symm]
    · rfl
  · rw [L₁.ideal_crossExit_zero ρ (φ.exit_injective.ne hef), L₂.ideal_crossExit_zero _ hef]

/-- **The ideal key resource is natural along morphisms**: pulling back along a morphism
commutes with the two resources. -/
theorem ideal_submatrix (φ : Hom L₂ L₁) (ρ : Op B₁.space) :
    (L₁.ideal ρ).submatrix φ φ = L₂.ideal (ρ.submatrix φ φ) := by
  ext x y
  exact φ.ideal_apply ρ x y

/-- Changing the two key coordinates of a point neither enters nor leaves the image of a
morphism. -/
theorem mk_coordinates_symm_mem_range (φ : Hom L₂ L₁) {f : B₁.Exit}
    {a b : (L₁.disposition f).Key} {w : L₁.Residual f}
    (h : (⟨f, (L₁.coordinates f).symm (a, b, w)⟩ : B₁.space) ∈ Set.range φ)
    (a' b' : (L₁.disposition f).Key) :
    (⟨f, (L₁.coordinates f).symm (a', b', w)⟩ : B₁.space) ∈ Set.range φ := by
  obtain ⟨⟨e, p⟩, hp⟩ := h
  rcases hc : L₂.coordinates e p with ⟨a₀, b₀, u⟩
  obtain rfl : p = (L₂.coordinates e).symm (a₀, b₀, u) := by
    rw [← hc, Equiv.symm_apply_apply]
  rw [φ.apply_coordinates_symm] at hp
  obtain ⟨rfl, hw⟩ := Sigma.mk.inj_iff.mp hp
  have hw' := congrArg (fun z => z.2.2) ((L₁.coordinates _).symm.injective (eq_of_heq hw))
  refine ⟨⟨e, (L₂.coordinates e).symm ((φ.key e).symm a', (φ.key e).symm b', u)⟩, ?_⟩
  rw [φ.apply_coordinates_symm]
  simp only [Equiv.apply_symm_apply]
  exact congrArg (fun r => (⟨φ.exit e, (L₁.coordinates (φ.exit e)).symm (a', b', r)⟩ : B₁.space))
    hw'

/-- The ideal of an operator supported on the image of a morphism vanishes off that image. -/
theorem ideal_apply_eq_zero_of_notMem_range (φ : Hom L₂ L₁) {M : Op B₁.space}
    (hM : ∀ y z, (y ∉ Set.range φ ∨ z ∉ Set.range φ) → M y z = 0) {y z : B₁.space}
    (hyz : y ∉ Set.range φ ∨ z ∉ Set.range φ) :
    L₁.ideal M y z = 0 := by
  obtain ⟨f, p⟩ := y
  obtain ⟨g, q⟩ := z
  by_cases hfg : f = g
  · subst hfg
    rcases hp : L₁.coordinates f p with ⟨a, b, w⟩
    rcases hq : L₁.coordinates f q with ⟨a', b', w'⟩
    obtain rfl : p = (L₁.coordinates f).symm (a, b, w) := by
      rw [← hp, Equiv.symm_apply_apply]
    obtain rfl : q = (L₁.coordinates f).symm (a', b', w') := by
      rw [← hq, Equiv.symm_apply_apply]
    rw [L₁.ideal_coordinate_entry]
    split_ifs
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun oldA _ =>
        Finset.sum_eq_zero fun oldB _ => hM _ _ ?_)
      refine hyz.imp (fun hy hmem => hy ?_) (fun hz hmem => hz ?_)
      · exact φ.mk_coordinates_symm_mem_range hmem a b
      · exact φ.mk_coordinates_symm_mem_range hmem a' b'
    · rfl
  · exact L₁.ideal_crossExit_zero M hfg p q

/-- **An operator supported on the image of a morphism is idealized through its pullback.**

For two operators vanishing off the image of `φ`, the target ideal sends one to the other exactly
when the source ideal sends their pullbacks to one another. -/
theorem ideal_eq_iff (φ : Hom L₂ L₁) {M M' : Op B₁.space}
    (hM : ∀ y z, (y ∉ Set.range φ ∨ z ∉ Set.range φ) → M y z = 0)
    (hM' : ∀ y z, (y ∉ Set.range φ ∨ z ∉ Set.range φ) → M' y z = 0) :
    L₁.ideal M = M' ↔ L₂.ideal (M.submatrix φ φ) = M'.submatrix φ φ := by
  constructor
  · rintro rfl
    exact (φ.ideal_submatrix M).symm
  · intro h
    ext y z
    by_cases hyz : y ∈ Set.range φ ∧ z ∈ Set.range φ
    · obtain ⟨⟨x, rfl⟩, ⟨x', rfl⟩⟩ := hyz
      rw [φ.ideal_apply, h, Matrix.submatrix_apply]
    · have hyz' : y ∉ Set.range φ ∨ z ∉ Set.range φ := not_and_or.mp hyz
      rw [φ.ideal_apply_eq_zero_of_notMem_range hM hyz', hM' y z hyz']


/-- A key/key/residual coordinate read through explicit identifications of its three types. -/
private theorem prod3_eq_of_heq {K₁ K₂ R₁ R₂ : Type} (hK : K₁ = K₂) (hR : R₁ = R₂)
    {x : K₁ × K₁ × R₁} {y : K₂ × K₂ × R₂} (h : x ≍ y) :
    x = ((Equiv.cast hK).symm y.1, (Equiv.cast hK).symm y.2.1,
      (Equiv.cast hR).symm y.2.2) := by
  subst hK
  subst hR
  obtain rfl := eq_of_heq h
  rfl

/-- **A fibre inclusion with the same local data is a morphism.**

`V` carries every complete exit fibre of `B₂` into the exit `F e` of `B₁`, where the disposition
and retained type are those of `e` and the layout coordinates are the same values. The key and
residual maps of the morphism are the identifications along these type equalities. -/
def ofHEq (V : B₂.space → B₁.space) (F : B₂.Exit → B₁.Exit) (hF : Function.Injective F)
    (hVfst : ∀ x, (V x).1 = F x.1)
    (hdisp : ∀ e, L₁.disposition (F e) = L₂.disposition e)
    (hres : ∀ e, L₁.Residual (F e) = L₂.Residual e)
    (hcoord : ∀ x, L₁.coordinates (V x).1 (V x).2 ≍ L₂.coordinates x.1 x.2) :
    Hom L₂ L₁ where
  toFun := V
  exit := F
  exit_injective := hF
  key e := (Equiv.cast (congrArg Disposition.Key (hdisp e))).symm
  residual e := (Equiv.cast (hres e)).symm
  apply_coordinates_symm' e c := by
    show V ⟨e, (L₂.coordinates e).symm c⟩ = _
    have h1 := hVfst ⟨e, (L₂.coordinates e).symm c⟩
    have h2 := hcoord ⟨e, (L₂.coordinates e).symm c⟩
    simp only [Equiv.apply_symm_apply] at h2
    generalize V ⟨e, (L₂.coordinates e).symm c⟩ = w at h1 h2 ⊢
    obtain ⟨f, q⟩ := w
    obtain rfl : f = F e := h1
    refine congrArg (Sigma.mk (F e)) ((L₁.coordinates (F e)).injective ?_)
    rw [Equiv.apply_symm_apply]
    exact prod3_eq_of_heq (congrArg Disposition.Key (hdisp e)) (hres e) h2

@[simp] theorem coe_ofHEq (V : B₂.space → B₁.space) (F : B₂.Exit → B₁.Exit)
    (hF : Function.Injective F) (hVfst : ∀ x, (V x).1 = F x.1)
    (hdisp : ∀ e, L₁.disposition (F e) = L₂.disposition e)
    (hres : ∀ e, L₁.Residual (F e) = L₂.Residual e)
    (hcoord : ∀ x, L₁.coordinates (V x).1 (V x).2 ≍ L₂.coordinates x.1 x.2) :
    ⇑(ofHEq V F hF hVfst hdisp hres hcoord) = V := rfl

end Hom


variable {B : Boundary P} (L : BoundaryKeyLayout B)

/-- **Ambient commutation of the boundary-native ideal key resource with a structured relabel.**

`R` is an arbitrary permutation of the complete output space, `F` an arbitrary permutation of the
complete public exits, and `kappa e` an arbitrary bijection from the key alphabet at `e` to the key
alphabet at `F e`. The single hypothesis says that in the layout's own explicit coordinates `R`
sends the point over `e` with keys `(a, b)` to the point over `F e` with keys
`(kappa e a, kappa e b)` — the same bijection on both parties' key registers — and that the
residual coordinate at `F e` is determined (it is quantified over, so the hypothesis also records
that the residual alphabet at a relabelled exit is a subsingleton). Then `R` is an endomorphism
of the layout and `Hom.ideal_submatrix` applies.

Both defining features of the resource are used: full public-exit pinching (through `F` being a
permutation) and the uniform shared-key replacement inside one exit (through one common `kappa`). -/
theorem ideal_submatrix_comm [∀ e, Nonempty (L.Residual e)]
    (R : Equiv.Perm B.space) (F : Equiv.Perm B.Exit)
    (kappa : ∀ e : B.Exit, (L.disposition e).Key ≃ (L.disposition (F e)).Key)
    (hcoord : ∀ (x : B.space) (v : L.Residual (F x.1)),
      L.spaceCoordinates (R x) =
        ⟨F x.1, (kappa x.1 (L.coordinates x.1 x.2).1,
          kappa x.1 (L.coordinates x.1 x.2).2.1, v)⟩)
    (rho : Op B.space) :
    L.ideal (rho.submatrix R R) = (L.ideal rho).submatrix R R := by
  refine (Hom.ideal_submatrix
    { toFun := R
      exit := F
      exit_injective := F.injective
      key := kappa
      residual := fun e _ => (inferInstance : Nonempty (L.Residual (F e))).some
      apply_coordinates_symm' := fun e c => ?_ } rho).symm
  apply L.spaceCoordinates.injective
  have hx := hcoord ⟨e, (L.coordinates e).symm c⟩ (inferInstance : Nonempty (L.Residual (F e))).some
  simp only [Equiv.apply_symm_apply] at hx
  rw [hx]
  simp only [spaceCoordinates_apply, Equiv.apply_symm_apply]

/-- Componentwise form of `ideal_submatrix_comm`.

The relabel is described by its action on complete public exits (`hfst`) and on the two key
coordinates (`hk1`, `hk2`, one common `kappa` on both parties), while the private residual
coordinate is a subsingleton (`hres`). This is the form the concrete retained layout supplies. -/
theorem ideal_submatrix_comm_of_keys
    (R : Equiv.Perm B.space) (F : Equiv.Perm B.Exit)
    (kappa : ∀ e : B.Exit, (L.disposition e).Key ≃ (L.disposition (F e)).Key)
    (hres : ∀ (e : B.Exit) (u v : L.Residual e), u = v)
    (hfst : ∀ x : B.space, (R x).1 = F x.1)
    (hk1 : ∀ x : B.space,
      (L.coordinates (R x).1 (R x).2).1 ≍ kappa x.1 (L.coordinates x.1 x.2).1)
    (hk2 : ∀ x : B.space,
      (L.coordinates (R x).1 (R x).2).2.1 ≍ kappa x.1 (L.coordinates x.1 x.2).2.1)
    (rho : Op B.space) :
    L.ideal (rho.submatrix R R) = (L.ideal rho).submatrix R R := by
  classical
  have key : ∀ (y : B.space) (f : B.Exit), y.1 = f →
      ∀ (a b : (L.disposition f).Key) (v : L.Residual f),
        (L.coordinates y.1 y.2).1 ≍ a → (L.coordinates y.1 y.2).2.1 ≍ b →
        L.spaceCoordinates y = ⟨f, (a, b, v)⟩ := by
    intro y f hf a b v h1 h2
    subst hf
    rw [L.spaceCoordinates_apply]
    refine congrArg (Sigma.mk y.1) ?_
    exact Prod.ext (eq_of_heq h1) (Prod.ext (eq_of_heq h2) (hres _ _ _))
  let residual (e : B.Exit) (u : L.Residual e) : L.Residual (F e) :=
    let x : B.space := ⟨e, (L.coordinates e).symm (Classical.arbitrary _,
      Classical.arbitrary _, u)⟩
    cast (congrArg L.Residual (hfst x)) (L.coordinates (R x).1 (R x).2).2.2
  refine (Hom.ideal_submatrix
    { toFun := R
      exit := F
      exit_injective := F.injective
      key := kappa
      residual := residual
      apply_coordinates_symm' := fun e c => ?_ } rho).symm
  apply L.spaceCoordinates.injective
  have hx := key (R ⟨e, (L.coordinates e).symm c⟩) (F e) (hfst _)
    _ _ (residual e c.2.2) (hk1 _) (hk2 _)
  simpa only [spaceCoordinates_apply, Equiv.apply_symm_apply] using hx

end BoundaryKeyLayout

end LOCC
