import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Math.Logic.HEqUnit
import QCryptLean.Quantum.Operators.Basic

/-! # Relabel -/


open scoped Matrix BigOperators

open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC


variable {P : Type} [Fintype P] [DecidableEq P]

namespace BoundaryRelabel

/-- Transport of a joint register along an equality of multipartite systems. -/
abbrev systemTotalCast {R R' : MultipartiteSystem P} (h : R = R') : R.total ≃ R'.total :=
  Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h)

theorem systemTotalCast_symm_heq {R R' : MultipartiteSystem P} (h : R = R') (q : R'.total) :
    (systemTotalCast h).symm q ≍ q := by
  subst h
  rfl

/-- Registers of heterogeneously equal joint coordinates over equal multipartite systems. -/
theorem heq_apply_of_system_eq {R R' : MultipartiteSystem P} (h : R = R') {q : R.total} {q' :
    R'.total}
    (hq : q ≍ q') (p : P) : q p ≍ q' p := by
  subst h
  rw [eq_of_heq hq]

end BoundaryRelabel

open BoundaryRelabel


/-- A boundary key layout whose two key coordinates are the named laboratories' own registers and
whose retained coordinate is trivial. -/
structure BoundaryKeyLayout.RegisterKeyed {B : Boundary P} (L : BoundaryKeyLayout B) (a b : P) :
    Prop where
  /-- The retained coordinate carries no information. -/
  residual : ∀ e : B.Exit, Subsingleton (L.Residual e)
  /-- Alice's key coordinate is her own register. -/
  aliceKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).1 ≍ q a
  /-- Bob's key coordinate is his own register. -/
  bobKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).2.1 ≍ q b

namespace BoundaryKeyLayout.RegisterKeyed

variable {B : Boundary P} {L : BoundaryKeyLayout B} {a b : P}

/-- The key alphabet at a complete exit is Alice's own register there. -/
theorem key_eq (h : RegisterKeyed L a b) (e : B.Exit) [Nonempty (B.system e).total] :
    (L.disposition e).Key = (B.system e).reg a := by
  let : Nonempty (B.system e).total := inferInstance
  obtain ⟨q⟩ := (inferInstance : Nonempty (B.system e).total)
  exact type_eq_of_heq (h.aliceKey e q)

/-- The key alphabet at a complete exit is Bob's own register there. The mirror of `key_eq`; on an
accepting exit it says the two parties hold registers of the *same* key alphabet, and on an
aborting exit that both hold the trivial one. -/
theorem key_eq_bob (h : RegisterKeyed L a b) (e : B.Exit) [Nonempty (B.system e).total] :
    (L.disposition e).Key = (B.system e).reg b := by
  obtain ⟨q⟩ := (inferInstance : Nonempty (B.system e).total)
  exact type_eq_of_heq (h.bobKey e q)

/-- The key alphabet and Alice's register have the same cardinality. -/
theorem card_key (h : RegisterKeyed L a b) (e : B.Exit) [Nonempty (B.system e).total] :
    Fintype.card ((L.disposition e).Key) = Fintype.card ((B.system e).reg a) :=
  Fintype.card_congr (Equiv.cast (h.key_eq e))

/-- Alice's and Bob's key coordinates agree exactly when their registers do. -/
theorem alice_eq_bob_iff (h : RegisterKeyed L a b) (e : B.Exit) (q : (B.system e).total) :
    (L.coordinates e q).1 = (L.coordinates e q).2.1 ↔ q a ≍ q b := by
  constructor
  · intro hq
    exact ((h.aliceKey e q).symm.trans (hq ▸ (h.bobKey e q))).symm.symm
  · intro hq
    exact eq_of_heq ((h.aliceKey e q).trans (hq.trans (h.bobKey e q).symm))

/-- Alice's key coordinates at two points agree exactly when her registers do. -/
theorem alice_eq_alice_iff (h : RegisterKeyed L a b) (e : B.Exit) (q q' : (B.system e).total) :
    (L.coordinates e q).1 = (L.coordinates e q').1 ↔ q a ≍ q' a := by
  constructor
  · intro hq
    exact ((h.aliceKey e q).symm.trans (hq ▸ (h.aliceKey e q'))).symm.symm
  · intro hq
    exact eq_of_heq ((h.aliceKey e q).trans (hq.trans (h.aliceKey e q').symm))

/-- Enumerating one exit fibre by its two key coordinates. -/
noncomputable def fibreEquiv (h : RegisterKeyed L a b) (e : B.Exit) [Nonempty (L.Residual e)] :
    (L.disposition e).Key × (L.disposition e).Key ≃ (B.system e).total :=
  letI : Subsingleton (L.Residual e) := h.residual e
  letI : Unique (L.Residual e) := uniqueOfSubsingleton (Classical.arbitrary _)
  (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodUnique (L.disposition e).Key (L.Residual e)).symm).trans
    (L.coordinates e).symm

theorem fibreEquiv_apply (h : RegisterKeyed L a b) (e : B.Exit) [Nonempty (L.Residual e)]
    (k l : (L.disposition e).Key) (u : L.Residual e) :
    h.fibreEquiv e (k, l) = (L.coordinates e).symm (k, l, u) := by
  let : Subsingleton (L.Residual e) := h.residual e
  change (L.coordinates e).symm (k, l, _) = _
  exact congrArg (L.coordinates e).symm
    (congrArg (fun r => (k, l, r)) (Subsingleton.elim _ _))

/-- **Register-level entry formula for the boundary-derived ideal, on the agreeing diagonal.** -/
theorem ideal_apply_diag (h : RegisterKeyed L a b) (rho : Quantum.Operators.Op B.space)
    (e : B.Exit) (q q' : (B.system e).total)
    (hq : q a ≍ q b) (hq' : q' a ≍ q' b) (hqq : q a ≍ q' a) :
    L.ideal rho ⟨e, q⟩ ⟨e, q'⟩ =
      (((Fintype.card ((B.system e).reg a) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ p : (B.system e).total, rho ⟨e, p⟩ ⟨e, p⟩ := by
  let : Nonempty (B.system e).total := ⟨q⟩
  let : Nonempty (L.Residual e) := ⟨(L.coordinates e q).2.2⟩
  let : Subsingleton (L.Residual e) := h.residual e
  rcases hc : L.coordinates e q with ⟨A, Bk, u⟩
  rcases hc' : L.coordinates e q' with ⟨A', Bk', u'⟩
  have hqe : q = (L.coordinates e).symm (A, Bk, u) := by rw [← hc]; simp
  have hqe' : q' = (L.coordinates e).symm (A', Bk', u') := by rw [← hc']; simp
  have hAB : A = Bk := by
    have := (h.alice_eq_bob_iff e q).mpr hq
    rw [hc] at this
    exact this
  have hAB' : A' = Bk' := by
    have := (h.alice_eq_bob_iff e q').mpr hq'
    rw [hc'] at this
    exact this
  have hAA : A = A' := by
    have := (h.alice_eq_alice_iff e q q').mpr hqq
    rw [hc, hc'] at this
    exact this
  rw [hqe, hqe', L.ideal_coordinate_entry, ite_eq_left ⟨hAB, hAB', hAA⟩, h.card_key e]
  refine congrArg (fun z : ℂ => (((Fintype.card ((B.system e).reg a) : ℝ)⁻¹ : ℝ) : ℂ) * z) ?_
  have hprod := Fintype.sum_prod_type
    (f := fun z : (L.disposition e).Key × (L.disposition e).Key =>
      rho (⟨e, (L.coordinates e).symm (z.1, z.2, u)⟩ : B.space)
        (⟨e, (L.coordinates e).symm (z.1, z.2, u')⟩ : B.space))
  rw [← hprod]
  refine Fintype.sum_equiv (h.fibreEquiv e) _ _ ?_
  intro z
  obtain ⟨k, l⟩ := z
  have huu : (L.coordinates e).symm (k, l, u') = (L.coordinates e).symm (k, l, u) :=
    congrArg (L.coordinates e).symm
      (congrArg (fun r => (k, l, r)) (Subsingleton.elim u' u))
  simp only []
  rw [huu, h.fibreEquiv_apply e k l u]

/-- The boundary-derived ideal vanishes off the agreeing diagonal. -/
theorem ideal_apply_zero (h : RegisterKeyed L a b) (rho : Quantum.Operators.Op B.space)
    (x y : B.space)
    (hne : ¬ (x.1 = y.1 ∧ (x.2 a ≍ x.2 b) ∧ (y.2 a ≍ y.2 b) ∧ (x.2 a ≍ y.2 a))) :
    L.ideal rho x y = 0 := by
  classical
  obtain ⟨e, q⟩ := x
  obtain ⟨f, q'⟩ := y
  by_cases hef : e = f
  · subst hef
    let : Subsingleton (L.Residual e) := h.residual e
    rcases hc : L.coordinates e q with ⟨A, Bk, u⟩
    rcases hc' : L.coordinates e q' with ⟨A', Bk', u'⟩
    have hqe : q = (L.coordinates e).symm (A, Bk, u) := by rw [← hc]; simp
    have hqe' : q' = (L.coordinates e).symm (A', Bk', u') := by rw [← hc']; simp
    rw [hqe, hqe', L.ideal_coordinate_entry, ite_eq_right]
    rintro ⟨hAB, hAB', hAA⟩
    refine hne ⟨rfl, ?_, ?_, ?_⟩
    · refine (h.alice_eq_bob_iff e q).mp ?_
      rw [hc]
      exact hAB
    · refine (h.alice_eq_bob_iff e q').mp ?_
      rw [hc']
      exact hAB'
    · refine (h.alice_eq_alice_iff e q q').mp ?_
      rw [hc, hc']
      exact hAA
  · exact L.ideal_crossExit_zero rho hef q q'

end BoundaryKeyLayout.RegisterKeyed


/-- An **exit-renaming register relabelling** of boundary output spaces: complete public exits are
renamed injectively, corresponding exits carry the same multipartite system, and every joint
register coordinate is transported unchanged. -/
structure Boundary.ExitRenaming {B₁ B₂ : Boundary P} (Θ : B₁.space ≃ B₂.space) where
  /-- The induced renaming of complete public exits. -/
  exits : B₁.Exit → B₂.Exit
  /-- Distinct complete public exits stay distinct. -/
  exits_inj : Function.Injective exits
  /-- Renamed complete exits carry the same multipartite system. -/
  systems : ∀ g : B₁.Exit, B₂.system (exits g) = B₁.system g
  /-- The relabelling renames the complete public exit. -/
  fst : ∀ x : B₁.space, (Θ x).1 = exits x.1
  /-- The relabelling leaves the joint register coordinate unchanged. -/
  snd : ∀ x : B₁.space, (Θ x).2 ≍ x.2

namespace Boundary.ExitRenaming

variable {B₁ B₂ B₃ : Boundary P}

/-- Explicit value of an exit-renaming register relabelling. -/
theorem sigma_eq {Θ : B₁.space ≃ B₂.space} (hΘ : Boundary.ExitRenaming Θ) (g : B₁.Exit)
    (p : (B₁.system g).total) :
    Θ ⟨g, p⟩ = ⟨hΘ.exits g, (systemTotalCast (hΘ.systems g)).symm p⟩ := by
  refine Sigma.ext (hΘ.fst ⟨g, p⟩) ?_
  exact (hΘ.snd ⟨g, p⟩).trans (systemTotalCast_symm_heq (hΘ.systems g) p).symm

/-- Composition of exit-renaming register relabellings. -/
def trans {Θ₁ : B₁.space ≃ B₂.space} {Θ₂ : B₂.space ≃ B₃.space}
    (h₁ : Boundary.ExitRenaming Θ₁) (h₂ : Boundary.ExitRenaming Θ₂) : Boundary.ExitRenaming
      (Θ₁.trans Θ₂) where
  exits g := h₂.exits (h₁.exits g)
  exits_inj := h₂.exits_inj.comp h₁.exits_inj
  systems g := (h₂.systems (h₁.exits g)).trans (h₁.systems g)
  fst x := by
    change (Θ₂ (Θ₁ x)).1 = _
    rw [h₂.fst (Θ₁ x), h₁.fst x]
  snd x := by
    change (Θ₂ (Θ₁ x)).2 ≍ _
    exact (h₂.snd (Θ₁ x)).trans (h₁.snd x)

/-- The exit renaming of an exit-renaming register relabelling is onto. -/
theorem exits_surjective [∀ e, Nonempty (B₂.system e).total] {Θ : B₁.space ≃ B₂.space} (hΘ :
  Boundary.ExitRenaming Θ) :
    Function.Surjective hΘ.exits := by
  intro g'
  obtain ⟨p⟩ := (inferInstance : Nonempty (B₂.system g').total)
  refine ⟨(Θ.symm ⟨g', p⟩).1, ?_⟩
  have h := hΘ.fst (Θ.symm ⟨g', p⟩)
  rw [Θ.apply_symm_apply] at h
  exact h.symm

/-- The exit renaming as a bijection of complete public exits. -/
noncomputable def exitEquiv [∀ e, Nonempty (B₂.system e).total] {Θ : B₁.space ≃ B₂.space} (hΘ :
  Boundary.ExitRenaming Θ) :
    B₁.Exit ≃ B₂.Exit :=
  Equiv.ofBijective hΘ.exits ⟨hΘ.exits_inj, hΘ.exits_surjective⟩

/-- The inverse of an exit-renaming register relabelling is one. -/
noncomputable def symm [∀ e, Nonempty (B₂.system e).total] {Θ : B₁.space ≃ B₂.space} (hΘ :
  Boundary.ExitRenaming Θ) :
    Boundary.ExitRenaming Θ.symm where
  exits := hΘ.exitEquiv.symm
  exits_inj := hΘ.exitEquiv.symm.injective
  systems g' := by
    have hE : hΘ.exits (hΘ.exitEquiv.symm g') = g' := hΘ.exitEquiv.apply_symm_apply g'
    have h := hΘ.systems (hΘ.exitEquiv.symm g')
    rw [hE] at h
    exact h.symm
  fst y := by
    have h := hΘ.fst (Θ.symm y)
    rw [Θ.apply_symm_apply] at h
    exact (hΘ.exitEquiv.symm_apply_eq.mpr h).symm
  snd y := by
    have h := hΘ.snd (Θ.symm y)
    rw [Θ.apply_symm_apply] at h
    exact h.symm

end Boundary.ExitRenaming

/-- **The boundary-derived ideal key resource is intertwined by an exit-renaming register
relabelling of two register-keyed layouts.** Every complete public exit, both ordered keys and
the entire retained coordinate are preserved; no state, positivity, classicality or reachability
hypothesis is used. -/
theorem BoundaryKeyLayout.ideal_reindexOp_of_exitRenaming {B₁ B₂ : Boundary P}
    {L₁ : BoundaryKeyLayout B₁} {L₂ : BoundaryKeyLayout B₂} {a b : P}
    (h₁ : RegisterKeyed L₁ a b) (h₂ : RegisterKeyed L₂ a b)
    {Θ : B₁.space ≃ B₂.space} (hΘ : Boundary.ExitRenaming Θ) (M : Quantum.Operators.Op
      B₁.space) :
    L₂.ideal ((Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap M) = (Matrix.reindexLinearEquiv ℂ ℂ Θ
      Θ).toLinearMap (L₁.ideal M) := by
  classical
  ext x' y'
  obtain ⟨x, rfl⟩ : ∃ x, Θ x = x' := ⟨Θ.symm x', Θ.apply_symm_apply x'⟩
  obtain ⟨y, rfl⟩ : ∃ y, Θ y = y' := ⟨Θ.symm y', Θ.apply_symm_apply y'⟩
  have hrhs : (Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap (L₁.ideal M) (Θ x) (Θ y) = L₁.ideal M
    x y := by
    exact congrArg₂ (L₁.ideal M) (Θ.symm_apply_apply x) (Θ.symm_apply_apply y)
  rw [hrhs]
  obtain ⟨g, q⟩ := x
  obtain ⟨f, q'⟩ := y
  have hpull : ∀ (e : B₁.Exit) (p : (B₂.system (hΘ.exits e)).total),
      Θ.symm ⟨hΘ.exits e, p⟩ = ⟨e, systemTotalCast (hΘ.systems e) p⟩ := by
    intro e p
    refine Θ.injective ?_
    rw [Θ.apply_symm_apply, hΘ.sigma_eq e (systemTotalCast (hΘ.systems e) p),
      Equiv.symm_apply_apply]
  by_cases hgf : g = f
  · subst hgf
    by_cases hd : (q a ≍ q b) ∧ (q' a ≍ q' b) ∧ (q a ≍ q' a)
    · obtain ⟨hq, hq', hqq⟩ := hd
      have hcq : (systemTotalCast (hΘ.systems g)).symm q ≍ q :=
        systemTotalCast_symm_heq (hΘ.systems g) q
      have hcq' : (systemTotalCast (hΘ.systems g)).symm q' ≍ q' :=
        systemTotalCast_symm_heq (hΘ.systems g) q'
      have hSystem := (hΘ.systems g).symm
      rw [hΘ.sigma_eq g q, hΘ.sigma_eq g q',
        h₂.ideal_apply_diag ((Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap M) (hΘ.exits g)
          ((systemTotalCast (hΘ.systems g)).symm q) ((systemTotalCast (hΘ.systems g)).symm q')
          ((heq_apply_of_system_eq hSystem hcq.symm a).symm.trans
            (hq.trans (heq_apply_of_system_eq hSystem hcq.symm b)))
          ((heq_apply_of_system_eq hSystem hcq'.symm a).symm.trans
            (hq'.trans (heq_apply_of_system_eq hSystem hcq'.symm b)))
          ((heq_apply_of_system_eq hSystem hcq.symm a).symm.trans
            (hqq.trans (heq_apply_of_system_eq hSystem hcq'.symm a))),
        h₁.ideal_apply_diag M g q q' hq hq' hqq]
      have hcard : Fintype.card ((B₂.system (hΘ.exits g)).reg a) =
          Fintype.card ((B₁.system g).reg a) := by
        rw [hΘ.systems g]
      rw [hcard]
      refine congrArg (fun z : ℂ => (((Fintype.card ((B₁.system g).reg a) : ℝ)⁻¹ : ℝ) : ℂ) * z) ?_
      refine Eq.trans ?_ (Equiv.sum_comp (systemTotalCast (hΘ.systems g))
        (fun p => M (⟨g, p⟩ : B₁.space) (⟨g, p⟩ : B₁.space)))
      refine Finset.sum_congr rfl ?_
      intro p _
      exact congrArg₂ M (hpull g p) (hpull g p)
    · have hL : L₂.ideal ((Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap M) (Θ ⟨g, q⟩) (Θ ⟨g, q'⟩)
      = 0 := by
        refine h₂.ideal_apply_zero ((Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap M) _ _ ?_
        rintro ⟨-, hA, hB, hC⟩
        refine hd ⟨?_, ?_, ?_⟩
        · have hcq : (Θ ⟨g, q⟩).2 ≍ q := hΘ.snd ⟨g, q⟩
          have hSystem : B₂.system (Θ ⟨g, q⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hA.trans (heq_apply_of_system_eq hSystem hcq b))
        · have hcq : (Θ ⟨g, q'⟩).2 ≍ q' := hΘ.snd ⟨g, q'⟩
          have hSystem : B₂.system (Θ ⟨g, q'⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q'⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hB.trans (heq_apply_of_system_eq hSystem hcq b))
        · have hcq : (Θ ⟨g, q⟩).2 ≍ q := hΘ.snd ⟨g, q⟩
          have hcq' : (Θ ⟨g, q'⟩).2 ≍ q' := hΘ.snd ⟨g, q'⟩
          have hSystem : B₂.system (Θ ⟨g, q⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q⟩]; exact hΘ.systems g
          have hSystem' : B₂.system (Θ ⟨g, q'⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q'⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hC.trans (heq_apply_of_system_eq hSystem' hcq' a))
      rw [hL]
      refine (h₁.ideal_apply_zero M _ _ ?_).symm
      rintro ⟨-, hA, hB, hC⟩
      exact hd ⟨hA, hB, hC⟩
  · have hne : (Θ (⟨g, q⟩ : B₁.space)).1 ≠ (Θ (⟨f, q'⟩ : B₁.space)).1 := by
      rw [hΘ.fst ⟨g, q⟩, hΘ.fst ⟨f, q'⟩]
      exact fun h => hgf (hΘ.exits_inj h)
    rw [L₂.ideal_crossExit_zero ((Matrix.reindexLinearEquiv ℂ ℂ Θ Θ).toLinearMap M) hne _ _,
      L₁.ideal_crossExit_zero M hgf q q']


/-- Transport along an equality of output boundaries is an exit-renaming register relabelling. -/
def Boundary.ExitRenaming.cast {B₁ B₂ : Boundary P} (h : B₁ = B₂) :
    Boundary.ExitRenaming (Equiv.cast (congrArg Boundary.space h)) where
  exits := Equiv.cast (congrArg Boundary.Exit h)
  exits_inj := (Equiv.cast (congrArg Boundary.Exit h)).injective
  systems g := by subst h; rfl
  fst x := by subst h; rfl
  snd x := by subst h; rfl


end LOCC
