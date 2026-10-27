import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.QKD.OutputLayout

/-! # Graft -/


noncomputable section

namespace QKD.OutputLayout
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Transport an output layout along an equality of its public output boundary. -/
noncomputable def transport {B C : Boundary P} (h : B = C)
    (L : QKD.OutputLayout B) : QKD.OutputLayout C :=
  h ▸ L

/-- Boundary transport does not change the named Alice laboratory. -/
@[simp] theorem transport_alice {B C : Boundary P} (h : B = C)
    (L : QKD.OutputLayout B) : (transport h L).alice = L.alice := by
  subst C
  rfl

/-- Boundary transport does not change the named Bob laboratory. -/
@[simp] theorem transport_bob {B C : Boundary P} (h : B = C)
    (L : QKD.OutputLayout B) : (transport h L).bob = L.bob := by
  subst C
  rfl

/-- Boundary transport keeps the disposition of every transported exit. -/
theorem transport_disposition {B C : Boundary P} (h : B = C) (L : QKD.OutputLayout B)
    (f : B.Exit) :
    (transport h L).disposition (Equiv.cast (congrArg Boundary.Exit h) f) =
      L.disposition f := by
  subst C
  rfl

/-- Boundary transport keeps the output coordinates of every transported point. -/
theorem transport_coordinates_heq {B C : Boundary P} (h : B = C) (L : QKD.OutputLayout B)
    (x : B.space) :
    (transport h L).coordinates (Equiv.cast (congrArg Boundary.space h) x).1
        (Equiv.cast (congrArg Boundary.space h) x).2 ≍ L.coordinates x.1 x.2 := by
  subst C
  rfl

/-- Transport a family of child output layouts through a graft when all children use the same named
Alice and Bob laboratories.

The child exit, disposition, residual types, and local register splittings are read through
`Boundary.graftExitEquiv`; `Boundary.system_graftExitEquiv` supplies the final multipartite system
transport. -/
noncomputable def graftFixedParties
    {B : Boundary P} {C : B.Exit → Boundary P}
    (alice bob : P) (alice_ne_bob : alice ≠ bob)
    (L : ∀ e, QKD.OutputLayout (C e))
    (hA : ∀ e, (L e).alice = alice)
    (hB : ∀ e, (L e).bob = bob) :
    QKD.OutputLayout (B.graft C) where
  alice := alice
  bob := bob
  alice_ne_bob := alice_ne_bob
  disposition e :=
    let g := B.graftExitEquiv C e
    (L g.1).disposition g.2
  AliceResidual e :=
    let g := B.graftExitEquiv C e
    (L g.1).AliceResidual g.2
  BobResidual e :=
    let g := B.graftExitEquiv C e
    (L g.1).BobResidual g.2
  finAliceResidual e := by
    dsimp
    infer_instance
  decAliceResidual e := by
    dsimp
    infer_instance
  nonemptyAliceResidual e := by
    dsimp
    infer_instance
  finBobResidual e := by
    dsimp
    infer_instance
  decBobResidual e := by
    dsimp
    infer_instance
  nonemptyBobResidual e := by
    dsimp
    infer_instance
  aliceSplit e := by
    let g := B.graftExitEquiv C e
    change ((B.graft C).system e).reg alice ≃
      ((L g.1).disposition g.2).Key × (L g.1).AliceResidual g.2
    rw [Boundary.system_graftExitEquiv]
    rw [← hA g.1]
    exact (L g.1).aliceSplit g.2
  bobSplit e := by
    let g := B.graftExitEquiv C e
    change ((B.graft C).system e).reg bob ≃
      ((L g.1).disposition g.2).Key × (L g.1).BobResidual g.2
    rw [Boundary.system_graftExitEquiv]
    rw [← hB g.1]
    exact (L g.1).bobSplit g.2

/-- A grafted layout delegates its disposition to the attached child layout. -/
theorem graftFixedParties_disposition
    (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (e : B.Exit) (f : (C e).Exit) :
    (QKD.OutputLayout.graftFixedParties a b hab L hA hB).disposition
        ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩) = (L e).disposition f := by
  have hz : Boundary.graftExitEquiv B C ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩) =
      ⟨e, f⟩ := Equiv.apply_symm_apply _ _
  exact congrArg (fun z : Σ w : B.Exit, (C w).Exit => (L z.1).disposition z.2) hz

/-- A grafted layout has the retained type of the attached child layout. -/
theorem graftFixedParties_residual
    (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (e : B.Exit) (f : (C e).Exit) :
    (graftFixedParties a b hab L hA hB).Residual ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩) =
      (L e).Residual f := by
  induction B with
  | leaf S =>
      cases e
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩)
        (fun f => hA ⟨y, f⟩) (fun f => hB ⟨y, f⟩) e f

/-- **Output coordinates through a graft.**  At a point named in graft coordinates, the grafted
layout reads the output coordinates of the attached child layout.  The equality is heterogeneous
only because the key and retained types are indexed by the complete public exit.

The point is supplied with its defining equation `hp`, so the conclusion stays syntactically in
terms of the caller's own name for it. -/
theorem graftFixedParties_coordinates_heq
    (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (e : B.Exit) (r : (C e).space) (p : (B.graft C).space)
    (hp : p = (Boundary.graftSpaceEquiv B C).symm ⟨e, r⟩) :
    (graftFixedParties a b hab L hA hB).coordinates p.1 p.2 ≍ (L e).coordinates r.1 r.2 := by
  subst hp
  induction B with
  | leaf S =>
      cases e
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      exact HEq.rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩)
        (fun f => hA ⟨y, f⟩) (fun f => hB ⟨y, f⟩) e r

/-- **Key-coordinate transport through a graft of layouts with fixed key owners.**

Both ordered key coordinates of a grafted layout at a point named in graft coordinates are the
corresponding key coordinates of the attached child layout.  The equalities are heterogeneous only
because the key alphabet is indexed by the complete public exit. -/
theorem graftFixedParties_coordinates_keys_heq
    (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (e : B.Exit) (r : (C e).space) (p : (B.graft C).space)
    (hp : p = (Boundary.graftSpaceEquiv B C).symm ⟨e, r⟩) :
    ((QKD.OutputLayout.graftFixedParties a b hab L hA hB).coordinates p.1 p.2).1 ≍
        ((L e).coordinates r.1 r.2).1 ∧
      ((QKD.OutputLayout.graftFixedParties a b hab L hA hB).coordinates p.1 p.2).2.1 ≍
        ((L e).coordinates r.1 r.2).2.1 := by
  subst hp
  induction B with
  | leaf S =>
      cases e
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      exact ⟨HEq.rfl, HEq.rfl⟩
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩)
        (fun f => hA ⟨y, f⟩) (fun f => hB ⟨y, f⟩) e r

/-- `graftFixedParties_coordinates_keys_heq` at a layout presented under its own name.

Supplying the grafted layout as a separate argument together with a defining equation keeps the
conclusion syntactically in terms of that name, so successive graft levels compose without
re-unfolding either layout. -/
theorem graftFixedParties_coordinates_keys_heq_of_eq
    (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (Lg : QKD.OutputLayout (B.graft C))
    (hLg : Lg = QKD.OutputLayout.graftFixedParties a b hab L hA hB)
    (e : B.Exit) (r : (C e).space) (p : (B.graft C).space)
    (hp : p = (Boundary.graftSpaceEquiv B C).symm ⟨e, r⟩) :
    (Lg.coordinates p.1 p.2).1 ≍ ((L e).coordinates r.1 r.2).1 ∧
      (Lg.coordinates p.1 p.2).2.1 ≍ ((L e).coordinates r.1 r.2).2.1 := by
  subst hLg
  exact graftFixedParties_coordinates_keys_heq B C L a b hab hA hB e r p hp

/-- **The inclusion of one attached continuation is a morphism** from the child layout to the
grafted layout.  Its exit renaming is `e`'s part of the graft exit equivalence, and its key and
residual maps are the identifications of `graftFixedParties_disposition` and
`graftFixedParties_residual`. -/
def graftInclHom (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) (e : B.Exit) :
    BoundaryKeyLayout.Hom (L e).toBoundaryKeyLayout
      (graftFixedParties a b hab L hA hB).toBoundaryKeyLayout :=
  BoundaryKeyLayout.Hom.ofHEq (fun r => (Boundary.graftSpaceEquiv B C).symm ⟨e, r⟩)
    (fun f => (Boundary.graftExitEquiv B C).symm ⟨e, f⟩)
    (fun _ _ hfg => eq_of_heq (Sigma.mk.inj_iff.mp
      ((Boundary.graftExitEquiv B C).symm.injective hfg)).2)
    (fun r => Boundary.graftSpaceEquiv_symm_fst B C e r)
    (fun f => graftFixedParties_disposition B C L a b hab hA hB e f)
    (fun f => graftFixedParties_residual B C L a b hab hA hB e f)
    (fun r => graftFixedParties_coordinates_heq B C L a b hab hA hB e r _ rfl)

@[simp] theorem coe_graftInclHom (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) (e : B.Exit) :
    ⇑(graftInclHom B C L a b hab hA hB e) =
      fun r => (Boundary.graftSpaceEquiv B C).symm ⟨e, r⟩ :=
  rfl

end QKD.OutputLayout
