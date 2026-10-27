import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Relabel
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft

/-! # Register Keyed -/


noncomputable section

namespace QKD.OutputLayout
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A locally owned QKD output layout whose two key coordinates are the named laboratories' own
registers and whose retained coordinate is trivial. -/
structure RegisterKeyed {B : Boundary P} (L : QKD.OutputLayout B) : Prop where
  /-- The retained coordinate carries no information. -/
  residual : ∀ e : B.Exit, Subsingleton (L.Residual e)
  /-- Alice's key coordinate is her own register. -/
  aliceKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).1 ≍ q L.alice
  /-- Bob's key coordinate is his own register. -/
  bobKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).2.1 ≍ q L.bob

/-- A register-keyed QKD output layout is register keyed as a boundary key layout. -/
theorem RegisterKeyed.toBoundaryKeyLayout {B : Boundary P} (L : QKD.OutputLayout B)
    (h : RegisterKeyed L) :
    _root_.LOCC.BoundaryKeyLayout.RegisterKeyed L.toBoundaryKeyLayout L.alice L.bob where
  residual := h.residual
  aliceKey := h.aliceKey
  bobKey := h.bobKey

/-- A two-party output layout with the actual Alice and Bob names has no spectator laboratory. -/
theorem spectator_elim {B : Boundary TwoParty.Party} (L : QKD.OutputLayout B)
    (hA : L.alice = .alice) (hB : L.bob = .bob) (i : L.SpectatorParty) : False := by
  rcases i with ⟨⟨p, hpAlice⟩, hpBob⟩
  cases p with
  | alice => exact hpAlice hA.symm
  | bob =>
      apply hpBob
      apply Subtype.ext
      exact hB.symm

/-- A two-party output layout with trivial local residual factors has a trivial retained
coordinate. -/
theorem residual_subsingleton {B : Boundary TwoParty.Party} (L : QKD.OutputLayout B)
    (hA : L.alice = .alice) (hB : L.bob = .bob)
    (hAR : ∀ e, Subsingleton (L.AliceResidual e))
    (hBR : ∀ e, Subsingleton (L.BobResidual e))
    (e : B.Exit) : Subsingleton (L.Residual e) := by
  have := hAR e
  have := hBR e
  refine ⟨fun x y => ?_⟩
  apply Prod.ext
  · apply Prod.ext <;> exact Subsingleton.elim _ _
  · funext i
    exact (spectator_elim L hA hB i).elim

/-- A grafted layout's retained coordinate is the child layout's. -/
theorem graftFixedParties_residual_subsingleton (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (hL : ∀ (e : B.Exit) (f : (C e).Exit), Subsingleton ((L e).Residual f))
    (g : (B.graft C).Exit) :
    Subsingleton ((QKD.OutputLayout.graftFixedParties a b hab L hA hB).Residual g) := by
  induction B with
  | leaf S =>
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      exact hL () g
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases g with ⟨y, g⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩) (fun f => hA ⟨y, f⟩)
        (fun f => hB ⟨y, f⟩) (fun e f => hL ⟨y, e⟩ f) g

/-- A grafted layout's Alice key coordinate is Alice's own register. -/
theorem graftFixedParties_aliceKey (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (hL : ∀ (e : B.Exit) (f : (C e).Exit) (z : ((C e).system f).total),
      ((L e).coordinates f z).1 ≍ z ((L e).alice))
    (g : (B.graft C).Exit) (q : ((B.graft C).system g).total) :
    ((QKD.OutputLayout.graftFixedParties a b hab L hA hB).coordinates g q).1 ≍ q a := by
  induction B with
  | leaf S =>
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      exact hL () g q
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases g with ⟨y, g⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩) (fun f => hA ⟨y, f⟩)
        (fun f => hB ⟨y, f⟩) (fun e f z => hL ⟨y, e⟩ f z) g q

/-- A grafted layout's Bob key coordinate is Bob's own register. -/
theorem graftFixedParties_bobKey (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (hL : ∀ (e : B.Exit) (f : (C e).Exit) (z : ((C e).system f).total),
      ((L e).coordinates f z).2.1 ≍ z ((L e).bob))
    (g : (B.graft C).Exit) (q : ((B.graft C).system g).total) :
    ((QKD.OutputLayout.graftFixedParties a b hab L hA hB).coordinates g q).2.1 ≍ q b := by
  induction B with
  | leaf S =>
      have ha := hA ()
      have hb := hB ()
      subst a
      subst b
      exact hL () g q
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases g with ⟨y, g⟩
      exact ih y (fun f => C ⟨y, f⟩) (fun f => L ⟨y, f⟩) (fun f => hA ⟨y, f⟩)
        (fun f => hB ⟨y, f⟩) (fun e f z => hL ⟨y, e⟩ f z) g q

/-- Grafting register-keyed layouts gives a register-keyed layout. -/
theorem registerKeyed_graftFixedParties (B : Boundary P) (C : B.Exit → Boundary P)
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
    (hL : ∀ e, RegisterKeyed (L e)) :
    RegisterKeyed (QKD.OutputLayout.graftFixedParties a b hab L hA hB) where
  residual g := graftFixedParties_residual_subsingleton B C L a b hab hA hB
    (fun e f => (hL e).residual f) g
  aliceKey g q := graftFixedParties_aliceKey B C L a b hab hA hB
    (fun e f z => (hL e).aliceKey f z) g q
  bobKey g q := graftFixedParties_bobKey B C L a b hab hA hB
    (fun e f z => (hL e).bobKey f z) g q

end QKD.OutputLayout

namespace LOCC

namespace BoundaryKeyLayout.RegisterKeyed

variable {P : Type} [Fintype P] [DecidableEq P]
  {B : Boundary P} {L : BoundaryKeyLayout B} {a b : P}
  [∀ e, Nonempty (B.system e).total]

/-- **A register-keyed boundary key layout is a locally owned QKD output layout.**

Each party's key factor is the whole of that party's own output register — `aliceSplit` and
`bobSplit` are the identifications `key_eq`, `key_eq_bob` of those registers with the exit's key
alphabet — so neither party retains a further local factor.  The exit disposition is the layout's
own, unchanged; nothing is added beyond the two local ownership witnesses, and no identity,
security claim, entropy estimate or extra hypothesis is supplied here. -/
def toOutputLayout (h : RegisterKeyed L a b) (hab : a ≠ b) : QKD.OutputLayout B where
  alice := a
  bob := b
  alice_ne_bob := hab
  disposition := L.disposition
  AliceResidual _ := Unit
  BobResidual _ := Unit
  aliceSplit e := (Equiv.cast (h.key_eq e).symm).trans (Equiv.prodPUnit _).symm
  bobSplit e := (Equiv.cast (h.key_eq_bob e).symm).trans (Equiv.prodPUnit _).symm

/-- The locally owned refinement keeps the layout's own abort/accept disposition. -/
@[simp] theorem toOutputLayout_disposition (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) : (h.toOutputLayout hab).disposition e = L.disposition e := rfl

/-- Alice's derived first output coordinate is her own register value. -/
theorem toOutputLayout_coordinates_fst (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) (q : (B.system e).total) :
    ((h.toOutputLayout hab).coordinates e q).1 = cast (h.key_eq e).symm
      (q a) := rfl

/-- Bob's derived second output coordinate is his own register value. -/
theorem toOutputLayout_coordinates_snd_fst (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) (q : (B.system e).total) :
    ((h.toOutputLayout hab).coordinates e q).2.1 = cast (h.key_eq_bob
      e).symm (q b) := rfl

/-- **The retained coordinate of the locally owned refinement is a one-point type.**

Derived, not assumed: the layout's own coordinates and the derived local-ownership coordinates
present the same joint register as `Key × Key × Residual`, and the layout's retained coordinate is
a one-point type, so the derived retained coordinate is one too. -/
theorem card_toOutputLayout_residual (h : RegisterKeyed L a b) (hab : a ≠ b) (e : B.Exit) :
    Fintype.card ((h.toOutputLayout hab).Residual e) = 1 := by
  let : Nonempty (L.Residual e) := ⟨(L.coordinates e (Classical.arbitrary _)).2.2⟩
  have hres : Fintype.card (L.Residual e) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr (h.residual e)) Fintype.card_pos
  have hkey : 0 < Fintype.card ((L.disposition e).Key) := Fintype.card_pos
  have hcards : Fintype.card ((L.disposition e).Key) *
        (Fintype.card ((L.disposition e).Key) * Fintype.card (L.Residual e)) =
      Fintype.card ((L.disposition e).Key) *
        (Fintype.card ((L.disposition e).Key) *
          Fintype.card ((h.toOutputLayout hab).Residual e)) := by
    rw [← Fintype.card_prod, ← Fintype.card_prod, ← Fintype.card_prod, ← Fintype.card_prod]
    exact (Fintype.card_congr (L.coordinates e)).symm.trans
      (Fintype.card_congr ((h.toOutputLayout hab).coordinates e))
  have hstep := Nat.eq_of_mul_eq_mul_left hkey hcards
  rw [hres] at hstep
  exact (Nat.eq_of_mul_eq_mul_left hkey hstep).symm

/-- The retained coordinate of the locally owned refinement carries no information. -/
theorem toOutputLayout_residual_subsingleton (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) : Subsingleton ((h.toOutputLayout hab).Residual e) :=
  Fintype.card_le_one_iff_subsingleton.mp
    (le_of_eq (h.card_toOutputLayout_residual hab e))

/-- **A register-keyed layout leaves every spectator laboratory a one-point register.**  Local
ownership of the two keys is therefore genuine: no third party retains output information. -/
theorem toOutputLayout_spectators_subsingleton (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) : Subsingleton ((h.toOutputLayout hab).Spectators e) := by
  have := h.toOutputLayout_residual_subsingleton hab e
  refine ⟨fun s s' => ?_⟩
  have hpair : (⟨⟨(), ()⟩, s⟩ : (h.toOutputLayout hab).Residual e) = ⟨⟨(), ()⟩, s'⟩ :=
    Subsingleton.elim _ _
  exact congrArg Prod.snd hpair

/-- Alice's derived key coordinate is her own register, as a heterogeneous equality of values. -/
theorem toOutputLayout_aliceKey_heq (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) (q : (B.system e).total) :
    ((h.toOutputLayout hab).toBoundaryKeyLayout.coordinates e q).1 ≍ (L.coordinates e q).1 :=
  (heq_of_eq (h.toOutputLayout_coordinates_fst hab e q)).trans
    ((cast_heq (h.key_eq e).symm (q a)).trans (h.aliceKey e q).symm)

/-- Bob's derived key coordinate is his own register, as a heterogeneous equality of values. -/
theorem toOutputLayout_bobKey_heq (h : RegisterKeyed L a b) (hab : a ≠ b)
    (e : B.Exit) (q : (B.system e).total) :
    ((h.toOutputLayout hab).toBoundaryKeyLayout.coordinates e q).2.1 ≍
      (L.coordinates e q).2.1 :=
  (heq_of_eq (h.toOutputLayout_coordinates_snd_fst hab e q)).trans
    ((cast_heq (h.key_eq_bob e).symm (q b)).trans (h.bobKey e q).symm)

/-- The retained coordinates of a register-keyed layout and of its locally owned refinement are
both one-point types, hence equivalent.  *Which* equivalence is immaterial — there is exactly one —
so the selection below is inessential and is confined to proofs of propositions. -/
private theorem exists_residual_recoordinatization (h : RegisterKeyed L a b) (hab : a ≠ b) :
    ∃ residual : ∀ e : B.Exit,
        L.Residual e ≃ (h.toOutputLayout hab).toBoundaryKeyLayout.Residual e,
      ∀ (e : B.Exit) (q : (B.system e).total),
        ((h.toOutputLayout hab).toBoundaryKeyLayout.coordinates e q).2.2 =
          residual e ((L.coordinates e q).2.2) := by
  classical
  refine ⟨fun e => ?_, fun e _ => ?_⟩
  · haveI : Subsingleton (L.Residual e) := h.residual e
    haveI : Subsingleton ((h.toOutputLayout hab).toBoundaryKeyLayout.Residual e) :=
      h.toOutputLayout_residual_subsingleton hab e
    haveI : Unique (L.Residual e) := uniqueOfSubsingleton (L.coordinates e (Classical.arbitrary
      _)).2.2
    haveI : Unique ((h.toOutputLayout hab).toBoundaryKeyLayout.Residual e) :=
      uniqueOfSubsingleton ((h.toOutputLayout hab).coordinates e (Classical.arbitrary _)).2.2
    exact Equiv.ofUnique _ _
  · have : Subsingleton ((h.toOutputLayout hab).toBoundaryKeyLayout.Residual e) :=
      h.toOutputLayout_residual_subsingleton hab e
    exact Subsingleton.elim _ _

/-- **The locally owned refinement has the same boundary-derived ideal key resource.**

Both presentations have the layout's own disposition and the same two ordered key coordinates —
Alice's and Bob's own registers — and their retained coordinates differ by a bijection, so
`BoundaryKeyLayout.ideal_congr_of_disposition_eq` applies.  The equality is of the two ambient
channels on every complete public exit, accepting and aborting, for arbitrary operators; the
retained coordinate is not erased. -/
theorem toOutputLayout_ideal (h : RegisterKeyed L a b) (hab : a ≠ b) :
    (h.toOutputLayout hab).toBoundaryKeyLayout.ideal = L.ideal := by
  obtain ⟨residual, hres⟩ := h.exists_residual_recoordinatization hab
  exact BoundaryKeyLayout.ideal_congr_of_disposition_eq L _ (fun _ => rfl) residual
    (h.toOutputLayout_aliceKey_heq hab) (h.toOutputLayout_bobKey_heq hab) hres

/-- **The two presentations name the same accepting output point.**

An accepted output is determined by the two ordered keys, so the derived local-ownership
coordinates and the layout's own coordinates invert the same key pair to one and the same joint
register value, whatever retained coordinates are supplied on either side. -/
theorem toOutputLayout_acceptCoordinates_symm (h : RegisterKeyed L a b) (hab : a ≠ b)
    {e : B.Exit} {ℓ : ℕ}
    (h₂ : (h.toOutputLayout hab).disposition e = .accept ℓ)
    (h₁ : L.disposition e = .accept ℓ) (x y : Fin ℓ → Fin 2)
    (u : (h.toOutputLayout hab).toBoundaryKeyLayout.Residual e) (w : L.Residual e) :
    ((h.toOutputLayout hab).toBoundaryKeyLayout.acceptCoordinates h₂).symm (x, y, u) =
      (L.acceptCoordinates h₁).symm (x, y, w) := by
  obtain ⟨residual, hres⟩ := h.exists_residual_recoordinatization hab
  have : Subsingleton ((h.toOutputLayout hab).toBoundaryKeyLayout.Residual e) :=
    h.toOutputLayout_residual_subsingleton hab e
  rw [Subsingleton.elim u (residual e w)]
  exact BoundaryKeyLayout.acceptCoordinates_symm_congr L _ residual
    (h.toOutputLayout_aliceKey_heq hab) (h.toOutputLayout_bobKey_heq hab) hres h₁ h₂ x y w

/-- The locally owned refinement is register keyed as a QKD output layout. -/
theorem registerKeyed_toOutputLayout (h : RegisterKeyed L a b) (hab : a ≠ b) :
    QKD.OutputLayout.RegisterKeyed (h.toOutputLayout hab) where
  residual e := h.toOutputLayout_residual_subsingleton hab e
  aliceKey e q :=
    (heq_of_eq (h.toOutputLayout_coordinates_fst hab e q)).trans
      (cast_heq (h.key_eq e).symm (q a))
  bobKey e q :=
    (heq_of_eq (h.toOutputLayout_coordinates_snd_fst hab e q)).trans
      (cast_heq (h.key_eq_bob e).symm (q b))

end BoundaryKeyLayout.RegisterKeyed

end LOCC
