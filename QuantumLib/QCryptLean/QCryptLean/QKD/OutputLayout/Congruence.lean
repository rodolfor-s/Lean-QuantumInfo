import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft

/-!
# Literal congruence of local key ownership layouts

The laws compare owners, dispositions, both residual types, and both splitting equivalences.
Finite enumerations and decidable equalities are uniquely determined once the residual types agree.
Restriction to one announced branch lets a layout comparison follow the public tree.
-/

namespace QKD.OutputLayout
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Layout equality after boundary transport checks every non-proof ownership field. -/
theorem heq_ext {B C : Boundary P} (hB : B = C) (L : OutputLayout B) (M : OutputLayout C)
    (ha : L.alice = M.alice) (hb : L.bob = M.bob)
    (hd : ∀ e f, HEq e f → L.disposition e = M.disposition f)
    (hA : ∀ e f, HEq e f → L.AliceResidual e = M.AliceResidual f)
    (hR : ∀ e f, HEq e f → L.BobResidual e = M.BobResidual f)
    (hs : ∀ e f, HEq e f → HEq (L.aliceSplit e) (M.aliceSplit f))
    (ht : ∀ e f, HEq e f → HEq (L.bobSplit e) (M.bobSplit f)) : HEq L M := by
  cases hB
  rcases L with @⟨a, b, hab, d, A, R, fa, da, na, fr, dr, nr, s, t⟩
  rcases M with @⟨a', b', hab', d', A', R', fa', da', na', fr', dr', nr', s', t'⟩
  dsimp only at ha hb hd hA hR hs ht
  subst a'
  subst b'
  have hd' : d = d' := funext (fun e => hd e e HEq.rfl)
  have hA' : A = A' := funext (fun e => hA e e HEq.rfl)
  have hR' : R = R' := funext (fun e => hR e e HEq.rfl)
  subst d'
  subst A'
  subst R'
  have hs' : s = s' := funext (fun e => eq_of_heq (hs e e HEq.rfl))
  have ht' : t = t' := funext (fun e => eq_of_heq (ht e e HEq.rfl))
  subst s'
  subst t'
  have hfa : fa = fa' := Subsingleton.elim _ _
  have hda : da = da' := Subsingleton.elim _ _
  have hfr : fr = fr' := Subsingleton.elim _ _
  have hdr : dr = dr' := Subsingleton.elim _ _
  subst fa'
  subst da'
  subst fr'
  subst dr'
  rfl

/-- Restrict ownership data to one public branch without changing any local splitting. -/
def atAnnouncement {Y : Type} [Fintype Y] [DecidableEq Y] {B : Y → Boundary P}
    (L : OutputLayout (.announce Y B)) (y : Y) : OutputLayout (B y) where
  alice := L.alice
  bob := L.bob
  alice_ne_bob := L.alice_ne_bob
  disposition e := L.disposition ⟨y, e⟩
  AliceResidual e := L.AliceResidual ⟨y, e⟩
  BobResidual e := L.BobResidual ⟨y, e⟩
  finAliceResidual e := L.finAliceResidual ⟨y, e⟩
  decAliceResidual e := L.decAliceResidual ⟨y, e⟩
  nonemptyAliceResidual e := L.nonemptyAliceResidual ⟨y, e⟩
  finBobResidual e := L.finBobResidual ⟨y, e⟩
  decBobResidual e := L.decBobResidual ⟨y, e⟩
  nonemptyBobResidual e := L.nonemptyBobResidual ⟨y, e⟩
  aliceSplit e := L.aliceSplit ⟨y, e⟩
  bobSplit e := L.bobSplit ⟨y, e⟩

/-- Equal branch layouts and owners give equality of the complete announced layout. -/
theorem announced_heq {Y : Type} [Fintype Y] [DecidableEq Y] {B C : Y → Boundary P}
    (hB : ∀ y, B y = C y) (L : OutputLayout (.announce Y B))
    (M : OutputLayout (.announce Y C)) (ha : L.alice = M.alice) (hb : L.bob = M.bob)
    (hL : ∀ y, HEq (L.atAnnouncement y) (M.atAnnouncement y)) : HEq L M := by
  cases funext hB
  refine heq_ext rfl L M ha hb ?_ ?_ ?_ ?_ ?_
  all_goals
    intro e f h
    cases eq_of_heq h
    have h := eq_of_heq (hL e.1)
  · exact congrArg (fun K => K.disposition e.2) h
  · exact congrArg (fun K => K.AliceResidual e.2) h
  · exact congrArg (fun K => K.BobResidual e.2) h
  · exact congr_arg_heq (fun K => K.aliceSplit e.2) h
  · exact congr_arg_heq (fun K => K.bobSplit e.2) h

/-- Boundary transport changes no ownership data heterogeneously. -/
theorem transport_heq {B C : Boundary P} (h : B = C) (L : OutputLayout B) :
    HEq (transport h L) L := by
  cases h
  rfl

/-- Restricting a grafted layout to a public branch restricts the attached child layouts. -/
theorem atAnnouncement_graftFixedParties {Y : Type} [Fintype Y] [DecidableEq Y]
    {B : Y → Boundary P} {C : (Boundary.announce Y B).Exit → Boundary P}
    (a b : P) (hab : a ≠ b) (L : ∀ e, OutputLayout (C e))
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) (y : Y) :
    (graftFixedParties a b hab L hA hB).atAnnouncement y =
      graftFixedParties a b hab (fun e => L ⟨y, e⟩)
        (fun e => hA ⟨y, e⟩) (fun e => hB ⟨y, e⟩) := by
  apply eq_of_heq
  refine heq_ext rfl _ _ rfl rfl ?_ ?_ ?_ ?_ ?_
  all_goals
    intro e f h
    cases eq_of_heq h
    rfl

/-- A leaf prefix adds no ownership data to its sole attached layout. -/
theorem graftFixedParties_leaf {R : MultipartiteSystem P}
    {C : (Boundary.leaf R).Exit → Boundary P}
    (a b : P) (hab : a ≠ b) (L : ∀ e, OutputLayout (C e))
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) :
    graftFixedParties a b hab L hA hB = L () := by
  have ha := hA ()
  have hb := hB ()
  subst a
  subst b
  rfl

/-- Equal graft presentations and corresponding child layouts preserve all ownership fields. -/
theorem graftFixedParties_heq {B D : Boundary P} (hB : B = D)
    {C : B.Exit → Boundary P} {E : D.Exit → Boundary P}
    (hC : ∀ e f, HEq e f → C e = E f)
    (a b : P) (hab : a ≠ b) (L : ∀ e, OutputLayout (C e))
    (M : ∀ f, OutputLayout (E f))
    (hLA : ∀ e, (L e).alice = a) (hLB : ∀ e, (L e).bob = b)
    (hMA : ∀ f, (M f).alice = a) (hMB : ∀ f, (M f).bob = b)
    (hL : ∀ e f, HEq e f → HEq (L e) (M f)) :
    HEq (graftFixedParties a b hab L hLA hLB) (graftFixedParties a b hab M hMA hMB) := by
  cases hB
  have h : C = E := funext (fun e => hC e e HEq.rfl)
  cases h
  have h : L = M := funext (fun e => eq_of_heq (hL e e HEq.rfl))
  cases h
  rfl

end QKD.OutputLayout
