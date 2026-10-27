import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty

/-! # Output Layout -/


noncomputable section

namespace QKD
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A heterogeneous boundary-key layout whose two key factors belong to distinguished local
laboratories.

For each complete public exit, `aliceSplit` and `bobSplit` exhibit the key alphabet selected by
`disposition` as a factor of Alice's and Bob's own registers.  This is the local-register form of
the two-key full outputs in Christandl--König--Renner, arXiv:0809.3019, lines 435--448, and
Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, lines 394--400.  The layout retains both
local residual factors and every other party's register; it contains no program, channel, ideal
map, or security field. -/
structure OutputLayout (B : Boundary P) where
  /-- Alice's party index. -/
  alice : P
  /-- Bob's party index. -/
  bob : P
  /-- Alice and Bob are distinct laboratories. -/
  alice_ne_bob : alice ≠ bob
  /-- Abort/accept status and accepted key length at every complete public exit. -/
  disposition : B.Exit → BoundaryKeyLayout.Disposition
  /-- Alice's non-key local factor at each exit. -/
  AliceResidual : B.Exit → Type
  /-- Bob's non-key local factor at each exit. -/
  BobResidual : B.Exit → Type
  /-- Alice's residual factor is finite at every exit. -/
  [finAliceResidual : ∀ e, Fintype (AliceResidual e)]
  /-- Equality is decidable on Alice's residual factor at every exit. -/
  [decAliceResidual : ∀ e, DecidableEq (AliceResidual e)]
  /-- Alice's residual factor is inhabited at every exit. -/
  [nonemptyAliceResidual : ∀ e, Nonempty (AliceResidual e)]
  /-- Bob's residual factor is finite at every exit. -/
  [finBobResidual : ∀ e, Fintype (BobResidual e)]
  /-- Equality is decidable on Bob's residual factor at every exit. -/
  [decBobResidual : ∀ e, DecidableEq (BobResidual e)]
  /-- Bob's residual factor is inhabited at every exit. -/
  [nonemptyBobResidual : ∀ e, Nonempty (BobResidual e)]
  /-- Alice's key and residual factors inside Alice's local register. -/
  aliceSplit : ∀ e, (B.system e).reg alice ≃
    (disposition e).Key × AliceResidual e
  /-- Bob's key and residual factors inside Bob's local register. -/
  bobSplit : ∀ e, (B.system e).reg bob ≃
    (disposition e).Key × BobResidual e

attribute [instance] OutputLayout.finAliceResidual OutputLayout.decAliceResidual
  OutputLayout.nonemptyAliceResidual OutputLayout.finBobResidual
  OutputLayout.decBobResidual OutputLayout.nonemptyBobResidual

namespace OutputLayout

variable {B : Boundary P} (L : OutputLayout B)

/-- Bob as an element of the party indices away from Alice. -/
def bobAwayFromAlice : {i : P // i ≠ L.alice} :=
  ⟨L.bob, L.alice_ne_bob.symm⟩

/-- The indices of laboratories other than Alice and Bob. -/
abbrev SpectatorParty : Type :=
  {i : {i : P // i ≠ L.alice} // i ≠ L.bobAwayFromAlice}

/-- The dependent product of every spectator laboratory's register at one complete exit. -/
abbrev Spectators (e : B.Exit) : Type :=
  ∀ i : L.SpectatorParty, (B.system e).reg i.1.1

/-- Spectator registers form a finite coordinate type. -/
instance instFintypeSpectators (e : B.Exit) : Fintype (L.Spectators e) :=
  Pi.instFintype

/-- Equality of spectator-register coordinates is decidable. -/
instance instDecidableEqSpectators (e : B.Exit) : DecidableEq (L.Spectators e) :=
  Fintype.decidablePiFintype

/-- The complete spectator-register coordinate is inhabited. -/
instance instNonemptySpectators (e : B.Exit)
    [∀ i : L.SpectatorParty, Nonempty ((B.system e).reg i.1.1)] : Nonempty (L.Spectators e) :=
  inferInstance

/-- All output data other than Alice's and Bob's key factors at one complete exit. -/
abbrev Residual (e : B.Exit) : Type :=
  (L.AliceResidual e × L.BobResidual e) × L.Spectators e

/-- The complete residual coordinate is finite. -/
instance instFintypeResidual (e : B.Exit) : Fintype (L.Residual e) :=
  inferInstance

/-- Equality of complete residual coordinates is decidable. -/
instance instDecidableEqResidual (e : B.Exit) : DecidableEq (L.Residual e) :=
  inferInstance

/-- The complete residual coordinate is inhabited. -/
instance instNonemptyResidual (e : B.Exit) [Nonempty (L.Spectators e)] : Nonempty (L.Residual e) :=
  inferInstance

/-- Split a final joint register into Alice's local key/residual pair, Bob's local
key/residual pair, and the dependent product of all spectator registers.  The two successive
function-product splits preserve the party-indexed ownership data. -/
def registerSplit (e : B.Exit) : (B.system e).total ≃
    ((L.disposition e).Key × L.AliceResidual e) ×
      (((L.disposition e).Key × L.BobResidual e) × L.Spectators e) :=
  ((B.system e).splitAt L.alice).trans
    ((Equiv.prodCongr (Equiv.refl ((B.system e).reg L.alice))
      (Equiv.piSplitAt L.bobAwayFromAlice (fun i => (B.system e).reg i.1))).trans
    (Equiv.prodCongr (L.aliceSplit e)
      (Equiv.prodCongr (L.bobSplit e) (Equiv.refl (L.Spectators e)))))

/-- Reassociate the ownership-preserving register split into the two key coordinates followed by
all retained output data. -/
def coordinates (e : B.Exit) : (B.system e).total ≃
    (L.disposition e).Key × (L.disposition e).Key × L.Residual e :=
  (L.registerSplit e).trans
    ((Equiv.prodCongr (Equiv.refl ((L.disposition e).Key × L.AliceResidual e))
      (Equiv.prodAssoc (L.disposition e).Key (L.BobResidual e) (L.Spectators e))).trans
    ((Equiv.prodProdProdComm (L.disposition e).Key (L.AliceResidual e)
      (L.disposition e).Key (L.BobResidual e × L.Spectators e)).trans
    ((Equiv.prodCongr
      (Equiv.refl ((L.disposition e).Key × (L.disposition e).Key))
      (Equiv.prodAssoc (L.AliceResidual e) (L.BobResidual e)
        (L.Spectators e)).symm).trans
    (Equiv.prodAssoc (L.disposition e).Key (L.disposition e).Key (L.Residual e)))))

/-- Alice's first output coordinate is the key factor extracted from Alice's own local register.

This is the local-ownership refinement of the Alice-key component of the full QKD output in
Christandl--König--Renner, arXiv:0809.3019, lines 435--448. -/
theorem coordinates_aliceKey (e : B.Exit) (q : (B.system e).total) :
    (L.coordinates e q).1 = (L.aliceSplit e (q L.alice)).1 := by
  rfl

/-- Bob's second output coordinate is the key factor extracted from Bob's own local register.

This is the local-ownership refinement of the Bob-key component of the full QKD output in
Christandl--König--Renner, arXiv:0809.3019, lines 435--448, and the full protocol map in
Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, lines 394--400. -/
theorem coordinates_bobKey (e : B.Exit) (q : (B.system e).total) :
    (L.coordinates e q).2.1 = (L.bobSplit e (q L.bob)).1 := by
  rfl

/-- Forget the local-ownership witnesses while retaining the derived full-output coordinates used
by the boundary-native ideal resource. -/
def toBoundaryKeyLayout : BoundaryKeyLayout B where
  disposition := L.disposition
  Residual := L.Residual
  finResidual := fun _ => inferInstance
  decResidual := fun _ => inferInstance
  coordinates := L.coordinates

/-- Conversion to `BoundaryKeyLayout` preserves the exit disposition. -/
@[simp] theorem toBoundaryKeyLayout_disposition (e : B.Exit) :
    L.toBoundaryKeyLayout.disposition e = L.disposition e := by
  rfl

/-- Conversion to `BoundaryKeyLayout` preserves the derived full-output coordinates. -/
@[simp] theorem toBoundaryKeyLayout_coordinates (e : B.Exit) :
    L.toBoundaryKeyLayout.coordinates e = L.coordinates e := by
  rfl

end OutputLayout

/-- A two-party output layout supplies an inhabitant of each terminal joint register. -/
theorem OutputLayout.nonempty_system_total {B : LOCC.Boundary LOCC.TwoParty.Party}
    (L : OutputLayout B) (e : B.Exit) : Nonempty (B.system e).total := by
  have ha : Nonempty ((B.system e).reg L.alice) :=
    Nonempty.map (L.aliceSplit e).symm inferInstance
  have hb : Nonempty ((B.system e).reg L.bob) :=
    Nonempty.map (L.bobSplit e).symm inferInstance
  rcases hA : L.alice with _ | _ <;> rcases hB : L.bob with _ | _
  · exact (L.alice_ne_bob (hA.trans hB.symm)).elim
  · rw [hA] at ha
    rw [hB] at hb
    exact Nonempty.map (B.system e).pairEquiv.symm ⟨(Classical.choice ha, Classical.choice hb)⟩
  · rw [hA] at ha
    rw [hB] at hb
    exact Nonempty.map (B.system e).pairEquiv.symm ⟨(Classical.choice hb, Classical.choice ha)⟩
  · exact (L.alice_ne_bob (hA.trans hB.symm)).elim

end QKD
