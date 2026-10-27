import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ClassicalContinuation
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.Protocol

/-!
# Real/ideal interface for the complete measure-first BB84 protocol

The public interface of a configured experiment is its real map, its derived ideal map and the
normalized diamond distance between them, together with the accepted-key classicality of the real
output.  Christandl--König--Renner, arXiv:0809.3019, lines 423--455, motivate the full real/ideal
interface. The reduction connects the physical maps directly to the retained
experiment and analytical model through their natural registers.
-/

noncomputable section

namespace QKD.BB84

open LOCC
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.FiniteKey

/-- **Honest-register diagonality gives accepted-key classicality.**  If, within every exit, the
real output of a two-party protocol is diagonal in Alice's and Bob's registers, and its output
layout reads Alice's key from Alice's register and Bob's key from Bob's, then on every accepting
exit its two key registers are classical: distinct key pairs sit in distinct register values. -/
private theorem acceptedKeyClassical_of_honestRegistersDiagonal
    (A : QKD.Protocol TwoParty.Party) (halice : A.layout.alice = .alice)
    (hbob : A.layout.bob = .bob)
    (hdiag : ∀ rho, A.boundary.HonestRegistersDiagonal (A.real rho)) :
    A.AcceptedKeyClassical := by
  intro rho e keyLength haccept alice bob alice' bob' u v hmismatch
  -- Name the two accepted output points; their accept coordinates are the supplied keys.
  generalize hq : (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
    (alice, bob, u) = q
  generalize hq' : (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
    (alice', bob', v) = q'
  have hkey : A.layout.toBoundaryKeyLayout.acceptCoordinates haccept q = (alice, bob, u) := by
    rw [← hq, Equiv.apply_symm_apply]
    rfl
  have hkey' : A.layout.toBoundaryKeyLayout.acceptCoordinates haccept q' = (alice', bob', v) := by
    rw [← hq', Equiv.apply_symm_apply]
    rfl
  refine hdiag rho e q q' ?_
  -- Equal Alice and Bob registers would give equal key pairs.
  by_contra hregisters
  push Not at hregisters
  apply hmismatch
  constructor
  · have hcoordinate : (A.layout.coordinates e q).1 = (A.layout.coordinates e q').1 := by
      rw [A.layout.coordinates_aliceKey, A.layout.coordinates_aliceKey]
      exact congrArg (fun x => (A.layout.aliceSplit e x).1) (halice ▸ hregisters.1)
    have hacceptCoordinate :=
      A.layout.toBoundaryKeyLayout.acceptCoordinates_fst_eq_of_coordinates_fst_heq
        A.layout.toBoundaryKeyLayout haccept haccept q q' (heq_of_eq hcoordinate)
    rw [hkey, hkey'] at hacceptCoordinate
    exact hacceptCoordinate
  · have hcoordinate : (A.layout.coordinates e q).2.1 = (A.layout.coordinates e q').2.1 := by
      rw [A.layout.coordinates_bobKey, A.layout.coordinates_bobKey]
      exact congrArg (fun x => (A.layout.bobSplit e x).1) (hbob ▸ hregisters.2)
    have hacceptCoordinate :=
      A.layout.toBoundaryKeyLayout.acceptCoordinates_snd_fst_eq_of_coordinates_snd_fst_heq
        A.layout.toBoundaryKeyLayout haccept haccept q q' (heq_of_eq hcoordinate)
    rw [hkey, hkey'] at hacceptCoordinate
    exact hacceptCoordinate

namespace Parameters

variable (p : Parameters)

/-- **On every accepting exit, the configured protocol's two local key registers are classical.**

This is the full two-key output classicality condition preceding the marginal secrecy criterion in
Nahar et al., arXiv:2403.11851, lines 394--400.  It holds for every complex input operator, with
no hypothesis at all, and asserts neither uniformity nor independence from a reference system. -/
theorem acceptedKeyClassical_protocol : p.protocol.AcceptedKeyClassical := by
  refine acceptedKeyClassical_of_honestRegistersDiagonal p.protocol rfl rfl ?_
  -- `p.protocol` is `QKD.BB84.protocol` at the configured choices, whose real map is diagonal in
  -- Alice's and Bob's registers within every exit.
  rw [Parameters.protocol]
  exact protocol_real_honestRegistersDiagonal p.aliceBasis p.bobBasis p.rounds p.keyRounds
    p.zTests p.xTests p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate

/-- **A bound on the real/ideal diamond distance is full-interface security.**

The classicality conjunct is the theorem above, so a caller supplies only the distance bound.  No
channel equality is assumed beyond the displayed distance bound. The full interface follows
Christandl--König--Renner, arXiv:0809.3019, lines 423--455; the distinguishing advantage uses the
normalization of Portmann--Renner and Nahar et al. -/
theorem isSecure_of_realIdealDistance_le {epsilon : ℝ}
    (hdist : p.protocol.realIdealDistance ≤ epsilon) :
    p.protocol.IsSecure epsilon :=
  ⟨p.acceptedKeyClassical_protocol, hdist⟩

end Parameters

end QKD.BB84
