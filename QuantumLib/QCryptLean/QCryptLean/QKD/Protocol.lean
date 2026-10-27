import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Protocol -/


open Quantum.Operators

noncomputable section

namespace QKD
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]

end QKD

namespace LOCC.Program

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]
variable {alice bob : P} {R : MultipartiteSystem P}

/-- Read the complete local key ownership layout from the program's terminal values. -/
def outputLayout (p : Program R (QKD.KeyEnd alice bob)) (hne : alice ≠ bob) :
    QKD.OutputLayout p.boundary where
  alice := alice
  bob := bob
  alice_ne_bob := hne
  disposition e := (p.terminal e).disposition
  AliceResidual e := (p.terminal e).AliceResidual
  BobResidual e := (p.terminal e).BobResidual
  aliceSplit e := (p.terminal e).aliceSplit
  bobSplit e := (p.terminal e).bobSplit

end LOCC.Program

namespace QKD
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]

/-- A local protocol whose terminal values identify the two parties' final key registers. -/
structure Protocol (P : Type) [Fintype P] [DecidableEq P] [SystemPresentation P] where
  /-- Initial laboratory registers. -/
  start : MultipartiteSystem P
  /-- The owner of the first key. -/
  alice : P
  /-- The owner of the second key. -/
  bob : P
  /-- The key registers belong to different parties. -/
  alice_ne_bob : alice ≠ bob
  /-- The program, including local key ownership at each terminal branch. -/
  program : Program start (KeyEnd alice bob)

namespace Protocol

variable (A : Protocol P)

/-- The public output tree computed from the protocol. -/
abbrev boundary : Boundary P := A.program.boundary

/-- Local key ownership read from the protocol's terminal values. -/
def layout : OutputLayout A.boundary := A.program.outputLayout A.alice_ne_bob


/-- The complete protocol program supplies a complete public exit. -/
theorem nonempty_exit (A : Protocol P) [Nonempty A.start.total] : Nonempty A.boundary.Exit :=
  A.program.nonempty_exit

/-- The real protocol map is the denotation of the LOCC program. -/
def real : Quantum.Operators.Op A.start.total →ₗ[ℂ] Quantum.Operators.Op
  A.boundary.space :=
  A.program.denote

/-- The ambient full-exit-pinching resource replaces accepted keys and preserves residual data.

This is a postprocessor on the whole output boundary.  It is distinct from the ideal protocol
map, which first runs the real protocol. -/
def resource : Quantum.Operators.Op A.boundary.space →ₗ[ℂ]
  Quantum.Operators.Op A.boundary.space :=
  A.layout.toBoundaryKeyLayout.ideal

/-- The ideal protocol map is the boundary resource after the real protocol. -/
def ideal : Quantum.Operators.Op A.start.total →ₗ[ℂ] Quantum.Operators.Op
  A.boundary.space :=
  A.resource.comp A.real

/-- The real-minus-ideal map on the complete output interface. -/
def difference : Quantum.Operators.Op A.start.total →ₗ[ℂ] Quantum.Operators.Op
  A.boundary.space :=
  A.real - A.ideal

/-- The real-minus-ideal map is the difference of the two derived maps, by definition. -/
theorem difference_eq_real_sub_ideal (A : Protocol P) : A.difference = A.real - A.ideal := rfl

/-- **The normalized diamond distance between the protocol's real map and its ideal map.**

Both maps are derived from the program and the output layout, so this real number belongs to the
protocol alone: no coordinate package, reference system, ideal channel or security premise is
supplied by a caller.  The diamond norm quantifies over arbitrary references.

The intrinsic definition also covers empty input registers. -/
noncomputable def realIdealDistance (A : Protocol P) : ℝ :=
  Quantum.Channels.diamondDist A.real A.ideal

/-- The real/ideal distance is half the diamond norm of the real-minus-ideal map. -/
theorem realIdealDistance_eq_half_diamondNorm_difference
    (A : Protocol P) :
      A.realIdealDistance = (1 / 2) * Quantum.Channels.diamondNorm A.difference := rfl

/-- The real/ideal distance is nonnegative. -/
theorem realIdealDistance_nonneg (A : Protocol P) : 0 ≤ A.realIdealDistance := by
  exact Quantum.Channels.diamondDist_nonneg _ _

/-- Every real output has zero coherences between distinct complete public exits.

This is the classical-public-output property of the full QKD maps in
Christandl--König--Renner, arXiv:0809.3019, lines 423--448, derived here from the program. -/
theorem real_isExitBlockDiagonal (rho : Quantum.Operators.Op A.start.total) :
    Boundary.IsExitBlockDiagonal A.boundary (A.real rho) := by
  exact A.program.denote_isExitBlockDiagonal rho

/-- The real protocol map is trace preserving and completely positive. -/
theorem isChannel_real : Quantum.Channels.IsChannel A.real :=
  A.program.isChannel_denote

/-- The full-output key resource is trace preserving and completely positive. -/
theorem isChannel_resource : Quantum.Channels.IsChannel A.resource :=
  A.layout.toBoundaryKeyLayout.isChannel_ideal

/-- The ideal protocol map is a channel by composition with the key resource. -/
theorem isChannel_ideal : Quantum.Channels.IsChannel A.ideal :=
  A.isChannel_resource.comp A.isChannel_real

/-- On every accepting exit, both locally owned key registers are classical for every input.

Entries may retain arbitrary coherence in the residual coordinates.  This is the two-key output
condition preceding the Alice-key marginal criterion in
Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, lines 394--400. -/
def AcceptedKeyClassical (A : Protocol P) : Prop :=
  ∀ (rho : Quantum.Operators.Op A.start.total) (e : A.boundary.Exit) (ℓ : ℕ)
    (haccept : A.layout.disposition e = .accept ℓ)
    (alice bob alice' bob' : (Fin ℓ → Fin 2))
    (u v : A.layout.Residual e),
    ¬ (alice = alice' ∧ bob = bob') →
      A.real rho
          ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
            (alice, bob, u)⟩
          ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
            (alice', bob', v)⟩ = 0

/-- Full-interface QKD security: accepted local keys are classical and the normalized diamond
distance from the derived ideal protocol is at most `epsilon`.

The subject is the protocol and the budget alone.  Both maps being compared are derived from the
program and the output layout, and the distance is the coordinate-free `realIdealDistance`, so no
caller supplies a channel, an ideal map or a numbering of the registers.

This retains both keys and all public and residual outputs as in the full maps of
Christandl--König--Renner, arXiv:0809.3019, lines 423--448.  It is not Nahar et al.'s Alice-key
marginal, half-trace-distance criterion (arXiv:2403.11851, lines 394--400). -/
def IsSecure (A : Protocol P) (epsilon : ℝ) : Prop :=
  A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon

/-- Full-interface security includes the accepted-key classicality claim. -/
theorem IsSecure.acceptedKeyClassical {A : Protocol P}
    {epsilon : ℝ} (h : A.IsSecure epsilon) : A.AcceptedKeyClassical := h.1

/-- Full-interface security includes the normalized real/ideal diamond bound. -/
theorem IsSecure.realIdealDistance_le {A : Protocol P}
    {epsilon : ℝ} (h : A.IsSecure epsilon) : A.realIdealDistance ≤ epsilon := h.2

/-- Increasing the allowed error preserves full-interface security. -/
theorem IsSecure.mono {A : Protocol P} {ε ε' : ℝ}
    (h : A.IsSecure ε) (hε : ε ≤ ε') : A.IsSecure ε' :=
  ⟨h.1, h.2.trans hε⟩

/-- Full-interface security is exactly accepted-key classicality together with the normalized
real/ideal diamond bound. -/
theorem isSecure_iff (A : Protocol P) (epsilon : ℝ) :
    A.IsSecure epsilon ↔
      A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon := Iff.rfl

end Protocol

end QKD

namespace LOCC.Program

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]
variable {alice bob : P} {R : MultipartiteSystem P}

/-- Package a program with the local key ownership supplied by its terminal values. -/
def toProtocol (p : Program R (QKD.KeyEnd alice bob))
    (hne : alice ≠ bob := by decide) : QKD.Protocol P :=
  ⟨R, alice, bob, hne, p⟩

end LOCC.Program
