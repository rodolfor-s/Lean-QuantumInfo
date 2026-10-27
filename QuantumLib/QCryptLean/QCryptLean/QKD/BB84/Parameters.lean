import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ClassicalContinuation
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.Protocol

/-!
# Configured BB84 experiments

`Parameters` contains the physical measurement laws, sampling quotas, output lengths,
error-correction scheme and acceptance window. Its `protocol` runs the plain action chain;
the boundary and local key ownership are read from that program. Security analysis parameters
are supplied separately to the theorems in `QCryptLean.QKD.BB84.Security`.
-/

noncomputable section

namespace QKD.BB84
open LOCC
open QKD.BB84
open QKD.BB84.Reduction

open LOCC.TwoParty
open QKD.BB84.FiniteKey

/-- **The physical choices of one measure-first BB84 experiment.**

The packed selector partitions the `keyRounds + zTests + xTests` sifted rounds into the key block,
the Z-test block and the X-test block, in that order; `ec` is the error-correction scheme for that
selector and syndrome length, and is arbitrary unless a security theorem's conditions say otherwise.

Alice and Bob measure `rounds` signals with independent per-round basis laws `aliceBasis` and
`bobBasis`; nothing forces these to be uniform, equal, or of full support, and `rounds` may be
smaller than the total quota, in which case the experiment takes its shortage branch. -/
structure Parameters where
  /-- Alice's per-round basis law. -/
  aliceBasis : PMF Measurement.Basis
  /-- Bob's per-round basis law. -/
  bobBasis : PMF Measurement.Basis
  /-- Number of physical signal rounds actually measured. -/
  rounds : ℕ
  /-- Number of sifted rounds retained as key rounds. -/
  keyRounds : ℕ
  /-- Number of sifted rounds spent on the Z-basis test. -/
  zTests : ℕ
  /-- Number of sifted rounds spent on the X-basis test. -/
  xTests : ℕ
  /-- Length in bits of the final key produced on acceptance. -/
  keyLength : ℕ
  /-- Length in bits of the verification tag. -/
  tagLength : ℕ
  /-- Length in bits of the announced error-correction syndrome. -/
  leak : ℕ
  /-- The error-correction scheme for the packed selector and this syndrome length. -/
  ec : ECScheme (keyRounds + zTests + xTests)
    (@Sampling.packedPESel keyRounds zTests xTests) leak
  /-- Half-width `δ` of the parameter-estimation accept test. -/
  tolerance : ℝ
  /-- Centre `Q` of the parameter-estimation accept test: a test block is accepted when its
  observed mismatch frequency lies within `tolerance` of this value. -/
  errorRate : ℝ

namespace Parameters

variable (p : Parameters)

/-- The number of sifted rounds, `nK + mZ + mX`. -/
abbrev sifted : ℕ := p.keyRounds + p.zTests + p.xTests

/-- The number of test rounds, `mZ + mX`. -/
abbrev tests : ℕ := p.zTests + p.xTests

/-- The packed parameter-estimation mask: the first `keyRounds` sifted rounds are key rounds. -/
abbrev peSel : Fin p.sifted → Bool := @Sampling.packedPESel p.keyRounds p.zTests p.xTests

/-- The packed X-test mask: the last `xTests` sifted rounds are X-basis test rounds. -/
abbrev xSel : Fin p.sifted → Bool := @Sampling.packedXSel p.keyRounds p.zTests p.xTests

/-- **The configured measure-first BB84 protocol.**

This is the existing `QKD.BB84.protocol` construction at these choices: destructive local
measurement of `rounds` signals, late public sifting and shuffle, selected-bit retention or
shortage discard, the retained classical tail, and the final decision with its two ordered keys or
key-free abort.  The complete public transcript is retained. -/
def protocol : QKD.Protocol Party :=
  QKD.BB84.protocol p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
    p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate

/-- The configured protocol starts at the physical two-party stream multipartite system. -/
theorem protocol_start :
    p.protocol.start = Measurement.weightedStreamSystem Unit p.rounds := rfl

/-- The configured protocol's complete output boundary is computed from its action chain. -/
theorem protocol_boundary :
    p.protocol.boundary =
      (QKD.BB84.construction p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate).boundary := rfl

/-- The configured protocol runs the plain measure-first action chain. -/
theorem protocol_program :
    p.protocol.program =
      QKD.BB84.construction p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate := rfl

/-- **The real map of the configured experiment is the denotation of that same program.**

There is no separately supplied analysis channel: the derived map is
`LOCC.Program.denote` of the chronological construction, on the complete output boundary. -/
theorem protocol_real :
    p.protocol.real =
      (QKD.BB84.construction p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate).denote := rfl

/-- **The ideal map of the configured experiment is its own output resource after its real map.**

`QKD.Protocol.resource` is the full-exit key replacement read off the locally owned layout, so the
ideal key resource is derived from the same program and ownership data rather than chosen. -/
theorem protocol_ideal : p.protocol.ideal = p.protocol.resource.comp p.protocol.real := rfl

/-- The real-minus-ideal map compared by both security theorems is the difference of those two
derived
maps. -/
theorem protocol_difference : p.protocol.difference = p.protocol.real - p.protocol.ideal := rfl

/-- The configured protocol reads its locally owned output layout from terminal values. -/
theorem protocol_layout :
    p.protocol.layout =
      (QKD.BB84.construction p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate).outputLayout (by decide) := rfl

/-- Completeness supplies a public exit for the configured protocol. -/
instance instNonemptyProtocolExit : Nonempty p.protocol.boundary.Exit := by
  let : Nonempty p.protocol.start.total :=
    show Nonempty (Measurement.weightedStreamSystem Unit p.rounds).total from
      inferInstance
  exact p.protocol.nonempty_exit

/-! ## What the accept test actually tests

`errorRate` and `tolerance` are both real numbers and reach the underlying builders through
positional arguments, so their roles have to be readable off a theorem rather than off a call.
The three declarations below do that: `acceptFlag` is the very flag function the configured
protocol's final decision reads (`decisionAnnouncement_eq` is that pin, by `rfl`), and
`acceptFlag_eq_true_iff` says in physical terms when it accepts. -/

/-- The window an observed test frequency must lie in to be accepted:
`[errorRate - tolerance, errorRate + tolerance]`. -/
def acceptWindow : Set ℝ :=
  Set.Icc (p.errorRate - p.tolerance) (p.errorRate + p.tolerance)

/-- Membership of the accept window is the accept test `|observed − errorRate| ≤ tolerance`. -/
theorem mem_acceptWindow_iff (f : ℝ) :
    f ∈ p.acceptWindow ↔ |f - p.errorRate| ≤ p.tolerance := by
  rw [acceptWindow, Set.mem_Icc, abs_le]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Disclosed test bits, as the retained final stage indexes them: one value per disclosed test
round of the sifted block. -/
abbrev TestBits : Type :=
  Fin (min p.sifted p.tests) → Measurement.Bit

/-- The number of disclosed Z-basis test rounds at which Alice's and Bob's announced bits
disagree. -/
def zTestMismatches (as bs : p.TestBits) : ℕ :=
  (Finset.univ.filter fun j =>
    p.xSel (peRoundIdx (m := p.tests) p.peSel j) = false ∧ as j ≠ bs j).card

/-- The number of disclosed X-basis test rounds at which Alice's and Bob's announced bits
disagree. -/
def xTestMismatches (as bs : p.TestBits) : ℕ :=
  (Finset.univ.filter fun j =>
    p.xSel (peRoundIdx (m := p.tests) p.peSel j) = true ∧ as j ≠ bs j).card

/-- The observed Z-basis test frequency: mismatching disclosed Z-test rounds per Z-test round. -/
def zTestFrequency (as bs : p.TestBits) : ℝ :=
  (p.zTestMismatches as bs : ℝ) / (p.zTests : ℝ)

/-- The observed X-basis test frequency: mismatching disclosed X-test rounds per X-test round. -/
def xTestFrequency (as bs : p.TestBits) : ℝ :=
  (p.xTestMismatches as bs : ℝ) / (p.xTests : ℝ)

/-- **The parameter-estimation decision of the configured experiment.**

It passes exactly when both disclosed test blocks are nonempty and each block's observed mismatch
frequency lies in `acceptWindow`.  The denominators are the realised block sizes `zTests` and
`xTests` (`siftedZTestSampleSize_packed`, `siftedXTestSampleSize_packed`), and the centre of the
window is
`errorRate` while its half-width is `tolerance` — not the other way round. -/
theorem testsPassed_iff (as bs : p.TestBits) :
    QKD.BB84.testsPassed p.tests p.peSel p.xSel p.tolerance p.errorRate as bs = true ↔
      ((0 < p.zTests ∧ p.zTestFrequency as bs ∈ p.acceptWindow) ∧
        (0 < p.xTests ∧ p.xTestFrequency as bs ∈ p.acceptWindow)) := by
  rw [QKD.BB84.testsPassed]
  rw [show siftedZTestSampleSize p.peSel p.xSel = p.zTests from
      siftedZTestSampleSize_packed p.keyRounds p.zTests p.xTests,
    show siftedXTestSampleSize p.peSel p.xSel = p.xTests from
      siftedXTestSampleSize_packed p.keyRounds p.zTests p.xTests]
  simp only [Bool.and_eq_true, decide_eq_true_eq, p.mem_acceptWindow_iff, zTestFrequency,
    xTestFrequency, zTestMismatches, xTestMismatches]

/-- **The accept flag the configured experiment's final decision announces.**

It is a function of the announced test bits, the announced verification seed, the announced
verification tag, the announced syndrome and Bob's own raw register; `true` accepts. -/
def acceptFlag (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Measurement.Bits p.tagLength) (syn : Measurement.Bits p.leak)
    (y : Measurement.Bits p.sifted) : Bool :=
  QKD.BB84.acceptFlag p.sifted p.tests p.tagLength p.peSel p.xSel p.leak p.ec
    p.tolerance p.errorRate as bs evSeed evTag syn y

/-- **The final decision of the configured experiment is Bob's nondestructive readout of
`acceptFlag`, announced verbatim.**

The configured protocol's decision stage is definitionally the readout of the flag function above,
whose physical meaning is `acceptFlag_eq_true_iff`. -/
theorem decisionAnnouncement_eq (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Measurement.Bits p.tagLength) (syn : Measurement.Bits p.leak) :
    announceAccept (A := Measurement.Bits p.sifted) (xSel := p.xSel) p.ec
        p.tolerance p.errorRate as bs evSeed evTag syn =
      AnnouncedAction.ofInstrument .bob
        (Instrument.nondemolitionReadout (p.acceptFlag as bs evSeed evTag syn)) id := rfl

/-- **When the configured experiment accepts.**

Both disclosed test blocks must be nonempty with observed mismatch frequency inside
`acceptWindow`, *and* the announced verification tag must equal the tag recomputed from Bob's
reconciled string.  Nothing else is tested. -/
theorem acceptFlag_eq_true_iff (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Measurement.Bits p.tagLength) (syn : Measurement.Bits p.leak)
    (y : Measurement.Bits p.sifted) :
    p.acceptFlag as bs evSeed evTag syn y = true ↔
      (((0 < p.zTests ∧ p.zTestFrequency as bs ∈ p.acceptWindow) ∧
          (0 < p.xTests ∧ p.xTestFrequency as bs ∈ p.acceptWindow)) ∧
        evTag = verificationTag p.sifted p.tagLength p.peSel evSeed
          (p.ec.decode (QKD.BB84.bobRawKey p.sifted p.peSel y) syn)) := by
  rw [acceptFlag, QKD.BB84.acceptFlag]
  simp only [Bool.and_eq_true, decide_eq_true_eq, p.testsPassed_iff]

end Parameters

end QKD.BB84
