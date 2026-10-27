import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.Instrument.OnFactor
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Weighted
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.Protocol

/-!
# Measure-first BB84

Alice and Bob measure their qubits privately, announce their bases and a shuffle of matched
rounds, abort if there are too few matches, retain the key and test rounds, disclose the test
bits and Alice's seeds, tag and syndrome, then follow Bob's acceptance decision by hashing their
keys or discarding their registers. During measurement, `streamRegister F n` holds the records
already stored in `F` and the `n` remaining qubits: each recursive step appends one `StoredRecord`
to `F`, leaving `finishAcc F N` and an empty stream after all `N` measurements.
-/

noncomputable section

namespace QKD.BB84

open LOCC LOCC.TwoParty Measurement FiniteKey

section Actions

variable {A B : Type}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable {N n m ℓ ℓEV leakEC : ℕ}
variable {peSel xSel : Fin n → Bool}

section MeasurementActions

variable (p : PMF Basis) (F : Type) [Fintype F] [DecidableEq F]

/-- Measure Alice's next qubit and append its private basis/outcome record. -/
def measureAlice (r : ℕ) :=
  PrivateAction.ofInstrument (R := system _ B) .alice
    (Instrument.onFactor (streamInputSplit F r) (streamOutputSplit F r)
      (weightedMeasureAndRecord p))

/-- Measure Bob's next qubit and append its private basis/outcome record. -/
def measureBob (r : ℕ) :=
  PrivateAction.ofInstrument (R := system A _) .bob
    (Instrument.onFactor (streamInputSplit F r) (streamOutputSplit F r)
      (weightedMeasureAndRecord p))

end MeasurementActions

/-- Announce Alice's stored basis string. -/
def announceAliceBases (N : ℕ) :=
  AnnouncedAction.ofInstrument (R := system _ B) .alice
    (Instrument.nondemolitionReadout (completedBasisString N)) id

/-- Announce Bob's stored basis string. -/
def announceBobBases (N : ℕ) :=
  AnnouncedAction.ofInstrument (R := system A _) .bob
    (Instrument.nondemolitionReadout (completedBasisString N)) id

/-- Uniformly choose and announce an ordering of the matched rounds. -/
def announceShuffle (a b : Fin N → Basis) :=
  AnnouncedAction.ofInstrument (R := system _ B) .alice
    (Instrument.uniformSample (CompletedLocalRecord N) (Sampling.Shuffle a b)) id

/-- Retain Alice's basis string and selected outcome bits. -/
def retainAlice (selected : Fin n ↪ Fin N) :=
  PrivateAction.ofInstrument (R := system _ B) .alice
    (Instrument.functionAndForget (selectedLocalRecord selected))

/-- Retain Bob's basis string and selected outcome bits. -/
def retainBob (selected : Fin n ↪ Fin N) :=
  PrivateAction.ofInstrument (R := system A _) .bob
    (Instrument.functionAndForget (selectedLocalRecord selected))

/-- Erase Alice's private basis copy, retaining her selected bit string. -/
def forgetAliceBases (N n : ℕ) :=
  PrivateAction.ofInstrument (R := system _ B) .alice
    (Instrument.functionAndForget
      (fun q : SelectedLocalRecord N n => q.2))

/-- Erase Bob's private basis copy, retaining his selected bit string. -/
def forgetBobBases (N n : ℕ) :=
  PrivateAction.ofInstrument (R := system A _) .bob
    (Instrument.functionAndForget
      (fun q : SelectedLocalRecord N n => q.2))

/-- Announce Bob's test bit at the given selected-round position. -/
def announceBobTest (i : Fin n) :=
  AnnouncedAction.ofInstrument (R := system A _) .bob
    (Instrument.nondemolitionReadout (fun x : Bits n => x i)) id

/-- Announce Alice's test bit at the given selected-round position. -/
def announceAliceTest (i : Fin n) :=
  AnnouncedAction.ofInstrument (R := system _ B) .alice
    (Instrument.nondemolitionReadout (fun x : Bits n => x i)) id

/-- Sample the seeds and announce them with Alice's tag and syndrome. -/
def announceSeedTagSyndrome (ℓ ℓEV : ℕ)
    (ec : ECScheme n peSel leakEC) :=
  AnnouncedAction.ofInstrument (R := system _ B) .alice
    (Instrument.uniformChoice
      fun seeds : KeyHashSeedPairEV n ℓ ℓEV peSel =>
        Instrument.nondemolitionReadout
          (tagAndSyndrome n ℓ ℓEV peSel leakEC ec seeds))
    id

/-- Announce Bob's test-and-verification decision. -/
def announceAccept (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (min n m) → Bit)
    (verificationSeed : KeyHashSeed n ℓEV peSel)
    (tag : Bits ℓEV) (syndrome : Bits leakEC) :=
  AnnouncedAction.ofInstrument (R := system A _) .bob
    (Instrument.nondemolitionReadout
      (acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
        as bs verificationSeed tag syndrome))
    id

/-- Hash Alice's raw key and retain only the resulting key. -/
def hashAlice (seed : KeyHashSeed n ℓ peSel) :=
  PrivateAction.ofInstrument (R := system _ B) .alice
    (Instrument.functionAndForget (aliceKey n ℓ peSel seed))

/-- Decode Bob's raw key, hash it, and retain only the resulting key. -/
def correctAndHashBob (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ℓ peSel) (syndrome : Bits leakEC) :=
  PrivateAction.ofInstrument (R := system A _) .bob
    (Instrument.functionAndForget
      (bobKey n ℓ peSel leakEC ec seed syndrome))

/-- Discard Alice's current local register. -/
def discardAlice :=
  PrivateAction.ofInstrument (R := system _ B) .alice
    (Instrument.discardToUnit A)

/-- Discard Bob's current local register. -/
def discardBob :=
  PrivateAction.ofInstrument (R := system A _) .bob
    (Instrument.discardToUnit B)

end Actions

/-- Measure each round privately, Alice first and Bob second. -/
def measureRounds (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F]
    (N : ℕ) {End : MultipartiteSystem Party → Type 1}
    (k : Program
      (system
        (streamRegister (finishAcc F N) 0)
        (streamRegister (finishAcc F N) 0)) End) :
    Program (system (streamRegister F N) (streamRegister F N)) End :=
  match N with
  | 0 => k
  | n + 1 =>
      (measureAlice pA F n).then <|
        (measureBob pB F n).then
          (measureRounds pA pB (F × StoredRecord) n k)

/-- Announce Bob's then Alice's bit at each test position. -/
def announceTests {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    {End : MultipartiteSystem Party → Type 1}
    (k : (Fin r → Bit × Bit) →
      Program (system (Bits n) (Bits n)) End) :
    Program (system (Bits n) (Bits n)) End :=
  match r with
  | 0 => k Fin.elim0
  | r + 1 =>
      (announceBobTest (idx 0)).then fun b =>
        (announceAliceTest (idx 0)).then fun a =>
          announceTests r (Fin.tail idx) fun rest =>
            k (Fin.cons (a, b) rest)

/-- Run the public discussion and terminate with owned keys or abort. -/
def classicalTail (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Program (system (Bits n) (Bits n))
      (KeyEnd Party.alice Party.bob) :=
  announceTests (min n m) (peRoundIdx peSel) fun tests =>
    (announceSeedTagSyndrome ℓ ℓEV ec).then fun publicData =>
      let (seeds, tag, syndrome) := publicData
      (announceAccept (xSel := xSel) ec δ Q
        (fun j => (tests j).1) (fun j => (tests j).2)
        seeds.2 tag syndrome).then fun accepted =>
          if accepted then
            (hashAlice seeds.1).then <|
              (correctAndHashBob ec seeds.1 syndrome).then
                (.done (KeyEnd.keys ℓ))
          else
            discardAlice.then
              (discardBob.then (.done KeyEnd.abort))

/-- Measure-first BB84, including the public quota-shortage branch. -/
def construction (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) :
    Program
      (system (streamRegister Unit N) (streamRegister Unit N))
      (KeyEnd Party.alice Party.bob) :=
  measureRounds pA pB Unit N <|
    (announceAliceBases N).then fun aliceBases =>
      (announceBobBases N).then fun bobBases =>
        (announceShuffle aliceBases bobBases).then fun order =>
          let control : Sampling.RawControl N :=
            ⟨aliceBases, bobBases, order⟩
          if hasQuotas : Sampling.HasQuotas nK mZ mX control then
            let selected := Sampling.selectedEmbedding control hasQuotas
            (retainAlice selected).then <|
              (retainBob selected).then <|
                (forgetAliceBases N (nK + mZ + mX)).then <|
                  (forgetBobBases N (nK + mZ + mX)).then <|
                    classicalTail
                      (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                      Sampling.packedPESel Sampling.packedXSel
                      leakEC ec δ Q
          else
            discardAlice.then
              (discardBob.then (.done KeyEnd.abort))

/-- Derive the protocol interface from the chain and its terminal values. -/
def protocol (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) : QKD.Protocol Party :=
  (construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).toProtocol

end QKD.BB84
