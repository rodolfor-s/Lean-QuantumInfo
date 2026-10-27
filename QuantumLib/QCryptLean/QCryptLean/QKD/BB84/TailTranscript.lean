import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.Uniform
import QCryptLean.LOCC.Transcript
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SeedTagSyndrome
import QCryptLean.QKD.BB84.TailTranscript.Raw
import QCryptLean.QKD.BB84.Transcript
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft

/-!
# Natural public data of the classical tail

The program announces bits, seeds, tags and syndromes directly. This module groups those
public values into the data consumed by the final decision, preserving announcement order.
-/

noncomputable section

namespace QKD.BB84

/-- Joint seed, tag and syndrome in the analytical transcript. -/
abbrev FusedPublic
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :=
  KeyHashSeedPairEV n ℓ ℓEV peSel × (Measurement.Bits ℓEV × Measurement.Bits leakEC)


open LOCC QKD.BB84 Measurement
open LOCC.TwoParty
open QKD.BB84.FiniteKey

/-! ## The chronological announcement word of the classical tail -/

/-- Chronological transcript word for Bob/Alice PE cells followed by the fused seed, tag, and
syndrome announcement. -/
def classicalTailWord (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) : TList :=
  PE.transcriptWord (min n m)
    (.cons (FusedPublic n ℓ ℓEV peSel leakEC) .nil)

/-- Uniform pre-decision boundary reached after all PE and fused public cells. -/
abbrev classicalPreDecisionBoundary (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) : Boundary Party :=
  Boundary.uniform (FinalStage.rawSystem n)
    (classicalTailWord n m ℓ ℓEV peSel leakEC)

/-! ## The semantic data those cells carry -/

/-- Semantic values supplied to the final decision, in Alice/Bob PE order despite the physical
Bob-then-Alice announcement chronology. -/
structure ClassicalTailData (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) where
  /-- Alice’s announced parameter-estimation bits in the selected test positions. -/
  alicePE : Fin (min n m) → Bit
  /-- Bob’s announced parameter-estimation bits in the selected test positions. -/
  bobPE : Fin (min n m) → Bit
  /-- Public seeds for privacy amplification and error verification. -/
  seedPair : KeyHashSeedPairEV n ℓ ℓEV peSel
  /-- The announced error-verification hash tag. -/
  evTag : Bits ℓEV
  /-- The announced error-correction syndrome. -/
  syndrome : Bits leakEC

/-- Decode the Bob-then-Alice PE cells and the fused public cell into the semantic
data consumed by the final decision. -/
noncomputable def classicalTailRawDataEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    PreDecisionRaw (min n m)
        (FusedPublic n ℓ ℓEV peSel leakEC) ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC where
  toFun raw :=
    { alicePE := raw.alicePERaw
      bobPE := raw.bobPERaw
      seedPair := raw.fusedRaw.1
      evTag := raw.fusedRaw.2.1
      syndrome := raw.fusedRaw.2.2 }
  invFun d :=
    { bobPERaw := d.bobPE
      alicePERaw := d.alicePE
      fusedRaw := (d.seedPair, d.evTag, d.syndrome) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group the chronological transcript into the natural values consumed by the final decision. -/
noncomputable def classicalTailDataEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    Transcript (classicalTailWord n m ℓ ℓEV peSel leakEC) ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC :=
  (preDecisionRawEquiv
    (min n m)
    (FusedPublic n ℓ ℓEV peSel leakEC)).trans
      (classicalTailRawDataEquiv n m ℓ ℓEV peSel leakEC)

/-- Decode a complete pre-decision public exit into the semantic data supplied to the final
stage. -/
noncomputable def classicalTailExitEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC :=
  (Boundary.uniformExitEquiv (FinalStage.rawSystem n)
    (classicalTailWord n m ℓ ℓEV peSel leakEC)).trans
      (classicalTailDataEquiv n m ℓ ℓEV peSel leakEC)

/-- Public boundary obtained by attaching the semantic final decision and key/abort leaves to
every complete pre-decision transcript. -/
def rawClassicalTailBoundary
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) : Boundary Party :=
  (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).graft
    (fun _ => FinalStage.boundary ℓ)

/-- Lift the final-stage local key ownership through the retained pre-decision public prefix. -/
noncomputable def rawClassicalTailOutputLayout
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    QKD.OutputLayout (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (fun _ => FinalStage.outputLayout ℓ) (fun _ => rfl) (fun _ => rfl)

end QKD.BB84
