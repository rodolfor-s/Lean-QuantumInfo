import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Instrument
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Paired

/-!
# Accepted raw keys and measure-then-hash protocols

Every internal register is a finite type. The raw-key reference is explicit and
positive definite. The hash acts on natural classical types and retains the
public seed. Protocol factorization is an equality of actual output matrices.
-/

noncomputable section

namespace InfoTheory.Postselection

open Matrix Quantum.Operators Quantum.Channels
open scoped ComplexOrder
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL

variable (A B K C CE CP Raw E : Type*)
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] (k : ℕ)

/-- A protocol's accepted raw-key states with a common positive-definite reference. -/
structure RawKeyMeasurement where
  /-- The real and ideal protocol variants and their accept map. -/
  toProtocol : PMQKDProtocol A B K C CE CP Raw k
  /-- Accepted raw-key CQ states for each normalized IID component. -/
  rawKeyCQ : DensityOp (A × B) → CQState Raw E
  /-- A common subnormalized reference for the conditional entropy. -/
  sigmaE : SubDensityOp E
  /-- The reference has full support. -/
  sigmaE_posDef : sigmaE.toOp.PosDef

variable {A B K C CE CP Raw E k}

/-- The total probability of acceptance on a single-round IID component. -/
def RawKeyMeasurement.pAcc (M : RawKeyMeasurement A B K C CE CP Raw E k)
    (σ : DensityOp (A × B)) : ℝ := ∑ x, ((M.rawKeyCQ σ).stateMap x).trace

/-- Instrument and public-seed hashing semantics for one supported key length. -/
structure MeasureThenHash (M : RawKeyMeasurement A B K C CE CP Raw E k)
    (Public Seed Key : Type*) [Fintype Public] [Fintype Seed] [Nonempty Seed]
    [Fintype Key] [Nonempty Key] [DecidableEq Seed] [DecidableEq Key]
    [DecidableEq Public]
    (l' : ℕ) where
  /-- The transcript and purification reference form the conditioning register. -/
  condEquiv : (Public × (Fin k → A × B)) ≃ E
  /-- Completely positive accepted blocks on the round-grouped input. -/
  instrument : Raw → Operation (Fin k → A × B) Public
  /-- Positivity of every instrument block under reference extension. -/
  instrument_isCompletelyPositive : ∀ x, IsCompletelyPositive (instrument x)
  /-- Accepted instrument weight is at most one. -/
  instrument_weight_le_one : ∀ ρ : DensityOp (Fin k → A × B),
    ∑ x, (instrument x ρ.toOp).trace.re ≤ 1
  /-- The stored IID raw-key states are the instrument applied to canonical purifications. -/
  rawKeyCQ_stateMap_toOp : ∀ σ x,
    ((M.rawKeyCQ σ).stateMap x).toOp = Matrix.reindex condEquiv condEquiv
      (mapTensorId (instrument x) (Fin k → A × B) (σ.tensorPow k).purification.toOp)
  /-- The public seeded hash family. -/
  hash : HashFamily Seed Raw Key
  /-- Two-universality of the supplied family. -/
  isTwoUniversal_hash : hash.IsTwoUniversal
  /-- The key alphabet has the prescribed bit length. -/
  card_key : Fintype.card Key = 2 ^ l'
  /-- The physical encoding of transcript, public seed and key, including an abort slot. -/
  encode : Matrix (K × ((C × CE) × CP)) (Public × (Seed × Key)) ℂ
  /-- The physical output encoding is an isometry. -/
  encode_isometry : encodeᴴ * encode = 1
  /-- The accept projection is completely positive. -/
  acceptProj_isCompletelyPositive : IsCompletelyPositive M.toProtocol.acceptProj
  /-- The accepted real output is the public-seed extractor output. -/
  acceptProj_variantReal : ∀ ρ : DensityOp (Fin k → A × B),
    M.toProtocol.acceptProj (M.toProtocol.variantReal l'
      (Matrix.reindex (Quantum.Symmetry.pairFunctions A B k)
        (Quantum.Symmetry.pairFunctions A B k) ρ.toOp)) =
      encode * (InfoTheory.QuantumLHL.SeedKey.output hash
        (CQState.ofInstrument instrument instrument_isCompletelyPositive
          instrument_weight_le_one ρ)).toJointDensity.toOp * encodeᴴ
  /-- The accepted ideal output replaces the public-seed/key pair by its uniform target. -/
  acceptProj_variantIdeal : ∀ ρ : DensityOp (Fin k → A × B),
    M.toProtocol.acceptProj (M.toProtocol.variantIdeal l'
      (Matrix.reindex (Quantum.Symmetry.pairFunctions A B k)
        (Quantum.Symmetry.pairFunctions A B k) ρ.toOp)) =
      encode * (uniformCQState (C := Seed × Key)
        (CQState.ofInstrument instrument instrument_isCompletelyPositive
          instrument_weight_le_one ρ).quantumMarginal).toJointDensity.toOp * encodeᴴ

end InfoTheory.Postselection
