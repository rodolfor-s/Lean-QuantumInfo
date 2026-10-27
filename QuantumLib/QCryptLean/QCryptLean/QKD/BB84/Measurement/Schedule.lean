import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.OnFactor
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Weighted
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-!
# Semantics of the private BB84 measurement phase

This module analyzes `measureRounds` for `N` BB84 signal pairs.  At each signal
pair Alice and Bob separately apply the fixed local PMF-weighted destructive instrument to the head
qubit of their remaining stream, retain one `StoredRecord`, and recurse on the tail.  There are no
announced program nodes and no Eve register parameter.

The sequential local-instrument tree follows Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2.  Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates the
prepare-and-measure order but does not prove an arbitrary-input batch identity.  Pfister et al.,
arXiv:1506.07502v3, Sections IV--V motivate fixed per-party basis laws and late announcement.

The phase lemmas follow the recursive measurement chain.  Its auxiliary
accumulator is an untouched finite factor, not a classicality assertion.  Full-record CQ,
batch-channel, sampling, memory-freedom, and security statements are separate obligations.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty

/-- Apply the weighted destructive BB84 instrument to the stream head and preserve the tail. -/
def weightedStreamStep (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) :
    Instrument (streamRegister F (n + 1))
      (streamRegister (F × StoredRecord) n) Record :=
  Instrument.onFactor (streamInputSplit F n) (streamOutputSplit F n)
    (weightedMeasureAndRecord p)

/-- Exact Kraus entry of one weighted destructive stream-head step.

The entry is supported only when the accumulator and tail are unchanged and the stored record
matches the observed branch.  This is the one-factor `K ⊗ 1` entry law from arXiv:1210.4583,
Section 2, specialized to the weighted BB84 row instrument. -/
theorem weightedStreamStep_kraus_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (fOut fIn : F) (stored : StoredRecord)
    (tailOut : Fin n → Bit) (xs : Fin (n + 1) → Bit) :
    (weightedStreamStep p F n).kraus observed ()
        ((fOut, stored), tailOut) (fIn, xs) =
      if (fOut, tailOut) = (fIn, Fin.tail xs) ∧ stored.2 = observed then
        (Real.sqrt (p observed.1).toReal : ℂ) *
          basisUnitary observed.1 observed.2 (xs 0)
      else 0 := by
  refine (Instrument.onFactorKraus_apply (streamInputSplit F n) (streamOutputSplit F n)
    (weightedMeasureAndRecord p) observed () ((fOut, stored), tailOut) (fIn, xs)).trans ?_
  change (if (fOut, tailOut) = (fIn, Fin.tail xs) then
    (weightedMeasureAndRecord p).kraus observed () stored (xs 0) else 0) = _
  rw [weightedMeasureAndRecord_kraus_apply]
  split_ifs <;> simp_all

/-- Exact arbitrary-operator operation of one weighted destructive stream-head step.

The output spectator row `(fOut,tailOut)` and column `(fOut',tailOut')` remain independent; no
positivity, trace, self-adjointness, or equality assumption is made about `rho` or those two
coordinates. -/
theorem weightedStreamStep_operation_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (rho : Op (streamRegister F (n + 1)))
    (fOut fOut' : F) (stored stored' : StoredRecord)
    (tailOut tailOut' : Fin n → Bit) :
    ((weightedStreamStep p F n).operation observed rho)
        ((fOut, stored), tailOut) ((fOut', stored'), tailOut') =
      ((weightedMeasureAndRecord p).operation observed
        (rho.submatrix
          (fun j => (fOut, Fin.cons j tailOut))
          (fun j => (fOut', Fin.cons j tailOut'))))
        stored stored' := by
  rw [weightedStreamStep, Instrument.onFactor_operation_apply]
  rfl

/-- One stream-head branch makes the newly appended record diagonal while leaving both
accumulator coordinates and both unread-tail coordinates independent. -/
theorem weightedStreamStep_operation_newRecordDiagonal
    (p : PMF Basis) (F : Type) [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (rho : Op (streamRegister F (n + 1)))
    (f f' : F) (stored stored' : StoredRecord)
    (tail tail' : Fin n → Bit) (hne : stored ≠ stored') :
    ((weightedStreamStep p F n).operation observed rho)
        ((f, stored), tail) ((f', stored'), tail') = 0 := by
  rw [weightedStreamStep_operation_apply]
  exact weightedMeasureAndRecord_operation_storedDiagonal p observed _ stored stored' hne

/-! ## Two-party recursive program -/

/-- The two-party multipartite system before both laboratories process a stream of length `n`. -/
abbrev weightedStreamSystem (F : Type) [Fintype F] [DecidableEq F]
    (n : ℕ) : MultipartiteSystem Party :=
  system (streamRegister F n) (streamRegister F n)

end QKD.BB84.Measurement

namespace QKD.BB84
open LOCC LOCC.TwoParty Measurement

variable {End : MultipartiteSystem Party → Type 1}

/-- A zero-round measurement phase runs its continuation immediately. -/
theorem measureRounds_zero (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F]
    (k : Program (weightedStreamSystem F 0) End) : measureRounds pA pB F 0 k = k := rfl

/-- A successor round measures Alice, then Bob, then continues with the remaining stream. -/
theorem measureRounds_succ (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (k : Program (weightedStreamSystem (finishAcc F (n + 1)) 0) End) :
    measureRounds pA pB F (n + 1) k =
      (measureAlice pA F n).then
        ((measureBob pB F n).then (measureRounds pA pB (F × StoredRecord) n k)) := rfl

/-- Private measurement leaves the continuation's entire public output tree unchanged. -/
theorem measureRounds_boundary (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (k : Program (weightedStreamSystem (finishAcc F N) 0) End) :
    (measureRounds pA pB F N k).boundary = k.boundary := by
  induction N generalizing F with
  | zero => rfl
  | succ N ih => exact ih (F × StoredRecord) k

/-- Private measurement preserves every property read from its continuation's terminal values. -/
theorem measureRounds_terminal (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (k : Program (weightedStreamSystem (finishAcc F N) 0) End)
    {X : Sort*} (read : ∀ R, End R → X) (e : k.boundary.Exit) :
    read _ ((measureRounds pA pB F N k).terminal
        (cast (congrArg Boundary.Exit (measureRounds_boundary pA pB F N k).symm) e)) =
      read _ (k.terminal e) := by
  induction N generalizing F with
  | zero => rfl
  | succ N ih => exact ih (F × StoredRecord) k e

/-- The actual measurement phase's operator on the completed local records. -/
def measurementState (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ) :
    Op (weightedStreamSystem F N).total →ₗ[ℂ]
      Op (weightedStreamSystem (finishAcc F N) 0).total :=
  match N with
  | 0 => LinearMap.id
  | N + 1 =>
      ∑ a, ∑ i, ∑ b, ∑ j,
        (measurementState pA pB (F × StoredRecord) N).comp
          ((Matrix.conjLinearMap ((measureBob pB F N).successorKraus b j)).comp
            (Matrix.conjLinearMap ((measureAlice pA F N).successorKraus a i)))

/-- An arbitrary continuation receives precisely the completed-record operator of the phase. -/
theorem measureRounds_then_denote (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (k : Program (weightedStreamSystem (finishAcc F N) 0) End) :
    ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA
      pB F N k))) (Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB F N
      k)))).toLinearMap).comp
      (measureRounds pA pB F N k).denote = k.denote.comp (measurementState pA pB F N) := by
  induction N generalizing F with
  | zero =>
      apply LinearMap.ext
      intro rho
      rfl
  | succ N ih =>
      change Program (weightedStreamSystem (finishAcc (F × StoredRecord) N) 0) End at k
      change ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space
        (measureRounds_boundary pA pB (F × StoredRecord) N k))) (Equiv.cast (congrArg Boundary.space
        (measureRounds_boundary pA pB (F × StoredRecord) N k)))).toLinearMap).comp
          ((measureAlice pA F N).then ((measureBob pB F N).then
            (measureRounds pA pB (F × StoredRecord) N k))).denote = _
      dsimp +instances only [measureAlice, measureBob, PrivateAction.ofInstrument] at *
      simp only [PrivateAction.then, Program.denote_priv]
      apply LinearMap.ext
      intro rho
      simp +instances only [measurementState, measureAlice, measureBob,
        PrivateAction.ofInstrument, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro j _
      exact LinearMap.congr_fun (ih (F × StoredRecord) k) _

end QKD.BB84
