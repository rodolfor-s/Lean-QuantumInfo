import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.Quantum.Operators.Basic

/-! # Late Public Control -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty
open QKD.BB84.Sampling


/-- Alice's basis announcement is Alice's own action. -/
@[simp] theorem completedBasisAliceAnnouncement_actor (N : ℕ) :
    (announceAliceBases (B := CompletedLocalRecord N) N).actor = Party.alice := rfl

/-- Bob's basis announcement is Bob's own action. -/
@[simp] theorem completedBasisBobAnnouncement_actor (N : ℕ) :
    (announceBobBases (A := CompletedLocalRecord N) N).actor = Party.bob := rfl

/-- **The announced basis string is the stored one.**  The announcement map is the identity on the
readout's observed value, so the public transcript cell carries the actual string and not an
internal encoding of it. -/
@[simp] theorem completedBasisAliceAnnouncement_announce (N : ℕ) (a : Fin N → Basis) :
    (announceAliceBases (B := CompletedLocalRecord N) N).announce a = a := rfl

/-- The same for Bob's announcement. -/
@[simp] theorem completedBasisBobAnnouncement_announce (N : ℕ) (b : Fin N → Basis) :
    (announceBobBases (A := CompletedLocalRecord N) N).announce b = b := rfl

/-- **The basis announcement is the nondestructive readout of `completedBasisString`.**  Its
single Kraus matrix at the announced value `a` is the projector onto the completed records whose
stored basis string is exactly `a`, so the record itself is retained. -/
theorem completedBasisAliceAnnouncement_kraus (N : ℕ) (a : Fin N → Basis)
    (r : (announceAliceBases (B := CompletedLocalRecord N) N).krausIndex a) :
    (announceAliceBases (B := CompletedLocalRecord N) N).kraus a r =
      Instrument.nondemolitionReadoutKraus (completedBasisString N) a := rfl

/-- The same for Bob's announcement. -/
theorem completedBasisBobAnnouncement_kraus (N : ℕ) (b : Fin N → Basis)
    (r : (announceBobBases (A := CompletedLocalRecord N) N).krausIndex b) :
    (announceBobBases (A := CompletedLocalRecord N) N).kraus b r =
      Instrument.nondemolitionReadoutKraus (completedBasisString N) b := rfl


/-- The shuffle is sampled and announced by Alice. -/
@[simp] theorem shuffleAnnouncement_actor (N : ℕ) (a b : Fin N → Basis) :
    (announceShuffle (B := CompletedLocalRecord N) a b).actor = Party.alice := rfl

/-- The announcement is exactly the sampled ordering. -/
@[simp] theorem shuffleAnnouncement_announce (N : ℕ) (a b : Fin N → Basis)
    (o : Shuffle a b) :
    (announceShuffle (B := CompletedLocalRecord N) a b).announce o = o := rfl


/-- Key-free terminal multipartite system for a quota-shortage branch. -/
abbrev lateSelectionAbortSystem : MultipartiteSystem Party := system Unit Unit

/-- Quota-dependent terminal boundary for one fully public raw control. -/
def lateSelectionLeaf (N nK mZ mX : ℕ)
    (omega : RawControl N) : Boundary Party :=
  if HasQuotas nK mZ mX omega then
    .leaf (weightedSelectedRecordSystem N (nK + mZ + mX))
  else .leaf lateSelectionAbortSystem

/-- Complete late-public transcript: Alice's bases, Bob's bases, and the dependent matched-round
ordering, followed by the quota-dependent terminal leaf. -/
noncomputable def lateSelectionBoundary (N nK mZ mX : ℕ) : Boundary Party :=
  .announce (Fin N → Basis) fun a =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩


/-- The complete public exit determined by a raw control, including its basis strings and exact
shuffle. -/
def lateSelectionExit (N nK mZ mX : ℕ)
    (omega : RawControl N) :
    (lateSelectionBoundary N nK mZ mX).Exit := by
  rcases omega with ⟨a, b, order⟩
  change Σ a : Fin N → Basis, Σ b : Fin N → Basis,
    Σ order : Shuffle a b,
      (lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).Exit
  refine ⟨a, b, order, ?_⟩
  by_cases h : HasQuotas nK mZ mX ⟨a, b, order⟩
  · rw [lateSelectionLeaf, ite_eq_left h]
    exact ()
  · rw [lateSelectionLeaf, ite_eq_right h]
    exact ()

/-- Embed a successful selected-record row into the complete late-public output space at the
specified raw-control exit. -/
noncomputable def lateSelectionSuccessAt
    (N nK mZ mX : ℕ) (omega : RawControl N)
    (h : HasQuotas nK mZ mX omega)
    (q : SelectedLocalRecord N (nK + mZ + mX) ×
      SelectedLocalRecord N (nK + mZ + mX)) :
    (lateSelectionBoundary N nK mZ mX).space := by
  unfold lateSelectionBoundary
  refine (Boundary.publicSpaceEquiv (P := Party) (fun a : Fin N → Basis =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩)).symm ⟨omega.a, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party) (fun b : Fin N → Basis =>
    .announce (Shuffle omega.a b) fun order =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, b, order⟩)).symm ⟨omega.b, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party)
    (fun order : Shuffle omega.a omega.b =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, omega.b, order⟩)).symm
        ⟨omega.order, ?_⟩
  have hleaf : lateSelectionLeaf N nK mZ mX omega =
      .leaf (weightedSelectedRecordSystem N (nK + mZ + mX)) := by
    simp [lateSelectionLeaf, h]
  exact cast (congrArg Boundary.space hleaf).symm
    ((Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv
          (SelectedLocalRecord N (nK + mZ + mX))
          (SelectedLocalRecord N (nK + mZ + mX))).symm q))

/-- Embed the unique key-free shortage row into the complete late-public output space at the
specified raw-control exit. -/
noncomputable def lateSelectionAbortAt
    (N nK mZ mX : ℕ) (omega : RawControl N)
    (h : ¬ HasQuotas nK mZ mX omega) :
    (lateSelectionBoundary N nK mZ mX).space := by
  unfold lateSelectionBoundary
  refine (Boundary.publicSpaceEquiv (P := Party) (fun a : Fin N → Basis =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩)).symm ⟨omega.a, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party) (fun b : Fin N → Basis =>
    .announce (Shuffle omega.a b) fun order =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, b, order⟩)).symm ⟨omega.b, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party)
    (fun order : Shuffle omega.a omega.b =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, omega.b, order⟩)).symm
        ⟨omega.order, ?_⟩
  have hleaf : lateSelectionLeaf N nK mZ mX omega =
      .leaf lateSelectionAbortSystem := by
    simp [lateSelectionLeaf, h]
  exact cast (congrArg Boundary.space hleaf).symm
    ((Boundary.leafSpaceEquiv lateSelectionAbortSystem).symm
      ((TwoParty.pairEquiv Unit Unit).symm ((), ())))

/-- Reconstruct one complete chronological stored-record vector from a basis string and a bit
string. -/
def completeStoredRecords {N : ℕ}
    (a : Fin N → Basis) (x : Fin N → Bit) : Fin N → StoredRecord :=
  fun i => ((), (a i, x i))

/-- The completed measurements after the announced control and the two private retentions. -/
def selectedControlState (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N) (h : HasQuotas nK mZ mX omega)
    (rho : Op (weightedStreamSystem Unit N).total) :
    Op (weightedSelectedRecordSystem N (nK + mZ + mX)).total :=
  (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
    (selectedEmbedding omega h)).successorOperation ()
      ((retainAlice (B := CompletedLocalRecord N)
        (selectedEmbedding omega h)).successorOperation ()
        ((announceShuffle omega.a omega.b).successorOperation omega.order
          ((announceBobBases N).successorOperation omega.b
            ((announceAliceBases N).successorOperation omega.a
              (measurementState pA pB Unit N rho)))))

end QKD.BB84.Measurement

namespace QKD.BB84
open LOCC LOCC.TwoParty

/-- The quota-dependent terminal leaf has one complete public exit. -/
instance lateSelectionLeafUnique (N nK mZ mX : ℕ) (omega : Sampling.RawControl N) :
    Unique (Measurement.lateSelectionLeaf N nK mZ mX omega).Exit := by
  unfold Measurement.lateSelectionLeaf
  split <;> exact inferInstance

/-- The final multipartite system of the quota-dependent terminal leaf is selected by the same quota
test. -/
theorem lateSelectionLeaf_system (N nK mZ mX : ℕ) (omega : Sampling.RawControl N)
    (e : (Measurement.lateSelectionLeaf N nK mZ mX omega).Exit) :
    (Measurement.lateSelectionLeaf N nK mZ mX omega).system e =
      if Sampling.HasQuotas nK mZ mX omega then
        Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)
      else Measurement.lateSelectionAbortSystem := by
  revert e
  unfold Measurement.lateSelectionLeaf
  split
  · rename_i h
    rw [ite_eq_left h]
    intro e
    rfl
  · rename_i h
    rw [ite_eq_right h]
    intro e
    rfl

/-- Complete late-selection exits are exactly the announced basis strings and exact dependent
shuffle.  The quota-dependent leaf exit is `Unit` and contributes no extra choice. -/
def lateSelectionExitEquiv (N nK mZ mX : ℕ) :
    (Measurement.lateSelectionBoundary N nK mZ mX).Exit ≃
      Sampling.RawControl N where
  toFun e := ⟨e.1, e.2.1, e.2.2.1⟩
  invFun := Measurement.lateSelectionExit N nK mZ mX
  left_inv e := by
    rcases e with ⟨a, b, order, leaf⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact Subsingleton.elim _ _
  right_inv omega := by
    rcases omega with ⟨a, b, order⟩
    rfl


end QKD.BB84
