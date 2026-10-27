import Mathlib.Algebra.BigOperators.Fin
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Registers

/-! # Records -/


noncomputable section

namespace QKD.BB84.Measurement


/-- The local memory after `N` measurements, starting with memory of type `F`;
each measurement appends its basis and outcome as one `StoredRecord`. -/
@[implicit_reducible] def finishAcc (F : Type) (N : ℕ) : Type :=
  match N with
  | 0 => F
  | n + 1 => finishAcc (F × StoredRecord) n

/-- Explicit nonempty instance for a finished accumulator. -/
@[instance]
theorem nonempty_finishAcc (F : Type) [hF : Nonempty F] (N : ℕ) :
    Nonempty (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => QKD.BB84.Measurement.nonempty_finishAcc (F × StoredRecord) n

/-- Explicit finite instance for a finished accumulator. -/
@[implicit_reducible]
def finishAccFintype (F : Type) [hF : Fintype F] (N : ℕ) :
    Fintype (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => finishAccFintype (F × StoredRecord) n

instance (F : Type) [Fintype F] (N : ℕ) : Fintype (finishAcc F N) :=
  finishAccFintype F N

/-- Explicit decidable-equality instance for a finished accumulator. -/
@[implicit_reducible] def finishAccDecidableEq (F : Type) [hF : DecidableEq F] (N : ℕ) :
    DecidableEq (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => finishAccDecidableEq (F × StoredRecord) n

instance (F : Type) [DecidableEq F] (N : ℕ) : DecidableEq (finishAcc F N) :=
  finishAccDecidableEq F N

/-- Read a nested finished accumulator as its initial value and chronological record vector. -/
def finishAccForward (F : Type) (N : ℕ) (x : finishAcc F N) :
    F × (Fin N → StoredRecord) :=
  match N, x with
  | 0, f => (f, fun i => Fin.elim0 i)
  | n + 1, x =>
      let q := finishAccForward (F × StoredRecord) n x
      (q.1.1, Fin.cons q.1.2 q.2)

/-- Rebuild the nested accumulator from its initial value and chronological record vector. -/
def finishAccBackward (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) : finishAcc F N :=
  match N, q with
  | 0, q => q.1
  | n + 1, q =>
      finishAccBackward (F × StoredRecord) n
        ((q.1, q.2 0), Fin.tail q.2)

/-- Rebuilding after reading a finished accumulator is the identity. -/
theorem finishAccBackward_forward (F : Type) (N : ℕ) (x : finishAcc F N) :
    finishAccBackward F N (finishAccForward F N x) = x := by
  induction N generalizing F with
  | zero => rfl
  | succ n ih =>
      exact ih (F × StoredRecord) x

/-- Reading after rebuilding a chronological vector is the identity. -/
theorem finishAccForward_backward (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) :
    finishAccForward F N (finishAccBackward F N q) = q := by
  induction N generalizing F with
  | zero =>
      rcases q with ⟨f, records⟩
      have hrecords : records = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      subst records
      rfl
  | succ n ih =>
      rcases q with ⟨f, records⟩
      simp only [finishAccBackward, finishAccForward, ih]
      exact Prod.ext rfl (Fin.cons_self_tail records)

/-- Explicit equivalence between the nested accumulator and chronological records. -/
def finishAccEquiv (F : Type) (N : ℕ) :
    finishAcc F N ≃ F × (Fin N → StoredRecord) where
  toFun := finishAccForward F N
  invFun := finishAccBackward F N
  left_inv := finishAccBackward_forward F N
  right_inv := finishAccForward_backward F N

/-- The first coordinate read at a successor stage is the earliest appended record. -/
theorem finishAccEquiv_succ_head (F : Type) (n : ℕ)
    (x : finishAcc F (n + 1)) :
    (finishAccEquiv F (n + 1) x).2 0 =
      (finishAccEquiv (F × StoredRecord) n x).1.2 := by
  rfl

/-- The tail read at a successor stage is the recursively accumulated chronological tail. -/
theorem finishAccEquiv_succ_tail (F : Type) (n : ℕ)
    (x : finishAcc F (n + 1)) :
    Fin.tail (finishAccEquiv F (n + 1) x).2 =
      (finishAccEquiv (F × StoredRecord) n x).2 := by
  simp [finishAccEquiv, finishAccForward, Fin.tail_cons]

/-- Remove a leading `Unit` factor without using the distinct `PUnit` type. -/
def unitProdEquiv (T : Type) : Unit × T ≃ T where
  toFun q := q.2
  invFun x := ((), x)
  left_inv q := by rcases q with ⟨⟨⟩, x⟩; rfl
  right_inv _ := rfl

/-- Chronological record equivalence for the physical top-level Unit accumulator. -/
def finishAccUnitEquiv (N : ℕ) : finishAcc Unit N ≃ (Fin N → StoredRecord) :=
  (finishAccEquiv Unit N).trans (unitProdEquiv (Fin N → StoredRecord))


/-- A laboratory's stored records of type `F` together with its `n` unmeasured qubits,
whose computational basis is labelled by `Fin n → Bit`. -/
abbrev streamRegister (F : Type) (n : ℕ) : Type :=
  F × (Fin n → Bit)

/-- Split the head qubit from the untouched accumulator and tail stream. -/
def streamInputSplit (F : Type) (n : ℕ) :
    streamRegister F (n + 1) ≃ Bit × streamRegister F n where
  toFun q := (q.2 0, (q.1, Fin.tail q.2))
  invFun q := (q.2.1, Fin.cons q.1 q.2.2)
  left_inv q := by
    rcases q with ⟨f, xs⟩
    simp only
    exact Prod.ext rfl (Fin.cons_self_tail xs)
  right_inv q := by
    rcases q with ⟨x, f, xs⟩
    simp [Fin.tail_cons]

/-- Reassociate a newly stored record in front of the unchanged accumulator and tail. -/
def streamOutputSplit (F : Type) (n : ℕ) :
    streamRegister (F × StoredRecord) n ≃ StoredRecord × streamRegister F n where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv q := by rcases q with ⟨⟨f, r⟩, xs⟩; rfl
  right_inv q := by rcases q with ⟨r, f, xs⟩; rfl

/-- Remove the unique empty remaining stream and expose the chronological accumulator records.

This pure equivalence requires no finiteness, decidable-equality, or inhabitance instance for `F`.
-/
def finishedStreamEquiv (F : Type) (N : ℕ) :
    streamRegister (finishAcc F N) 0 ≃ F × (Fin N → StoredRecord) where
  toFun q := finishAccEquiv F N q.1
  invFun q := ((finishAccEquiv F N).symm q, fun i => Fin.elim0 i)
  left_inv q := by
    rcases q with ⟨acc, tail⟩
    apply Prod.ext
    · exact (finishAccEquiv F N).symm_apply_apply acc
    · funext i
      exact Fin.elim0 i
  right_inv q := (finishAccEquiv F N).apply_symm_apply q

/-- Read the local basis choice from every chronological stored record. -/
def storedBasisString {N : ℕ}
    (r : Fin N → StoredRecord) : Fin N → Basis :=
  fun i => (r i).2.1

/-- A local record retaining every basis choice and only the outcome bits selected by a fixed
embedding. -/
abbrev SelectedLocalRecord (N n : ℕ) :=
  (Fin N → Basis) × (Fin n → Bit)

/-- Keep every basis choice and only the outcome bits at the rounds chosen by `f`,
listing the retained bits in the order given by `f`. -/
def selectedLocalRecord {n N : ℕ} (f : Fin n ↪ Fin N)
    (q : streamRegister (finishAcc Unit N) 0) : SelectedLocalRecord N n :=
  let r := (finishedStreamEquiv Unit N q).2
  (storedBasisString r, fun i => (r (f i)).2.2)

/-- A laboratory's record after all `N` qubits have been measured, containing every
basis choice and outcome in order and no unmeasured qubits. -/
abbrev CompletedLocalRecord (N : ℕ) :=
  streamRegister (finishAcc Unit N) 0

/-- Read the basis chosen for each of the `N` rounds from a laboratory's completed
measurement record. -/
def completedBasisString (N : ℕ) (q : CompletedLocalRecord N) :
    Fin N → Basis :=
  storedBasisString ((finishedStreamEquiv Unit N q).2)

end QKD.BB84.Measurement
