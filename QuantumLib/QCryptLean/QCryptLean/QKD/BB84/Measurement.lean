import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.UniformChoice
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates

/-!
# Destructive BB84 measurements

This module constructs the single-qubit private measure-and-record primitive and the local
actions that apply it.  A party chooses the Z or X basis uniformly, measures immediately, and
retains its local basis/outcome record.  The exact branch operation and stored-record diagonality
are proved for arbitrary finite spectator registers.

The Z/X measurement and late-announcement order follow
arXiv:quant-ph/0512258v2, `main.tex:673-736`.  Independent private basis choices and
fixed-batch late sifting follow Pfister et al., arXiv:1506.07502, Sections IV--V.  Nahar et al.,
arXiv:2403.11851, Appendix B discusses the separate permutation/measurement identity.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty

/-- The basis-change matrix: identity for Z and Hadamard for X. -/
def basisUnitary (theta : Basis) : Matrix Bit Bit ℂ :=
  match theta with
  | Basis.z => 1
  | Basis.x => Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm
      Quantum.Gates.hadamard

/-- The rank-one row Kraus matrix for outcome `x` in basis `theta`. -/
def fixedBasisKraus (theta : Basis) (x : Bit) : Matrix Unit Bit ℂ :=
  fun _ j => basisUnitary theta x j

/-- The two row Kraus matrices of either fixed basis resolve the qubit identity.

This is the single-qubit completeness equation for the Z/X measurements in
arXiv:quant-ph/0512258v2, `main.tex:673-736`. -/
theorem fixedBasisKraus_complete (theta : Basis) :
    ∑ x : Bit, (fixedBasisKraus theta x)ᴴ * fixedBasisKraus theta x = 1 := by
  have hunitary : (basisUnitary theta)ᴴ * basisUnitary theta = 1 := by
    cases theta with
    | z => simp [basisUnitary]
    | x =>
      simp only [basisUnitary, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, Quantum.Gates.hadamard_unitary,
        Matrix.submatrix_one_equiv]
  rw [← hunitary]
  ext i j
  simp [Matrix.mul_apply, fixedBasisKraus, Matrix.conjTranspose_apply]

/-- Measure one qubit in a fixed BB84 basis and discard the measured qubit. -/
def fixedBasisMeasurement (theta : Basis) : Instrument Bit Unit Bit :=
  Instrument.ofFine (fixedBasisKraus theta) (fixedBasisKraus_complete theta)

/-- Choose Z or X uniformly, measure immediately, and retain the local basis/outcome record. -/
def uniformMeasureAndRecord : Instrument Bit StoredRecord Record :=
  (Instrument.uniformChoice fixedBasisMeasurement).keeping

/-- Exact recorded Kraus entry, keeping the observed branch distinct from the stored coordinate.

The amplitude is the uniform-basis factor `1 / sqrt 2` times the selected row of the Z/X
basis-change matrix, and all other stored-record blocks vanish. -/
theorem uniformMeasureAndRecord_kraus_apply
    (observed : Record) (stored : StoredRecord) (j : Bit) :
    uniformMeasureAndRecord.kraus observed () stored j =
      if stored.2 = observed then
        ((1 : ℂ) / (Real.sqrt 2 : ℂ)) *
          basisUnitary observed.1 observed.2 j
      else 0 := by
  simp [uniformMeasureAndRecord, Instrument.keeping,
    Instrument.uniformChoice, Instrument.uniformChoiceKraus,
    Instrument.uniformChoiceScale, fixedBasisMeasurement, Instrument.ofFine,
    fixedBasisKraus, card_basis]

/-! ## Local actions -/

/-- Measure Alice's qubit while leaving an arbitrary finite spectator register untouched. -/
def measureAliceWithSpectator
    (S : Type) [Fintype S] [DecidableEq S] :
    PrivateAction (system Bit S) :=
  PrivateAction.ofInstrument .alice
    uniformMeasureAndRecord

/-- Measure Bob's qubit while leaving an arbitrary finite spectator register untouched. -/
def measureBobWithSpectator
    (S : Type) [Fintype S] [DecidableEq S] :
    PrivateAction (system S Bit) :=
  PrivateAction.ofInstrument .bob
    uniformMeasureAndRecord

/-- The two-qubit input multipartite system. -/
abbrev inputSystem : MultipartiteSystem Party := system Bit Bit

/-- The multipartite system after both laboratories have measured and retained only classical
records. -/
abbrev outputSystem : MultipartiteSystem Party := system StoredRecord StoredRecord

/-- Embed an Alice qubit value and spectator coordinate into the input joint register. -/
def aliceInputAt
    {S : Type} [Fintype S] [DecidableEq S]
    (j : Bit) (s : S) : (system Bit S).total :=
  (TwoParty.pairEquiv Bit S).symm (j, s)

/-- Embed Alice's stored record and spectator coordinate into the output joint register. -/
def aliceOutputAt
    {S : Type} [Fintype S] [DecidableEq S]
    (stored : StoredRecord) (s : S) : (measureAliceWithSpectator S).out.total :=
  ((system Bit S).splitAtSet .alice StoredRecord).symm
    (stored, fun j => match h : j.1 with
      | .alice => (j.2 h).elim
      | .bob => s)

/-- Exact lifted branch operation for Alice with an arbitrary spectator and arbitrary operator.

The two spectator coordinates are independent.  The coefficient is the probability `1/2` of
the observed basis, and the final factor is the explicitly conjugated row entry.  No positivity,
self-adjointness, or trace normalization of `rho` is assumed. -/
theorem measureAliceWithSpectator_liftedOperation_apply
    {S : Type} [Fintype S] [DecidableEq S]
    (observed : Record) (rho : Op (system Bit S).total)
    (stored stored' : StoredRecord) (s s' : S) :
    ((measureAliceWithSpectator S).liftedOperation observed rho)
        (aliceOutputAt stored s) (aliceOutputAt stored' s') =
      if stored.2 = observed ∧ stored'.2 = observed then
        (1 / 2 : ℂ) *
          ∑ j : Bit, ∑ k : Bit,
            basisUnitary observed.1 observed.2 j *
              rho (aliceInputAt j s) (aliceInputAt k s') *
                star (basisUnitary observed.1 observed.2 k)
      else 0 := by
  have hout_fst (a : StoredRecord) (t : S) :
      (((system Bit S).splitAtSet .alice StoredRecord)
        (aliceOutputAt a t)).1 = a := by
    simp [aliceOutputAt]
  have hrestore (j : Bit) (a : StoredRecord) (t : S) :
      ((system Bit S).splitAt .alice).symm
          (j, (((system Bit S).splitAtSet .alice StoredRecord)
              (aliceOutputAt a t)).2) = aliceInputAt j t := by
    apply (TwoParty.pairEquiv Bit S).injective
    apply Prod.ext <;>
      simp [aliceInputAt, aliceOutputAt, MultipartiteSystem.splitAt, TwoParty.pairEquiv]
  change ((uniformMeasureAndRecord.liftAt (system Bit S) .alice).operation observed rho)
    (aliceOutputAt stored s) (aliceOutputAt stored' s') = _
  refine (Instrument.liftAt_operation_apply (R := system Bit S) .alice
    uniformMeasureAndRecord observed rho (aliceOutputAt stored s)
      (aliceOutputAt stored' s')).trans ?_
  rw [hout_fst stored s, hout_fst stored' s']
  change uniformMeasureAndRecord.operation observed
    (rho.submatrix
      (fun x : Bit => ((system Bit S).splitAt .alice).symm
        (x, (((system Bit S).splitAtSet .alice StoredRecord) (aliceOutputAt stored s)).2))
      (fun y : Bit => ((system Bit S).splitAt .alice).symm
        (y, (((system Bit S).splitAtSet .alice StoredRecord) (aliceOutputAt stored' s')).2)))
    stored stored' = _
  simp_rw [hrestore]
  unfold uniformMeasureAndRecord
  have hkeep := Instrument.keeping_operation_apply
    (Instrument.uniformChoice fixedBasisMeasurement) observed
    (rho.submatrix (fun x => aliceInputAt x s) (fun y => aliceInputAt y s'))
    stored.1 stored'.1 stored.2 stored'.2
  refine hkeep.trans ?_
  by_cases hstored : stored.2 = observed ∧ stored'.2 = observed
  · rw [ite_eq_left hstored, ite_eq_left hstored]
    rw [Instrument.uniformChoice_operation]
    change (Fintype.card Basis : ℂ)⁻¹ *
      (∑ _ : Unit, fixedBasisKraus observed.1 observed.2 *
        rho.submatrix (fun x => aliceInputAt x s) (fun y => aliceInputAt y s') *
          (fixedBasisKraus observed.1 observed.2)ᴴ) stored.1 stored'.1 = _
    simp only [card_basis, Finset.univ_unique, Finset.sum_singleton,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      fixedBasisKraus, Fin.sum_univ_two]
    ring
  · simp [hstored]

/-- Block-diagonality in Alice's retained record, with an otherwise arbitrary spectator. -/
def AliceRecordDiagonal
    {S : Type} [Fintype S] [DecidableEq S]
    (sigma : Op (measureAliceWithSpectator S).out.total) : Prop :=
  ∀ stored stored' : StoredRecord, ∀ s s' : S,
    stored.2 ≠ stored'.2 →
      sigma (aliceOutputAt stored s) (aliceOutputAt stored' s') = 0

/-- Summing the private physical outcomes yields an output diagonal in the stored record.

This is the precise CQ invariant asserted here.  `StoredRecord` remains a quantum-register index
type in the syntax; the theorem supplies the diagonal invariant rather than treating that
type alone as a ban on coherent actions. -/
theorem measureAliceWithSpectator_sum_isRecordDiagonal
    {S : Type} [Fintype S] [DecidableEq S]
    (rho : Op (system Bit S).total) :
    AliceRecordDiagonal
      ((∑ observed : Record,
          (measureAliceWithSpectator S).liftedOperation observed) rho) := by
  intro stored stored' s s' hne
  change (∑ observed : Record, (measureAliceWithSpectator S).liftedOperation observed rho
    (aliceOutputAt stored s) (aliceOutputAt stored' s')) = 0
  apply Finset.sum_eq_zero
  intro observed _
  exact (measureAliceWithSpectator_liftedOperation_apply observed rho stored stored' s s').trans
    (ite_eq_right fun hboth => hne (hboth.1.trans hboth.2.symm))

end QKD.BB84.Measurement
