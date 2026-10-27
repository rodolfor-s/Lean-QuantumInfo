import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-! # Final Stage -/


open Quantum.Operators (Op)

open scoped BigOperators

noncomputable section

namespace QKD.BB84.FinalStage
open LOCC LOCC.TwoParty FiniteKey Measurement


/-- The two raw bit-string registers entering the final decision stage. -/
@[reducible] def rawSystem (n : ℕ) : MultipartiteSystem Party :=
  TwoParty.system (Bits n) (Bits n)

/-- The accepted output multipartite system containing Alice's and Bob's bit-string keys. -/
@[reducible] def keySystem (ℓ : ℕ) : MultipartiteSystem Party :=
  TwoParty.system (Bits ℓ) (Bits ℓ)

/-- The abort output multipartite system, containing no Alice or Bob key register. -/
@[reducible] def abortSystem : MultipartiteSystem Party :=
  TwoParty.system Unit Unit

/-- The branch selected by the semantic flag: digit zero accepts and digit one aborts. -/
def flagBoundary (ℓ : ℕ) (flag : Fin 2) : Boundary Party :=
  if flag = 0 then .leaf (keySystem ℓ) else .leaf abortSystem

/-- The public boundary of the direct final stage, indexed by the semantic decision flag. -/
def boundary (ℓ : ℕ) : Boundary Party :=
  .announce (Fin 2) (flagBoundary ℓ)


/-- Each branch of the semantic decision is a completed leaf, so it declares exactly one complete
public exit. -/
instance flagBoundaryExitUnique (ℓ : ℕ) (flag : Fin 2) :
    Unique (flagBoundary ℓ flag).Exit := by
  unfold flagBoundary
  split <;> exact inferInstance

/-- **A complete public exit of the final stage is exactly the announced decision flag.**

The branch selected by the flag is a completed leaf, so the flag is this stage's entire public
record: there is no further announcement to read, and no exit is lost. -/
def exitEquiv (ℓ : ℕ) : (boundary ℓ).Exit ≃ Fin 2 where
  toFun e := e.1
  invFun flag := ⟨flag, default⟩
  left_inv e := by
    obtain ⟨flag, leaf⟩ := e
    exact congrArg (Sigma.mk flag) (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- **What survives the final stage.**  When the announced flag accepts, both parties hold a
`2 ^ ℓ`-element key register; when it aborts, neither holds a key register at all — the raw data
was discarded rather than replaced by a zero key. -/
theorem system_eq (ℓ : ℕ) (e : (boundary ℓ).Exit) :
    (boundary ℓ).system e = if e.1 = 0 then keySystem ℓ else abortSystem := by
  obtain ⟨flag, leaf⟩ := e
  change (flagBoundary ℓ flag).system leaf = if flag = 0 then keySystem ℓ else abortSystem
  revert leaf
  unfold flagBoundary
  split
  · rename_i h
    rw [ite_eq_left h]
    intro leaf
    rfl
  · rename_i h
    rw [ite_eq_right h]
    intro leaf
    rfl

/-- Convert the semantic final flag into the key disposition of the heterogeneous output. -/
def disposition (ℓ : ℕ) (flag : Fin 2) : BoundaryKeyLayout.Disposition :=
  if flag = 0 then .accept ℓ else .abort

/-- Local ownership of the accepted keys and the key-free abort output. -/
def outputLayout (ℓ : ℕ) : QKD.OutputLayout (boundary ℓ) where
  alice := .alice
  bob := .bob
  alice_ne_bob := by decide
  disposition e := disposition ℓ e.1
  AliceResidual _ := Unit
  BobResidual _ := Unit
  finAliceResidual _ := inferInstance
  decAliceResidual _ := inferInstance
  nonemptyAliceResidual _ := inferInstance
  finBobResidual _ := inferInstance
  decBobResidual _ := inferInstance
  nonemptyBobResidual _ := inferInstance
  aliceSplit e := by
    rcases e with ⟨flag, e⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at e
      cases e
      change Bits ℓ ≃ Bits ℓ × Unit
      exact (Equiv.prodPUnit (Bits ℓ)).symm
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at e
      cases e
      change Unit ≃ Unit × Unit
      exact (Equiv.prodPUnit Unit).symm
  bobSplit e := by
    rcases e with ⟨flag, e⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at e
      cases e
      change Bits ℓ ≃ Bits ℓ × Unit
      exact (Equiv.prodPUnit (Bits ℓ)).symm
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at e
      cases e
      change Unit ≃ Unit × Unit
      exact (Equiv.prodPUnit Unit).symm

/-- The heterogeneous output's key disposition at a complete exit is the disposition of the flag
that exit announced. -/
@[simp] theorem outputLayout_disposition (ℓ : ℕ) (e : (boundary ℓ).Exit) :
    (outputLayout ℓ).disposition e = disposition ℓ e.1 := rfl

end QKD.BB84.FinalStage


namespace QKD.BB84
open LOCC LOCC.TwoParty FiniteKey Measurement

/-- Bob's decision readout retains exactly the raw values that yield the announced flag. -/
theorem announceAccept_operation_diag
    (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (min n m) → Fin 2) (seed : KeyHashSeed n ℓEV peSel)
    (tag : Bits ℓEV) (syndrome : Bits leakEC) (flag : Bool)
    (rho : Op (system (Bits n) (Bits n)).total) (a b : Bits n) :
    (announceAccept (A := Bits n) (xSel := xSel) ec δ Q
      as bs seed tag syndrome).successorOperation
        flag rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) =
      if acceptFlag n m ℓEV peSel xSel leakEC ec δ Q as bs seed tag syndrome b =
          flag then rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0 := by
  refine (AnnouncedAction.successorOperation_bob_apply
    (Instrument.nondemolitionReadout
      (acceptFlag n m ℓEV peSel xSel leakEC ec δ Q as bs seed tag syndrome))
        id flag rho a a b b).trans ?_
  simp only [Instrument.nondemolitionReadout_operation_apply, and_self, Matrix.submatrix_apply]

/-- The two accepted key actions read the raw diagonal and retain exactly their computed keys. -/
theorem hashAlice_correctAndHashBob_denote_apply
    (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ℓ peSel) (syndrome : Bits leakEC)
    (rho : Op (system (Bits n) (Bits n)).total)
    (a a' b b' : Bits ℓ) :
    ((hashAlice (B := Bits n) seed).then <|
      (correctAndHashBob ec seed syndrome).then (.done (KeyEnd.keys ℓ))).denote rho
        ⟨(), (pairEquiv _ _).symm (a, b)⟩ ⟨(), (pairEquiv _ _).symm (a', b')⟩ =
      ∑ y : Bits n,
        if b = bobKey n ℓ peSel leakEC ec seed syndrome y ∧
            b' = bobKey n ℓ peSel leakEC ec seed syndrome y then
          ∑ x : Bits n,
            if a = aliceKey n ℓ peSel seed x ∧
                a' = aliceKey n ℓ peSel seed x then
              rho ((pairEquiv _ _).symm (x, y)) ((pairEquiv _ _).symm (x, y))
            else 0
        else 0 :=
  functionAndForget_pair_denote_apply _ _ _ rho a a' b b'

/-- Both discard actions preserve exactly the input trace at the declared abort terminal. -/
theorem discardAlice_discardBob_denote_apply (n : ℕ)
    (rho : Op (system (Bits n) (Bits n)).total) :
    ((discardAlice (A := Bits n) (B := Bits n)).then <|
      discardBob.then (.done KeyEnd.abort)).denote rho
        ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩
        ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩ =
      ∑ b : Bits n, ∑ a : Bits n,
        rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) :=
  discard_pair_denote_apply _ rho

end QKD.BB84
