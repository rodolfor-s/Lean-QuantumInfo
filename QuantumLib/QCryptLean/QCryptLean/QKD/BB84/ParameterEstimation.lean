import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-!
# Public disclosure of the parameter-estimation bits

The actual `announceTests` recursion publishes Bob's cell before Alice's at each position.
These equivalences decode the resulting public tree into semantic test pairs and the output
of its continuation, retaining every announced value.
-/

open Quantum.Operators (Op)

open scoped BigOperators

noncomputable section

namespace QKD.BB84
open LOCC LOCC.TwoParty Measurement

variable {End : MultipartiteSystem Party → Type 1}

/-- Regroup two chronological bit cells and a tail as one vector of semantic pairs. -/
private def testConsExitEquiv {r : ℕ} (K : (Fin (r + 1) → Bit × Bit) → Type) :
    (Σ b : Bit, Σ a : Bit, Σ rest : Fin r → Bit × Bit,
      K (Fin.cons (a, b) rest)) ≃ Σ tests, K tests  where
  toFun e := ⟨Fin.cons (e.2.1, e.1) e.2.2.1, e.2.2.2⟩
  invFun e := ⟨(e.1 0).2, (e.1 0).1, Fin.tail e.1,
    cast (congrArg K (Fin.cons_self_tail e.1).symm) e.2⟩
  left_inv e := by
    rcases e with ⟨b, a, rest, e⟩
    dsimp only [Fin.cons_zero]
    congr 1
  right_inv e := by
    rcases e with ⟨tests, e⟩
    simp


/-- The discussion's computed exits are the disclosed bit pairs and continuation exits. -/
def announceTestsExitEquiv {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End) :
    (announceTests r idx k).boundary.Exit ≃ Σ tests, (k tests).boundary.Exit := by
  induction r with
  | zero =>
      letI : Unique (Fin 0 → Bit × Bit) :=
        ⟨⟨Fin.elim0⟩, fun _ => Subsingleton.elim _ _⟩
      exact (Equiv.uniqueSigma fun tests => (k tests).boundary.Exit).symm
  | succ r ih =>
      change (Σ b : Bit, Σ a : Bit,
        (announceTests r (Fin.tail idx) fun rest =>
          k (Fin.cons (a, b) rest)).boundary.Exit) ≃ _
      exact (Equiv.sigmaCongrRight fun b =>
        Equiv.sigmaCongrRight fun a =>
          ih (Fin.tail idx) (fun rest =>
            k (Fin.cons (a, b) rest))).trans
              (testConsExitEquiv fun tests => (k tests).boundary.Exit)

/-- The discussion output consists of its semantic test pairs and continuation output. -/
def announceTestsSpaceEquiv {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End) :
    (announceTests r idx k).boundary.space ≃ Σ tests, (k tests).boundary.space := by
  induction r with
  | zero =>
      letI : Unique (Fin 0 → Bit × Bit) :=
        ⟨⟨Fin.elim0⟩, fun _ => Subsingleton.elim _ _⟩
      exact (Equiv.uniqueSigma fun tests => (k tests).boundary.space).symm
  | succ r ih =>
      let next := fun b a rest => k (Fin.cons (a, b) rest)
      exact (Boundary.publicSpaceEquiv _).trans <|
        (Equiv.sigmaCongrRight fun b =>
          (Boundary.publicSpaceEquiv _).trans <|
            Equiv.sigmaCongrRight fun a =>
              ih (Fin.tail idx) (next b a)) |>.trans <|
        testConsExitEquiv (fun tests => (k tests).boundary.space)

/-- Decoding a successor discussion reads its two head cells before the remaining tests. -/
theorem announceTestsSpaceEquiv_succ {n r : ℕ} (idx : Fin (r + 1) → Fin n)
    (k : (Fin (r + 1) → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (q : (announceTests (r + 1) idx k).boundary.space) :
    let next := fun b a rest => k (Fin.cons (a, b) rest)
    let afterAlice := fun b a => announceTests r (Fin.tail idx) (next b a)
    let afterBob := fun b => (announceAliceTest (idx 0)).then (afterAlice b)
    let qb := Boundary.publicSpaceEquiv (fun b => (afterBob b).boundary) q
    let qa := Boundary.publicSpaceEquiv (fun a => (afterAlice qb.1 a).boundary) qb.2
    let rest := announceTestsSpaceEquiv r (Fin.tail idx) (next qb.1 qa.1) qa.2
    announceTestsSpaceEquiv (r + 1) idx k q =
      ⟨Fin.cons (qa.1, qb.1) rest.1, rest.2⟩ := rfl

/-- Decoding the discussion preserves its terminal system. -/
theorem system_announceTestsExitEquiv {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (e : (announceTests r idx k).boundary.Exit) :
    (announceTests r idx k).boundary.system e =
      (k (announceTestsExitEquiv r idx k e).1).boundary.system
        (announceTestsExitEquiv r idx k e).2 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rcases e with ⟨b, a, e⟩
      exact ih (Fin.tail idx) _ e

/-- Decoding the discussion preserves the value declared at its actual termination. -/
theorem terminal_announceTestsExitEquiv {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (e : (announceTests r idx k).boundary.Exit) :
    HEq ((announceTests r idx k).terminal e)
      ((k (announceTestsExitEquiv r idx k e).1).terminal
        (announceTestsExitEquiv r idx k e).2) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rcases e with ⟨b, a, e⟩
      exact ih (Fin.tail idx) _ e

/-- Bob's announced test value retains exactly the matching raw diagonal entries. -/
theorem announceBobTest_operation_diag {n : ℕ} (i : Fin n) (value : Bit)
    (rho : Op (system (Bits n) (Bits n)).total) (a b : Bits n) :
    (announceBobTest (A := Bits n) i).successorOperation value rho
        ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) =
      if b i = value then
        rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0 := by
  refine (AnnouncedAction.successorOperation_bob_apply
    (Instrument.nondemolitionReadout ((fun x : Bits n => x i)))
      (Equiv.refl _) value rho a a b b).trans ?_
  simp only [Instrument.nondemolitionReadout_operation_apply, and_self, Matrix.submatrix_apply]

/-- Alice's announced test value retains exactly the matching raw diagonal entries. -/
theorem announceAliceTest_operation_diag {n : ℕ} (i : Fin n) (value : Bit)
    (rho : Op (system (Bits n) (Bits n)).total) (a b : Bits n) :
    (announceAliceTest (B := Bits n) i).successorOperation value rho
        ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) =
      if a i = value then
        rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0 := by
  refine (AnnouncedAction.successorOperation_alice_apply
    (Instrument.nondemolitionReadout ((fun x : Bits n => x i)))
      (Equiv.refl _) value rho a a b b).trans ?_
  simp only [Instrument.nondemolitionReadout_operation_apply, and_self, Matrix.submatrix_apply]

/-- Raw strings agree with all test values returned by the discussion. -/
def TestReadoutMatches {n r : ℕ} (idx : Fin r → Fin n)
    (tests : Fin r → Bit × Bit) (a b : Bits n) : Prop :=
  ∀ j, a (idx j) = (tests j).1 ∧
    b (idx j) = (tests j).2

/-- Agreement with a finite test transcript is decidable. -/
instance {n r : ℕ} (idx : Fin r → Fin n) (tests : Fin r → Bit × Bit)
    (a b : Bits n) : Decidable (TestReadoutMatches idx tests a b) :=
  inferInstanceAs (Decidable (∀ j, a (idx j) = (tests j).1 ∧
    b (idx j) = (tests j).2))

/-- No test constraints are imposed by an empty discussion. -/
theorem testReadoutMatches_zero {n : ℕ} (idx : Fin 0 → Fin n)
    (tests : Fin 0 → Bit × Bit) (a b : Bits n) :
    TestReadoutMatches idx tests a b := fun j => Fin.elim0 j

/-- The next test constrains the disclosed head pair and all remaining test positions. -/
theorem testReadoutMatches_cons {n r : ℕ} (idx : Fin (r + 1) → Fin n)
    (x y : Bit) (tests : Fin r → Bit × Bit) (a b : Bits n) :
    TestReadoutMatches idx (Fin.cons (x, y) tests) a b ↔
      a (idx 0) = x ∧
      b (idx 0) = y ∧
      TestReadoutMatches (Fin.tail idx) tests a b := by
  simp only [TestReadoutMatches, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail_def, and_assoc]

/-- The discussion restricts a diagonal continuation kernel to the actual announced tests. -/
theorem announceTests_denote_diag
    {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (K : ∀ tests, (k tests).boundary.space → Bits n → Bits n → ℂ)
    (hK : ∀ tests rho q, (k tests).denote rho q q =
      ∑ b, ∑ a, K tests q a b *
        rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)))
    (rho : Op (system (Bits n) (Bits n)).total)
    (q : (announceTests r idx k).boundary.space) :
    let z := announceTestsSpaceEquiv r idx k q
    (announceTests r idx k).denote rho q q =
      ∑ b, ∑ a, if TestReadoutMatches idx z.1 a b then
        K z.1 z.2 a b * rho ((pairEquiv _ _).symm (a, b))
          ((pairEquiv _ _).symm (a, b)) else 0 := by
  induction r generalizing rho with
  | zero =>
      change (k Fin.elim0).denote rho q q =
        ∑ b, ∑ a, if TestReadoutMatches idx Fin.elim0 a b then
          K Fin.elim0 q a b * rho ((pairEquiv _ _).symm (a, b))
            ((pairEquiv _ _).symm (a, b)) else 0
      simp only [testReadoutMatches_zero, ite_true]
      exact hK Fin.elim0 rho q
  | succ r ih =>
      let next := fun b a rest => k (Fin.cons (a, b) rest)
      let afterAlice := fun b a => announceTests r (Fin.tail idx) (next b a)
      let afterBob := fun b => (announceAliceTest (idx 0)).then (afterAlice b)
      let bob := announceBobTest (A := Bits n) (idx 0)
      let alice := announceAliceTest (B := Bits n) (idx 0)
      let qb := Boundary.publicSpaceEquiv (fun b => (afterBob b).boundary) q
      let qa := Boundary.publicSpaceEquiv (fun a => (afterAlice qb.1 a).boundary) qb.2
      let rest := announceTestsSpaceEquiv r (Fin.tail idx) (next qb.1 qa.1) qa.2
      refine (Program.denote_ofInstrument_publicSpaceEquiv_apply
        (R := system (Bits n) (Bits n)) .bob
        (Instrument.nondemolitionReadout ((fun x : Bits n => x (idx 0))))
          (Equiv.refl _) afterBob rho q).trans ?_
      refine (Program.denote_ofInstrument_publicSpaceEquiv_apply
        (R := system (Bits n) (Bits n)) .alice
        (Instrument.nondemolitionReadout ((fun x : Bits n => x (idx 0))))
          (Equiv.refl _) (afterAlice qb.1)
            (bob.successorOperation (qb.1) rho) qb.2).trans ?_
      refine (ih (Fin.tail idx) (next qb.1 qa.1)
        (fun tests => K (Fin.cons (qa.1, qb.1) tests))
        (fun tests => hK (Fin.cons (qa.1, qb.1) tests))
          _ qa.2).trans ?_
      rw [announceTestsSpaceEquiv_succ]
      change (∑ b, ∑ a, if TestReadoutMatches (Fin.tail idx) rest.1 a b then
        K (Fin.cons (qa.1, qb.1) rest.1) rest.2 a b *
          (alice.successorOperation (qa.1)
            (bob.successorOperation (qb.1) rho))
              ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0) =
        ∑ b, ∑ a, if TestReadoutMatches idx
          (Fin.cons (qa.1, qb.1) rest.1) a b then
          K (Fin.cons (qa.1, qb.1) rest.1) rest.2 a b *
            rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      have hentry := (announceAliceTest_operation_diag (idx 0) (qa.1)
        (bob.successorOperation (qb.1) rho) a b).trans
          (congrArg (fun z : ℂ =>
            if a (idx 0) = qa.1 then z else 0)
              (announceBobTest_operation_diag (idx 0) (qb.1) rho a b))
      refine (congrArg (fun z : ℂ => if TestReadoutMatches (Fin.tail idx) rest.1 a b then
        K (Fin.cons (qa.1, qb.1) rest.1) rest.2 a b * z
          else 0) hentry).trans ?_
      simp only [testReadoutMatches_cons]
      have hscalar (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (c z : ℂ) :
          (if r then c * (if p then if q then z else 0 else 0) else 0) =
            (if p ∧ q ∧ r then c * z else 0) := by
        by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
          simp only [hp, hq, hr, ite_true, ite_false, and_self, false_and, and_false, mul_zero]
      exact hscalar _ _ _ _ _

/-- The recursive discussion preserves diagonal continuation outputs for every input operator. -/
theorem announceTests_denote_offDiagonal_zero
    {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (hk : ∀ tests rho x y, x ≠ y → (k tests).denote rho x y = 0)
    (rho : Op (system (Bits n) (Bits n)).total)
    (x y : (announceTests r idx k).boundary.space) (hxy : x ≠ y) :
    (announceTests r idx k).denote rho x y = 0 := by
  induction r generalizing rho with
  | zero => exact hk Fin.elim0 rho x y hxy
  | succ r ih =>
      let next := fun b a => announceTests r (Fin.tail idx)
        (fun rest => k (Fin.cons (a, b) rest))
      refine Program.denote_announced_offDiagonal_zero
        (announceBobTest (A := Bits n) (idx 0)) (Equiv.refl _) (fun _ => rfl)
        (fun b => (announceAliceTest (idx 0)).then (next b)) ?_ rho x y hxy
      intro b sigma u v huv
      refine Program.denote_announced_offDiagonal_zero
        (announceAliceTest (B := Bits n) (idx 0)) (Equiv.refl _) (fun _ => rfl)
        (next b) ?_ sigma u v huv
      intro a tau w z hwz
      exact ih (Fin.tail idx)
        (fun rest => k (Fin.cons (a, b) rest))
        (fun rest => hk (Fin.cons (a, b) rest)) tau w z hwz

/-- Decoding a discussion output decodes its exit and leaves its quantum coordinate intact. -/
theorem announceTestsSpaceEquiv_exit {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (q : (announceTests r idx k).boundary.space) :
    (⟨(announceTestsSpaceEquiv r idx k q).1,
      (announceTestsSpaceEquiv r idx k q).2.1⟩ : Σ tests, (k tests).boundary.Exit) =
        announceTestsExitEquiv r idx k q.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rcases q with ⟨⟨b, a, e⟩, q⟩
      exact congrArg (fun z : Σ tests, (k (Fin.cons
        (a, b) tests)).boundary.Exit =>
          (⟨Fin.cons (a, b) z.1, z.2⟩ :
            Σ tests, (k tests).boundary.Exit)) (ih (Fin.tail idx) _ ⟨e, q⟩)
/-- Decoding the discussion transports its final register without changing its value. -/
theorem announceTestsSpaceEquiv_snd_heq {n : ℕ} (r : ℕ) (idx : Fin r → Fin n)
    (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n)) End)
    (q : (announceTests r idx k).boundary.space) :
    HEq (announceTestsSpaceEquiv r idx k q).2.2 q.2 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rcases q with ⟨⟨b, a, e⟩, q⟩
      exact ih (Fin.tail idx) _ ⟨e, q⟩

end QKD.BB84
