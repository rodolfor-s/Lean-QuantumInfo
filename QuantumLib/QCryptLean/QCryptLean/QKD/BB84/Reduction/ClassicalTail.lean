import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.ParameterEstimation
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SeedTagSyndrome
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.Quantum.Operators.Basic

/-!
# The finite kernel of the classical BB84 tail

The test-discussion induction, fused announcement, public decision and private terminal actions
provide the exact output formula for arbitrary complex input operators.
-/

open Quantum.Operators (Op)

open scoped BigOperators
noncomputable section
namespace QKD.BB84.Reduction
open LOCC LOCC.TwoParty FiniteKey Measurement

/-- The terminal kernel checks the accepted keys and gives unit weight after a discard. -/
def terminalKeyKernel (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (seed : KeyHashSeed n ℓ peSel)
    (syndrome : Bits leakEC) (flag : Fin 2)
    (q : (FinalStage.flagBoundary ℓ flag).space) (a b : Bits n) : ℂ :=
  if h : flag = 0 then
    let registers := cast (congrArg (fun B : Boundary Party => B.space)
      (show FinalStage.flagBoundary ℓ flag = .leaf (FinalStage.keySystem ℓ) from
        ite_eq_left h)) q
    if pairEquiv _ _ registers.2 =
      (aliceKey n ℓ peSel seed a,
        bobKey n ℓ peSel leakEC ec seed syndrome b) then 1 else 0
  else 1

/-- The actual hashing or discarding branch has the declared terminal kernel. -/
theorem flagBranch_denote_diag (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (seed : KeyHashSeed n ℓ peSel)
    (syndrome : Bits leakEC) (flag : Bool)
    (rho : Op (system (Bits n) (Bits n)).total)
    (q : (if flag then
      (hashAlice (B := Bits n) seed).then
        ((correctAndHashBob ec seed syndrome).then (.done (KeyEnd.keys ℓ)))
    else (discardAlice (A := Bits n) (B := Bits n)).then
      (discardBob.then (.done KeyEnd.abort))).boundary.space) :
    (if flag then
      (hashAlice (B := Bits n) seed).then
        ((correctAndHashBob ec seed syndrome).then (.done (KeyEnd.keys ℓ)))
    else (discardAlice (A := Bits n) (B := Bits n)).then
      (discardBob.then (.done KeyEnd.abort))).denote rho q q =
      ∑ b, ∑ a, terminalKeyKernel n ℓ peSel leakEC ec seed syndrome
        ((Equiv.boolNot.trans finTwoEquiv.symm) flag)
        (flagBranchSpaceEquiv n ℓ peSel leakEC ec seed syndrome flag q) a b *
          rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) := by
  revert q
  cases flag with
  | true =>
      intro q
      change (Boundary.leaf (system (Bits ℓ) (Bits ℓ))).space at q
      rcases q with ⟨⟨⟩, q⟩
      obtain ⟨⟨ka, kb⟩, rfl⟩ := (pairEquiv (Bits ℓ) (Bits ℓ)).symm.surjective q
      refine (hashAlice_correctAndHashBob_denote_apply n ℓ peSel leakEC ec seed syndrome
        rho ka ka kb kb).trans ?_
      simp only [and_self]
      apply Finset.sum_congr rfl
      intro b _
      have hsum {I : Type} [Fintype I] (p : Prop) [Decidable p] (f : I → ℂ) :
          (if p then ∑ i, f i else 0) = ∑ i, if p then f i else 0 := by
        simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      refine (hsum _ _).trans ?_
      apply Finset.sum_congr rfl
      intro a _
      change _ = (if (ka, kb) = (aliceKey n ℓ peSel seed a,
        bobKey n ℓ peSel leakEC ec seed syndrome b) then 1 else 0) * _
      by_cases ha : ka = aliceKey n ℓ peSel seed a <;>
        by_cases hb : kb = bobKey n ℓ peSel leakEC ec seed syndrome b <;>
          simp only [Prod.mk.injEq, ha, hb, and_self, true_and, false_and, ite_true,
            ite_false, one_mul, zero_mul]
  | false =>
    intro q
    change (Boundary.leaf (system Unit Unit)).space at q
    rcases q with ⟨⟨⟩, q⟩
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, rfl⟩ := (pairEquiv Unit Unit).symm.surjective q
    refine (discardAlice_discardBob_denote_apply n rho).trans ?_
    change _ = ∑ b, ∑ a, (1 : ℂ) *
      rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b))
    simp only [one_mul]


/-- Bob's public decision restricts the terminal kernel to the computed accept flag. -/
def decisionKernel (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (seeds : KeyHashSeedPairEV n ℓ ℓEV peSel) (tag : Bits ℓEV)
    (syndrome : Bits leakEC) (q : (FinalStage.boundary ℓ).space)
    (a b : Bits n) : ℂ :=
  let z := Boundary.publicSpaceEquiv (FinalStage.flagBoundary ℓ) q
  if acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome b =
        (Equiv.boolNot.trans finTwoEquiv.symm).symm z.1 then
    terminalKeyKernel n ℓ peSel leakEC ec seeds.1 syndrome z.1 z.2 a b else 0

/-- Reading the natural decision output restricts the terminal kernel to the announced Boolean. -/
private theorem decisionKernel_decisionSpaceEquiv
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (seeds : KeyHashSeedPairEV n ℓ ℓEV peSel) (tag : Bits ℓEV)
    (syndrome : Bits leakEC) :
    let p := ((announceAccept (A := Bits n) (xSel := xSel) ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
        if flag then
          (hashAlice seeds.1).then
            ((correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
        else discardAlice.then (discardBob.then (.done KeyEnd.abort)))
    ∀ (q : p.boundary.space) (a b : Bits n),
      decisionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests seeds tag syndrome
        (decisionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests seeds tag syndrome q) a b =
      if acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
          (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome b = q.1.1 then
        terminalKeyKernel n ℓ peSel leakEC ec seeds.1 syndrome
          ((Equiv.boolNot.trans finTwoEquiv.symm) q.1.1)
          (flagBranchSpaceEquiv n ℓ peSel leakEC ec seeds.1 syndrome q.1.1
            ⟨q.1.2, q.2⟩) a b else 0 := by
  intro p q a b
  rcases q with ⟨⟨flag, e⟩, q⟩
  cases flag <;> rfl

/-- The actual decision followed by termination has the decision kernel. -/
theorem decision_denote_diag (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (seeds : KeyHashSeedPairEV n ℓ ℓEV peSel) (tag : Bits ℓEV)
    (syndrome : Bits leakEC)
    (rho : Op (system (Bits n) (Bits n)).total)
    :
    let k : Bool → Program (system (Bits n) (Bits n))
        (KeyEnd Party.alice Party.bob) := fun flag => (if flag then
        (hashAlice (B := Bits n) seeds.1).then
          ((correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
      else (discardAlice (A := Bits n) (B := Bits n)).then
        (discardBob.then (.done KeyEnd.abort)))
    let p := (announceAccept (A := Bits n) (xSel := xSel) ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then k
    ∀ q : p.boundary.space, p.denote rho q q =
      ∑ b, ∑ a, decisionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests seeds tag syndrome
        (decisionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests seeds tag syndrome q) a b *
          rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) := by
  intro k p q
  change (Σ e : Σ flag : Bool, (k flag).boundary.Exit,
    ((k e.1).boundary.system e.2).total) at q
  refine (Program.denote_ofInstrument_publicSpaceEquiv_apply
    (R := system (Bits n) (Bits n)) .bob
    (Instrument.nondemolitionReadout (acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome))
        (Equiv.refl _) k rho q).trans ?_
  refine (flagBranch_denote_diag n ℓ peSel leakEC ec seeds.1 syndrome q.1.1 _ _).trans ?_
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  refine (congrArg (fun z : ℂ => (_ : ℂ) * z)
    (announceAccept_operation_diag n m ℓEV peSel xSel leakEC ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome q.1.1 rho a b)).trans ?_
  rw [decisionKernel_decisionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q
    tests seeds tag syndrome q a b]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rfl

/-- The fused cell enforces Alice's public data and contributes the uniform seed weight. -/
def seedDiscussionKernel (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (z : (KeyHashSeedPairEV n ℓ ℓEV peSel × (Bits ℓEV × Bits leakEC)) ×
      (FinalStage.boundary ℓ).space) (a b : Bits n) : ℂ :=
  if tagAndSyndrome n ℓ ℓEV peSel leakEC ec
      z.1.1 a =
        z.1.2 then
    (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ *
      decisionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests z.1.1 z.1.2.1 z.1.2.2 z.2 a b
  else 0

/-- Multiplying the fused kernel separates the announcement weight from the decision kernel. -/
private theorem seedDiscussionKernel_mul
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (z : (KeyHashSeedPairEV n ℓ ℓEV peSel × (Bits ℓEV × Bits leakEC)) ×
      (FinalStage.boundary ℓ).space) (a b : Bits n) (c : ℂ) :
    seedDiscussionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests z a b * c =
      decisionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests z.1.1 z.1.2.1 z.1.2.2 z.2 a b *
        (if tagAndSyndrome n ℓ ℓEV peSel leakEC ec z.1.1 a = z.1.2 then
          (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ * c else 0) := by
  simp only [seedDiscussionKernel]
  split_ifs <;> ring

/-- Reading a seed announcement feeds that cell's operation to its continuation. -/
private theorem seedDiscussion_denote_continuation
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (k : KeyHashSeedPairEV n ℓ ℓEV peSel × Bits ℓEV × Bits leakEC →
      Program (system (Bits n) (Bits n)) (KeyEnd Party.alice Party.bob))
    (rho : Op (system (Bits n) (Bits n)).total)
    (q : ((announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).then k).boundary.space) :
    ((announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).then k).denote rho q q =
      (k q.1.1).denote ((announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).successorOperation
        q.1.1 rho) ⟨q.1.2, q.2⟩ ⟨q.1.2, q.2⟩ := by
  refine (Program.denote_then_publicSpaceEquiv_symm_apply
    (announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec) (Equiv.refl _)
    (fun _ => rfl) k rho q.1.1 ⟨q.1.2, q.2⟩ ⟨q.1.2, q.2⟩).trans ?_
  rfl

/-- The verification announcement and decision have the fused cell's kernel. -/
theorem seedDiscussion_denote_diag
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (rho : Op (system (Bits n) (Bits n)).total)
    :
    let k : KeyHashSeedPairEV n ℓ ℓEV peSel × Bits ℓEV × Bits leakEC →
        Program (system (Bits n) (Bits n)) (KeyEnd Party.alice Party.bob) := fun cell =>
      let (seeds, tag, syndrome) := cell
      ((announceAccept (A := Bits n) (xSel := xSel) ec δ Q
        (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice (B := Bits n) seeds.1).then
              ((correctAndHashBob (A := Bits ℓ) ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
          else (discardAlice (A := Bits n) (B := Bits n)).then
            ((discardBob (A := Unit) (B := Bits n)).then (.done KeyEnd.abort)))
    let p := (announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).then k
    ∀ q : p.boundary.space, p.denote rho q q =
      ∑ b, ∑ a, seedDiscussionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
        (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q) a b *
          rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) := by
  intro k p q
  change (Σ e : Σ cell : KeyHashSeedPairEV n ℓ ℓEV peSel × Bits ℓEV × Bits leakEC,
    (k cell).boundary.Exit, ((k e.1).boundary.system e.2).total) at q
  rcases q with ⟨⟨⟨seeds, tag, syndrome⟩, e⟩, v⟩
  refine (seedDiscussion_denote_continuation n ℓ ℓEV peSel leakEC ec k rho
    ⟨⟨(seeds, tag, syndrome), e⟩, v⟩).trans ?_
  refine (decision_denote_diag n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
    seeds tag syndrome _ ⟨e, v⟩).trans ?_
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  refine (congrArg (fun z : ℂ => (_ : ℂ) * z)
    (announceSeedTagSyndrome_operation_diag n ℓ ℓEV peSel leakEC ec
      seeds (tag, syndrome) rho a b)).trans ?_
  exact (seedDiscussionKernel_mul n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
    ((seeds, tag, syndrome),
      decisionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests seeds tag syndrome ⟨e, v⟩)
    a b _).symm

/-- The tail kernel combines its disclosed test bits with the fused cell and final decision. -/
def classicalTailKernel (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (z : ClassicalTailData n m ℓ ℓEV peSel leakEC × (FinalStage.boundary ℓ).space)
    (a b : Bits n) : ℂ :=
  let tests := fun j => (z.1.alicePE j, z.1.bobPE j)
  if TestReadoutMatches (peRoundIdx peSel) tests a b then
    seedDiscussionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
      ((z.1.seedPair, z.1.evTag, z.1.syndrome), z.2) a b else 0

/-- Test and seed coordinates expose the factors of the complete classical kernel. -/
private theorem classicalTailKernel_classicalTailSpaceEquiv
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
  let k : (Fin (min n m) → Bit × Bit) →
      Program (system (Bits n) (Bits n)) (KeyEnd Party.alice Party.bob) :=
    fun tests =>
      (announceSeedTagSyndrome ℓ ℓEV ec).then fun cell =>
        let (seeds, tag, syndrome) := cell
        (announceAccept (xSel := xSel) ec δ Q
          (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then <|
              (correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))
  ∀ (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) (a b : Bits n),
    let z := announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q
    classicalTailKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q
      (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q) a b =
        if TestReadoutMatches (peRoundIdx peSel) z.1 a b then
          seedDiscussionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q z.1
            (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q z.1 z.2) a b
        else 0 := by
  intro k q a b z
  rfl

/-- The actual tail's diagonal output is given by the finite classical kernel. -/
theorem classicalTail_denote_diag (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (rho : Op (system (Bits n) (Bits n)).total)
    (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote rho q q =
      ∑ b, ∑ a, classicalTailKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q
        (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q) a b *
          rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) := by
  let k : (Fin (min n m) → Bit × Bit) →
      Program (system (Bits n) (Bits n)) (KeyEnd Party.alice Party.bob) :=
    fun tests =>
      (announceSeedTagSyndrome ℓ ℓEV ec).then fun cell =>
        let (seeds, tag, syndrome) := cell
        (announceAccept (xSel := xSel) ec δ Q
          (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then <|
              (correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))
  change (announceTests (min n m) (peRoundIdx peSel) k).boundary.space at q
  change (announceTests (min n m) (peRoundIdx peSel) k).denote rho q q = _
  rw [announceTests_denote_diag (min n m) (peRoundIdx peSel) k
    (fun tests q => seedDiscussionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
      (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q))
    (fun tests => seedDiscussion_denote_diag n m ℓ ℓEV peSel xSel leakEC ec δ Q tests)]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simpa only [ite_mul, zero_mul] using congrArg
    (fun z : ℂ => z * rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)))
    (classicalTailKernel_classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q a b).symm

/-- The tail's terminal key or discard actions make every complete output diagonal. -/
theorem classicalTail_denote_offDiagonal_zero
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (rho : Op (system (Bits n) (Bits n)).total)
    (x y : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space)
    (hxy : x ≠ y) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote rho x y = 0 := by
  unfold classicalTail at x y hxy ⊢
  refine announceTests_denote_offDiagonal_zero _ _ _ ?_ rho x y hxy
  intro tests sigma u v huv
  refine Program.denote_announced_offDiagonal_zero
    (announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec)
    (Equiv.refl _) (fun _ => rfl) _ ?_ sigma u v huv
  intro cell tau w z hwz
  rcases cell with ⟨seeds, tag, syndrome⟩
  dsimp only at w z hwz ⊢
  refine Program.denote_announced_offDiagonal_zero
    (announceAccept (A := Bits n) (xSel := xSel) ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome)
      (Equiv.refl Bool) (fun _ => rfl) _ ?_ tau w z hwz
  dsimp +instances only [announceSeedTagSyndrome, announceAccept, hashAlice, correctAndHashBob,
    discardAlice, discardBob, AnnouncedAction.ofInstrument, PrivateAction.ofInstrument] at *
  intro flag upsilon a b hab
  revert a b hab
  cases flag with
  | true =>
    intro a b hab
    change (Boundary.leaf (system (Bits ℓ) (Bits ℓ))).space at a b
    exact functionAndForget_pair_denote_offDiagonal_zero
      (aliceKey n ℓ peSel seeds.1)
      (bobKey n ℓ peSel leakEC ec seeds.1 syndrome)
      (KeyEnd.keys ℓ) upsilon a b hab
  | false =>
    intro a b hab
    apply False.elim
    apply hab
    apply (Boundary.leafSpaceEquiv (system Unit Unit)).injective
    funext p
    cases p <;> exact Unit.ext _ _

/-- Every entry of the actual tail is given by its diagonal finite kernel. -/
theorem classicalTail_denote_apply (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (rho : Op (system (Bits n) (Bits n)).total)
    (q q' : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote rho q q' =
      if q = q' then
        ∑ b, ∑ a, classicalTailKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q
          (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q) a b *
            rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b))
      else 0 := by
  by_cases h : q = q'
  · subst q'
    rw [ite_eq_left rfl]
    exact classicalTail_denote_diag n m ℓ ℓEV peSel xSel leakEC ec δ Q rho q
  · rw [ite_eq_right h]
    exact classicalTail_denote_offDiagonal_zero n m ℓ ℓEV peSel xSel leakEC ec δ Q rho q q' h

/-- The actual PE and fused public data generated by a raw input and a sampled seed pair. -/
def rawClassicalTailDataOf
    (n m ell ellEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ell ellEV peSel) :
    QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC :=
  let tagSyn := QKD.BB84.tagAndSyndrome n ell ellEV peSel leakEC ec
      st (x .alice)
  { alicePE := fun j =>
      x .alice (peRoundIdx (m := m) peSel j)
    bobPE := fun j =>
      x .bob (peRoundIdx (m := m) peSel j)
    seedPair := st
    evTag := tagSyn.1
    syndrome := tagSyn.2 }

/-- The final point records the announced accepting keys or the key-free abort leaf. -/
noncomputable def finalStagePoint (ell : ℕ) (flag : Fin 2) (a b : Bits ell) :
    (FinalStage.boundary ell).space :=
  if flag = 0 then ⟨⟨0, ()⟩, (pairEquiv _ _).symm (a, b)⟩
  else ⟨⟨1, ()⟩, (pairEquiv Unit Unit).symm ((), ())⟩

/-- The literal final-stage output generated by semantic public data and one raw input. -/
noncomputable def rawClassicalTailFinalPoint
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) : (FinalStage.boundary ell).space :=
  let flag := acceptFlag n m ellEV peSel xSel leakEC ec delta Q
    d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)
  finalStagePoint ell ((Equiv.boolNot.trans finTwoEquiv.symm) flag)
    (aliceKey n ell peSel d.seedPair.1 (x .alice))
    (bobKey n ell peSel leakEC ec d.seedPair.1 d.syndrome (x .bob))

/-- The complete analytical output point, retaining every public cell and the ordered local keys. -/
noncomputable def rawClassicalTailOutputPoint
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ell ellEV peSel) :
    (QKD.BB84.rawClassicalTailBoundary n m ell ellEV peSel leakEC).space :=
  let d := rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st
  (Boundary.graftSpaceEquiv
      (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
      (fun _ => FinalStage.boundary ell)).symm
    ⟨(QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC).symm d,
      rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x⟩


/-- The decision kernel selects exactly the generated final point. -/
theorem decisionKernel_eq_indicator
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (d : ClassicalTailData n m ℓ ℓEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) (q : (FinalStage.boundary ℓ).space) :
    decisionKernel n m ℓ ℓEV peSel xSel leakEC ec δ Q
      (fun j => (d.alicePE j, d.bobPE j)) d.seedPair d.evTag d.syndrome q
        (x .alice) (x .bob) =
      if q = rawClassicalTailFinalPoint n m ℓ ℓEV peSel xSel leakEC ec δ Q d x
      then 1 else 0 := by
  classical
  rcases q with ⟨⟨flag, e⟩, q⟩
  fin_cases flag <;> cases e
  · obtain ⟨⟨ka, kb⟩, rfl⟩ := (pairEquiv (Bits ℓ) (Bits ℓ)).symm.surjective q
    change (if acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = true then
        terminalKeyKernel n ℓ peSel leakEC ec d.seedPair.1 d.syndrome 0
          ⟨(), (pairEquiv (Bits ℓ) (Bits ℓ)).symm (ka, kb)⟩
          (x .alice) (x .bob) else 0) = _
    unfold rawClassicalTailFinalPoint finalStagePoint
    generalize acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = f
    cases f with
    | true =>
      let keys := (aliceKey n ℓ peSel d.seedPair.1 (x .alice),
        bobKey n ℓ peSel leakEC ec d.seedPair.1 d.syndrome (x .bob))
      change (if (pairEquiv _ _) ((pairEquiv _ _).symm (ka, kb)) = keys then 1 else 0) =
        if (⟨⟨0, ()⟩, (pairEquiv _ _).symm (ka, kb)⟩ : (FinalStage.boundary ℓ).space) =
          ⟨⟨0, ()⟩, (pairEquiv _ _).symm keys⟩ then 1 else 0
      rw [Equiv.apply_symm_apply]
      apply if_congr ?_ rfl rfl
      constructor
      · intro h
        exact congrArg (fun ks => (⟨⟨0, ()⟩, (pairEquiv _ _).symm ks⟩ :
          (FinalStage.boundary ℓ).space)) h
      · intro h
        have hkeys := congrArg (FinalStage.outputEquiv ℓ) h
        change Sum.inl ((pairEquiv _ _) ((pairEquiv _ _).symm (ka, kb))) =
          (Sum.inl ((pairEquiv _ _) ((pairEquiv _ _).symm keys)) :
            (Bits ℓ × Bits ℓ) ⊕ Unit) at hkeys
        simpa only [Equiv.apply_symm_apply, Sum.inl.injEq] using hkeys
    | false =>
      simp only [Fin.isValue]
      apply Eq.symm
      apply ite_eq_right
      intro h
      exact Fin.zero_ne_one (congrArg (fun z : (FinalStage.boundary ℓ).space => z.1.1) h)
  · obtain ⟨⟨⟨⟩, ⟨⟩⟩, rfl⟩ := (pairEquiv Unit Unit).symm.surjective q
    change (if acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = false then
        terminalKeyKernel n ℓ peSel leakEC ec d.seedPair.1 d.syndrome 1
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩
          (x .alice) (x .bob) else 0) = _
    unfold rawClassicalTailFinalPoint finalStagePoint
    generalize acceptFlag n m ℓEV peSel xSel leakEC ec δ Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = f
    cases f with
    | true =>
      simp only [Fin.isValue]
      apply Eq.symm
      apply ite_eq_right
      intro h
      exact Fin.zero_ne_one (congrArg (fun z : (FinalStage.boundary ℓ).space => z.1.1) h).symm
    | false => rfl

open Classical in
/-- The complete scalar kernel selects the data and final point generated by the raw strings. -/
theorem classicalTailKernel_eq_indicator
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) (q : (FinalStage.boundary ell).space) :
    classicalTailKernel n m ell ellEV peSel xSel leakEC ec delta Q (d, q)
        (x .alice) (x .bob) =
      if rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x d.seedPair = d ∧
          q = rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x then
        (Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ)⁻¹
      else 0 := by
  classical
  have hDataEq
      (d : QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC)
      (x : (FinalStage.rawSystem n).total) :
      rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x d.seedPair = d ↔
        (∀ j, x .bob (peRoundIdx (m := m) peSel j) =
            d.bobPE j) ∧
          (∀ j, x .alice (peRoundIdx (m := m) peSel j) = d.alicePE j) ∧
          QKD.BB84.tagAndSyndrome n ell ellEV peSel leakEC ec
              d.seedPair
              (x .alice) = (d.evTag, d.syndrome) := by
    constructor
    · intro hd
      refine ⟨congrFun (congrArg QKD.BB84.ClassicalTailData.bobPE hd),
        congrFun (congrArg QKD.BB84.ClassicalTailData.alicePE hd), ?_⟩
      have hp :
          (QKD.BB84.tagAndSyndrome n ell ellEV peSel leakEC ec
                d.seedPair
                (x .alice)) = (d.evTag, d.syndrome) :=
        Prod.ext (congrArg QKD.BB84.ClassicalTailData.evTag hd)
          (congrArg QKD.BB84.ClassicalTailData.syndrome hd)
      exact hp
    · rintro ⟨hb, ha, hv⟩
      cases d
      dsimp only at hb ha hv
      simp only [rawClassicalTailDataOf, hv]
      congr 1
      · exact funext ha
      · exact funext hb
  have hd : rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x d.seedPair = d ↔
      TestReadoutMatches (peRoundIdx peSel) (fun j => (d.alicePE j, d.bobPE j))
        (x .alice) (x .bob) ∧
      tagAndSyndrome n ell ellEV peSel leakEC ec
        d.seedPair (x .alice) =
          (d.evTag, d.syndrome) := by
    rw [hDataEq]
    simp only [TestReadoutMatches, forall_and]
    tauto
  simp only [classicalTailKernel, seedDiscussionKernel, decisionKernel_eq_indicator]
  rw [hd]
  split_ifs <;> simp_all


/-- The actual classical tail emits the point determined by its raw input and seed. -/
theorem rawClassicalTailProgram_output_apply
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (rho : Quantum.Operators.Op (FinalStage.rawSystem n).total)
    (q q' : (QKD.BB84.rawClassicalTailBoundary n m ell ellEV peSel leakEC).space) :
    (Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv n m ell ellEV peSel xSel leakEC ec
      delta Q) (rawClassicalTailOutputEquiv n m ell ellEV peSel xSel leakEC ec delta Q)).toLinearMap
      ((classicalTail n m ell ellEV peSel xSel leakEC ec delta Q).denote rho) q q' =
      if q = q' then
        ∑ x : (FinalStage.rawSystem n).total,
          ∑ st : KeyHashSeedPairEV n ell ellEV peSel,
            if rawClassicalTailOutputPoint n m ell ellEV peSel xSel leakEC ec
                delta Q x st = q then
              (Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ)⁻¹ *
                rho x x
            else 0
      else 0 := by
  classical
  let E := rawClassicalTailOutputEquiv n m ell ellEV peSel xSel leakEC ec delta Q
  change (classicalTail n m ell ellEV peSel xSel leakEC ec delta Q).denote rho
    (E.symm q) (E.symm q') = _
  by_cases hqq : q = q'
  swap
  · rw [ite_eq_right hqq]
    exact classicalTail_denote_offDiagonal_zero n m ell ellEV peSel xSel leakEC ec delta Q
      rho (E.symm q) (E.symm q') (fun h => hqq (E.symm.injective h))
  subst q'
  rw [ite_eq_left rfl, classicalTail_denote_diag]
  have hOutputPoint
      (e : (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC).Exit)
      (a : (FinalStage.boundary ell).space)
      (x : (FinalStage.rawSystem n).total)
      (st : KeyHashSeedPairEV n ell ellEV peSel) :
      rawClassicalTailOutputPoint n m ell ellEV peSel xSel leakEC ec delta Q x st =
          (Boundary.graftSpaceEquiv
            (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
            (fun _ => FinalStage.boundary ell)).symm ⟨e, a⟩ ↔
        rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st =
            QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC e ∧
          rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q
            (QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC e) x = a := by
    dsimp only [rawClassicalTailOutputPoint]
    constructor
    · intro hp
      have hs := (Boundary.graftSpaceEquiv
        (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
        (fun _ => FinalStage.boundary ell)).symm.injective hp
      have he := congrArg Sigma.fst hs
      have hd : rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st =
          QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC e :=
        (Equiv.symm_apply_eq _).mp he
      have ha :
          rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q
            (rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st) x = a :=
        eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      exact ⟨hd, by rwa [hd] at ha⟩
    · rintro ⟨hd, ha⟩
      simp only [hd, Equiv.symm_apply_apply, ha]
      rfl
  obtain ⟨⟨e, q⟩, rfl⟩ := (Boundary.graftSpaceEquiv
    (classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
    (fun _ => FinalStage.boundary ell)).symm.surjective q
  let d := classicalTailExitEquiv n m ell ellEV peSel leakEC e
  have hcoords : classicalTailSpaceEquiv n m ell ellEV peSel xSel leakEC ec delta Q
      (E.symm ((Boundary.graftSpaceEquiv
        (classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
        (fun _ => FinalStage.boundary ell)).symm ⟨e, q⟩)) = (d, q) := by
    dsimp +instances only [E, rawClassicalTailOutputEquiv, Equiv.trans,
      Equiv.symm, DFunLike.coe, EquivLike.coe, Equiv.toFun, Function.comp]
    rw [Equiv.right_inv, Equiv.right_inv]
    dsimp +instances only [Equiv.sigmaEquivProd, Equiv.sigmaCongr, Equiv.sigmaCongrLeft,
      Equiv.sigmaCongrRight, Equiv.trans, Equiv.refl, Equiv.symm, Function.comp_def,
      DFunLike.coe, EquivLike.coe, Equiv.toFun, id]
    simp only [eq_rec_constant]
    rfl
  rw [hcoords]
  rw [Finset.sum_comm]
  refine (Fintype.sum_prod_type (fun ab : Bits n × Bits n =>
    classicalTailKernel n m ell ellEV peSel xSel leakEC ec delta Q (d, q) ab.1 ab.2 *
      rho ((pairEquiv _ _).symm ab) ((pairEquiv _ _).symm ab))).symm.trans ?_
  have hsum := Equiv.sum_comp (pairEquiv (Bits n) (Bits n)).symm
    (fun x => classicalTailKernel n m ell ellEV peSel xSel leakEC ec delta Q
      (d, q) (x .alice) (x .bob) * rho x x)
  refine hsum.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [classicalTailKernel_eq_indicator]
  symm
  rw [Fintype.sum_eq_single d.seedPair]
  · simp only [hOutputPoint, d]
    by_cases hd : rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x
        (classicalTailExitEquiv n m ell ellEV peSel leakEC e).seedPair =
          classicalTailExitEquiv n m ell ellEV peSel leakEC e <;>
      by_cases hq : q = rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q
        (classicalTailExitEquiv n m ell ellEV peSel leakEC e) x <;>
      simp only [hd, hq, eq_comm, and_true, and_false,
        ite_true, ite_false, zero_mul]
  · intro st hst
    apply ite_eq_right
    intro hp
    have hd := (hOutputPoint e q x st).mp hp
    exact hst (congrArg ClassicalTailData.seedPair hd.1)

end QKD.BB84.Reduction
