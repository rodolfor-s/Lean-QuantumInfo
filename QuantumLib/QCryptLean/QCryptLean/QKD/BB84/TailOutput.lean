import Mathlib.Logic.Equiv.Bool
import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Relabel
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.ParameterEstimation
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Congruence
import QCryptLean.QKD.OutputLayout.Graft
import QCryptLean.QKD.OutputLayout.RegisterKeyed
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-!
# Complete outputs of the classical BB84 tail

The output equivalence reads the actual public test, seed, and decision cells and retains the
final registers. Canonical output data are the semantic public transcript paired with the
accepted keys or discarded payload. The executable tree and its layout are those of `classicalTail`.
-/

open Quantum.Operators (Op)

noncomputable section

namespace QKD.BB84
open LOCC LOCC.TwoParty FiniteKey Measurement

/-- Complete tail output coordinates used by the numerical analytical model. -/
abbrev RawClassicalTailOutput (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :=
  (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).space

/-- The direct final-stage heterogeneous output as the accepted-key-pair-or-abort payload. Both
directions use the literal Alice/Bob final multipartite systems. -/
def FinalStage.outputEquiv (ell : Nat) :
    (FinalStage.boundary ell).space ≃
      (Bits ell × Bits ell) ⊕ Unit where
  toFun q := by
    rcases q with ⟨⟨flag, leaf⟩, registers⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at leaf
      cases leaf
      exact Sum.inl (TwoParty.pairEquiv (Bits ell) (Bits ell) registers)
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at leaf
      cases leaf
      exact Sum.inr ()
  invFun q := by
    rcases q with keys | abort
    · exact ⟨⟨0, ()⟩,
        (TwoParty.pairEquiv (Bits ell) (Bits ell)).symm keys⟩
    · cases abort
      exact ⟨⟨1, ()⟩, fun p => by cases p <;> exact ()⟩
  left_inv q := by
    rcases q with ⟨⟨flag, leaf⟩, registers⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at leaf
      cases leaf
      change (⟨⟨0, ()⟩,
        (TwoParty.pairEquiv (Bits ell) (Bits ell)).symm
          (TwoParty.pairEquiv (Bits ell) (Bits ell) registers)⟩ :
            (FinalStage.boundary ell).space) = ⟨⟨0, ()⟩, registers⟩
      exact congrArg (fun q : (FinalStage.keySystem ell).total =>
        (⟨⟨0, ()⟩, q⟩ : (FinalStage.boundary ell).space))
        ((TwoParty.pairEquiv (Bits ell) (Bits ell)).symm_apply_apply registers)
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at leaf
      cases leaf
      change (⟨⟨1, ()⟩, (fun p => by cases p <;> exact ())⟩ :
        (FinalStage.boundary ell).space) = ⟨⟨1, ()⟩, registers⟩
      have hregisters : (fun p => by cases p <;> exact ()) = registers := by
        funext p
        cases p <;> exact Unit.ext _ _
      rw [hregisters]
  right_inv q := by
    rcases q with keys | abort
    · exact congrArg Sum.inl
        ((TwoParty.pairEquiv (Bits ell) (Bits ell)).apply_symm_apply keys)
    · cases abort
      rfl

/-- Read the final registers of the actual branch selected by Bob's public flag. -/
def flagBranchSpaceEquiv (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (seed : KeyHashSeed n ℓ peSel)
    (syndrome : Bits leakEC) (flag : Bool) :
    (if flag then
      (hashAlice (B := Bits n) seed).then
        ((correctAndHashBob ec seed syndrome).then (.done (KeyEnd.keys ℓ)))
    else (discardAlice (A := Bits n) (B := Bits n)).then
      (discardBob.then (.done KeyEnd.abort))).boundary.space ≃
        (FinalStage.flagBoundary ℓ ((Equiv.boolNot.trans finTwoEquiv.symm) flag)).space :=
  Equiv.cast (congrArg Boundary.space (by
    cases flag <;> rfl))

/-- Read Bob's decision cell followed by the registers of its actual terminal branch. -/
def decisionSpaceEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (seeds : KeyHashSeedPairEV n ℓ ℓEV peSel) (tag : Bits ℓEV)
    (syndrome : Bits leakEC) :
    ((announceAccept (A := Bits n) (xSel := xSel) ec δ Q
      (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
        if flag then
          (hashAlice seeds.1).then
            ((correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
        else discardAlice.then (discardBob.then (.done KeyEnd.abort))).boundary.space ≃
      (FinalStage.boundary ℓ).space :=
  (Boundary.publicSpaceEquiv _).trans <|
    (Equiv.sigmaCongr (Equiv.boolNot.trans finTwoEquiv.symm) fun flag =>
      flagBranchSpaceEquiv n ℓ peSel leakEC ec seeds.1 syndrome flag).trans
        (Boundary.publicSpaceEquiv (FinalStage.flagBoundary ℓ)).symm

/-- Decode the fused verification cell and the subsequent decision and terminal registers. -/
def seedDiscussionSpaceEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit) :
    ((announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).then fun cell =>
      let (seeds, tag, syndrome) := cell
      (announceAccept (xSel := xSel) ec δ Q
        (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then
              ((correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))).boundary.space ≃
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Bits ℓEV × Bits leakEC)) ×
        (FinalStage.boundary ℓ).space :=
  (Boundary.publicSpaceEquiv _).trans <|
    (Equiv.sigmaCongrRight (fun ⟨seeds, tag, syndrome⟩ =>
      decisionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests
        seeds tag syndrome)).trans
      (Equiv.sigmaEquivProd _ _)

/-- The actual classical tail is read as all public data and its surviving final registers. -/
def classicalTailSpaceEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC × (FinalStage.boundary ℓ).space :=
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
  ((announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k).trans
    (Equiv.sigmaCongrRight fun tests =>
      seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests)).trans
    { toFun := fun q => (⟨fun j => (q.1 j).1, fun j => (q.1 j).2,
        q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩, q.2.2)
      invFun := fun q => ⟨fun j => (q.1.alicePE j, q.1.bobPE j),
        (q.1.seedPair, q.1.evTag, q.1.syndrome), q.2⟩
      left_inv := by rintro ⟨tests, ⟨seeds, tag, syndrome⟩, q⟩; rfl
      right_inv := by rintro ⟨⟨as, bs, seeds, tag, syndrome⟩, q⟩; rfl }

/-- Read the actual tail in the complete output coordinates of the analytical model. -/
def rawClassicalTailOutputEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space ≃
      RawClassicalTailOutput n m ℓ ℓEV peSel leakEC :=
  (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q).trans <|
    (Equiv.sigmaEquivProd _ _).symm.trans <|
      (Equiv.sigmaCongr (classicalTailExitEquiv n m ℓ ℓEV peSel leakEC).symm
        (fun _ => Equiv.refl _)).trans
          (Boundary.graftSpaceEquiv _ (fun _ => FinalStage.boundary ℓ)).symm

/-- Transporting a literal accepted final-stage point through the raw-tail graft preserves its
ordered Alice and Bob key coordinates. -/
theorem rawTail_graft_acceptCoordinates_keys
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ)
    (g : (QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (q : ((QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).system g).total)
    (hpoint :
      (Boundary.graftSpaceEquiv
          (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
          (fun _ => FinalStage.boundary ℓ)).symm
          ⟨e, (FinalStage.outputEquiv ℓ).symm (Sum.inl keys)⟩ =
        ⟨g, q⟩)
    (haccept :
      (QKD.BB84.rawClassicalTailOutputLayout
          n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.disposition g =
        .accept ℓ) :
    let L := (QKD.BB84.rawClassicalTailOutputLayout
      n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout
    ((L.acceptCoordinates haccept q).1,
      (L.acceptCoordinates haccept q).2.1) = keys := by
  let B := QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC
  let C : B.Exit → Boundary TwoParty.Party := fun _ => FinalStage.boundary ℓ
  let G := Boundary.graftSpaceEquiv B C
  let z := Boundary.graftExitEquiv B C g
  let hSystem := Boundary.system_graftExitEquiv B C g
  let qc := Equiv.cast (congrArg (fun R : MultipartiteSystem TwoParty.Party =>
    R.total) hSystem) q
  let L := (QKD.BB84.rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout
  have hforward : G ⟨g, q⟩ = ⟨e, (FinalStage.outputEquiv ℓ).symm (Sum.inl keys)⟩ := by
    rw [← hpoint]
    exact G.apply_symm_apply _
  rw [Boundary.graftSpaceEquiv_apply] at hforward
  have hchild : (⟨z.2, qc⟩ : (FinalStage.boundary ℓ).space) =
      (FinalStage.outputEquiv ℓ).symm (Sum.inl keys) :=
    congrArg (fun w : Σ _ : B.Exit, (FinalStage.boundary ℓ).space => w.2) hforward
  have castSplit_apply {R S : MultipartiteSystem TwoParty.Party} (h : R = S)
      (p : TwoParty.Party) {K A : Type} (E : S.reg p ≃ K × A) (r : R.total) :
      (cast (congrArg (fun D : MultipartiteSystem TwoParty.Party => D.reg p ≃ K × A) h.symm) E)
          (r p) =
        E ((Equiv.cast (congrArg (fun D : MultipartiteSystem TwoParty.Party =>
          D.total) h) r) p)
          := by
    cases h
    rfl
  have graftKeys (D : Boundary TwoParty.Party)
      (v : (D.graft (fun _ => FinalStage.boundary ℓ)).Exit)
      (r : ((D.graft (fun _ => FinalStage.boundary ℓ)).system v).total) :
      let LD := QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
        (fun _ : D.Exit => FinalStage.outputLayout ℓ) (fun _ => rfl) (fun _ => rfl)
      let w := Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v
      let rc := Equiv.cast (congrArg (fun R : MultipartiteSystem TwoParty.Party =>
        R.total)
        (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)) r
      (LD.coordinates v r).1 = ((FinalStage.outputLayout ℓ).coordinates w.2 rc).1 ∧
        (LD.coordinates v r).2.1 = ((FinalStage.outputLayout ℓ).coordinates w.2 rc).2.1 := by
    constructor
    · exact congrArg Prod.fst
        (castSplit_apply (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)
          .alice ((FinalStage.outputLayout ℓ).aliceSplit
            (Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v).2) r)
    · exact congrArg Prod.fst
        (castSplit_apply (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)
          .bob ((FinalStage.outputLayout ℓ).bobSplit
            (Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v).2) r)
  have hAlice : (L.coordinates g q).1 =
      ((FinalStage.outputLayout ℓ).coordinates z.2 qc).1 := by
    exact (graftKeys B g q).1
  have hBob : (L.coordinates g q).2.1 =
      ((FinalStage.outputLayout ℓ).coordinates z.2 qc).2.1 := by
    exact (graftKeys B g q).2
  have hAliceKeys : ((FinalStage.outputLayout ℓ).coordinates z.2 qc).1 ≍ keys.1 := by
    have h := congr_arg_heq
      (fun w : (FinalStage.boundary ℓ).space =>
        ((FinalStage.outputLayout ℓ).coordinates w.1 w.2).1) hchild
    exact h
  have hBobKeys : ((FinalStage.outputLayout ℓ).coordinates z.2 qc).2.1 ≍ keys.2 := by
    have h := congr_arg_heq
      (fun w : (FinalStage.boundary ℓ).space =>
        ((FinalStage.outputLayout ℓ).coordinates w.1 w.2).2.1) hchild
    exact h
  apply Prod.ext
  · exact eq_of_heq
      ((L.acceptCoordinates_fst_heq_coordinates_fst haccept q).trans
        ((heq_of_eq hAlice).trans hAliceKeys))
  · exact eq_of_heq
      ((L.acceptCoordinates_snd_fst_heq_coordinates_snd_fst haccept q).trans
        ((heq_of_eq hBob).trans hBobKeys))

/-- The analytical tail keeps only the two local keys or the discarded registers. -/
theorem rawClassicalTailOutputLayout_registerKeyed
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).RegisterKeyed := by
  have hfinal : (FinalStage.outputLayout ℓ).RegisterKeyed := by
    refine ⟨OutputLayout.residual_subsingleton _ rfl rfl ?_ ?_, ?_, ?_⟩
    · rintro ⟨flag, leaf⟩
      fin_cases flag <;> exact inferInstanceAs (Subsingleton Unit)
    · rintro ⟨flag, leaf⟩
      fin_cases flag <;> exact inferInstanceAs (Subsingleton Unit)
    · rintro ⟨flag, leaf⟩ q
      fin_cases flag <;> rfl
    · rintro ⟨flag, leaf⟩ q
      fin_cases flag <;> rfl
  exact OutputLayout.registerKeyed_graftFixedParties _ _ _ .alice .bob (by decide)
    (fun _ => rfl) (fun _ => rfl) (fun _ => hfinal)

/-- The actual tail's terminal values retain no non-key register. -/
theorem classicalTail_outputLayout_registerKeyed
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    ((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).outputLayout
      (by decide)).RegisterKeyed := by
  have hTests (r : ℕ) (idx : Fin r → Fin n)
      (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n))
        (KeyEnd Party.alice Party.bob))
      (hk : ∀ tests, ((k tests).outputLayout (by decide)).RegisterKeyed) :
      ((announceTests r idx k).outputLayout (by decide)).RegisterKeyed := by
    induction r with
    | zero => exact hk Fin.elim0
    | succ r ih =>
      have h b a := ih (Fin.tail idx) (fun rest => k (Fin.cons (a, b) rest))
        (fun rest => hk (Fin.cons (a, b) rest))
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨b, a, e⟩
        exact (h b a).residual e
      · rintro ⟨b, a, e⟩ q
        exact (h b a).aliceKey e q
      · rintro ⟨b, a, e⟩ q
        exact (h b a).bobKey e q
  unfold classicalTail
  apply hTests
  intro tests
  refine ⟨OutputLayout.residual_subsingleton _ rfl rfl ?_ ?_, ?_, ?_⟩
  · rintro ⟨cell, flag, e⟩
    cases flag <;> exact inferInstanceAs (Subsingleton Unit)
  · rintro ⟨cell, flag, e⟩
    cases flag <;> exact inferInstanceAs (Subsingleton Unit)
  · rintro ⟨cell, flag, e⟩ q
    cases flag <;> rfl
  · rintro ⟨cell, flag, e⟩ q
    cases flag <;> rfl

/-- Reading the classical tail's final flag reads its declared terminal disposition. -/
theorem classicalTailSpaceEquiv_disposition
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    ((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).terminal q.1).disposition =
      FinalStage.disposition ℓ
        (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q).2.1.1 := by
  have hTests (r : ℕ) (idx : Fin r → Fin n)
      (k : (Fin r → Bit × Bit) → Program (system (Bits n) (Bits n))
        (KeyEnd Party.alice Party.bob))
      (q : (announceTests r idx k).boundary.space) :
      ((announceTests r idx k).terminal q.1).disposition =
        ((k (announceTestsSpaceEquiv r idx k q).1).terminal
          (announceTestsSpaceEquiv r idx k q).2.1).disposition := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rcases q with ⟨⟨b, a, e⟩, q⟩
        exact ih (Fin.tail idx) _ ⟨e, q⟩
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
  have hK (tests) (q : (k tests).boundary.space) :
      ((k tests).terminal q.1).disposition = FinalStage.disposition ℓ
        (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q).2.1.1 := by
    rcases q with ⟨⟨cell, flag, leaf⟩, registers⟩
    cases flag <;> rfl
  exact (hTests (min n m) (peRoundIdx peSel) k q).trans
    (hK (announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q).1
      (announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q).2)

/-- Read the terminal exit selected by Bob's public flag. -/
private def flagBranchExitEquiv (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (seed : KeyHashSeed n ℓ peSel)
    (syndrome : Bits leakEC) (flag : Bool) :
    (if flag then
      (hashAlice (B := Bits n) seed).then
        ((correctAndHashBob ec seed syndrome).then (.done (KeyEnd.keys ℓ)))
    else (discardAlice (A := Bits n) (B := Bits n)).then
      (discardBob.then (.done KeyEnd.abort))).boundary.Exit ≃
        (FinalStage.flagBoundary ℓ ((Equiv.boolNot.trans finTwoEquiv.symm) flag)).Exit :=
  Equiv.cast (congrArg Boundary.Exit (by
    cases flag <;> rfl))

/-- Decode a seed cell and the decision exit it selects. -/
private def seedDiscussionExitEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit) :
    ((announceSeedTagSyndrome ℓ ℓEV ec).then fun cell =>
        let (seeds, tag, syndrome) := cell
        (announceAccept (xSel := xSel) ec δ Q
          (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then <|
              (correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))).boundary.Exit ≃
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Bits ℓEV × Bits leakEC)) ×
        (FinalStage.boundary ℓ).Exit :=
  (Equiv.sigmaCongrRight fun ⟨seeds, _tag, syndrome⟩ =>
      Equiv.sigmaCongr (Equiv.boolNot.trans finTwoEquiv.symm) fun flag =>
        flagBranchExitEquiv n ℓ peSel leakEC ec seeds.1 syndrome flag).trans
          (Equiv.sigmaEquivProd _ _)

/-- Reading a seed discussion output reads the same exit as its public-cell decoder. -/
private theorem seedDiscussionSpaceEquiv_exit
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (q : ((announceSeedTagSyndrome ℓ ℓEV ec).then fun cell =>
        let (seeds, tag, syndrome) := cell
        (announceAccept (xSel := xSel) ec δ Q
          (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then <|
              (correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))).boundary.space) :
    ((seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q).1,
      (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q).2.1) =
        seedDiscussionExitEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q.1 := by
  rcases q with ⟨⟨cell, flag, leaf⟩, registers⟩
  cases flag <;> rfl
/-- Decode the actual public cells into their semantic data and final decision exit. -/
def classicalTailExitDataEquiv (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.Exit ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC × (FinalStage.boundary ℓ).Exit :=
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
  let decode := seedDiscussionExitEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q
  ((announceTestsExitEquiv (min n m) (peRoundIdx peSel) k).trans
    (Equiv.sigmaCongrRight decode)).trans
    { toFun := fun q => (⟨fun j => (q.1 j).1, fun j => (q.1 j).2,
        q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩, q.2.2)
      invFun := fun q => ⟨fun j => (q.1.alicePE j, q.1.bobPE j),
        (q.1.seedPair, q.1.evTag, q.1.syndrome), q.2⟩
      left_inv := by rintro ⟨tests, ⟨seeds, tag, syndrome⟩, e⟩; rfl
      right_inv := by rintro ⟨⟨as, bs, seeds, tag, syndrome⟩, e⟩; rfl }
/-- The semantic output decoder reads the same complete exit as the exit decoder. -/
theorem classicalTailSpaceEquiv_exit
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    ((classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q).1,
      (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q).2.1) =
        classicalTailExitDataEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q.1 := by
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
  let decode := seedDiscussionExitEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q
  let assemble (tests : Fin (min n m) → Bit × Bit)
      (z : (KeyHashSeedPairEV n ℓ ℓEV peSel × (Bits ℓEV × Bits leakEC)) ×
        (FinalStage.boundary ℓ).Exit) :=
    ((⟨fun j => (tests j).1, fun j => (tests j).2,
      z.1.1, z.1.2.1, z.1.2.2⟩ : ClassicalTailData n m ℓ ℓEV peSel leakEC), z.2)
  let z := announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q
  refine (congrArg (assemble z.1)
    (seedDiscussionSpaceEquiv_exit n m ℓ ℓEV peSel xSel leakEC ec δ Q z.1 z.2)).trans ?_
  exact congrArg (fun e : Σ tests, (k tests).boundary.Exit =>
    assemble e.1 (decode e.1 e.2))
      (announceTestsSpaceEquiv_exit (min n m) (peRoundIdx peSel) k q)

/-- The two final public cells preserve the terminal joint register in semantic coordinates. -/
private theorem seedDiscussionSpaceEquiv_snd_heq
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (tests : Fin (min n m) → Bit × Bit)
    (q : ((announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).then fun cell =>
      let (seeds, tag, syndrome) := cell
      (announceAccept (xSel := xSel) ec δ Q
        (fun j => (tests j).1) (fun j => (tests j).2) seeds.2 tag syndrome).then fun flag =>
          if flag then
            (hashAlice seeds.1).then
              ((correctAndHashBob ec seeds.1 syndrome).then (.done (KeyEnd.keys ℓ)))
          else discardAlice.then (discardBob.then (.done KeyEnd.abort))).boundary.space) :
    HEq (seedDiscussionSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q tests q).2.2 q.2 := by
  rcases q with ⟨⟨cell, flag, leaf⟩, registers⟩
  cases flag <;> rfl

/-- The semantic output decoder leaves the final joint register unchanged. -/
theorem classicalTailSpaceEquiv_snd_heq
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    HEq (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q).2.2 q.2 := by
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
  exact (seedDiscussionSpaceEquiv_snd_heq n m ℓ ℓEV peSel xSel leakEC ec δ Q
    (announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q).1
    (announceTestsSpaceEquiv (min n m) (peRoundIdx peSel) k q).2).trans
      (announceTestsSpaceEquiv_snd_heq (min n m) (peRoundIdx peSel) k q)

/-- The semantic exit decoder preserves the final multipartite system. -/
theorem system_classicalTailExitDataEquiv
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (e : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.Exit) :
    (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.system e =
      (FinalStage.boundary ℓ).system
        (classicalTailExitDataEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q e).2 := by
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
  let decode := seedDiscussionExitEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q
  have hK (tests) (e : (k tests).boundary.Exit) :
      (k tests).boundary.system e = (FinalStage.boundary ℓ).system (decode tests e).2 := by
    rcases e with ⟨cell, flag, leaf⟩
    cases flag <;> rfl
  exact (system_announceTestsExitEquiv (min n m) (peRoundIdx peSel) k e).trans
    (hK (announceTestsExitEquiv (min n m) (peRoundIdx peSel) k e).1
      (announceTestsExitEquiv (min n m) (peRoundIdx peSel) k e).2)


/-- The analytical output coordinates preserve the disposition read from the tail's terminal. -/
theorem rawClassicalTailOutputEquiv_disposition
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (q : (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).disposition
      (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q).1 =
        ((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).terminal q.1).disposition := by
  refine Eq.trans ?_ (classicalTailSpaceEquiv_disposition
    n m ℓ ℓEV peSel xSel leakEC ec δ Q q).symm
  let z := classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q q
  refine (congrArg (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).disposition
    (Boundary.graftSpaceEquiv_symm_fst
      (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC) (fun _ => FinalStage.boundary ℓ)
      ((classicalTailExitEquiv n m ℓ ℓEV peSel leakEC).symm z.1) z.2)).trans ?_
  exact OutputLayout.graftFixedParties_disposition
    (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC) (fun _ => FinalStage.boundary ℓ)
    (fun _ => FinalStage.outputLayout ℓ) .alice .bob (by decide)
    (fun _ => rfl) (fun _ => rfl) _ _
/-- Fibre decoders assemble into a register-preserving relabelling of a grafted boundary. -/
private def exitRenaming_graft {B H C : Boundary Party} {D : Type}
    (out : B.space ≃ D × C.space) (exits : B.Exit ≃ D × C.Exit) (data : H.Exit ≃ D)
    (hsystem : ∀ e, C.system (exits e).2 = B.system e)
    (hexit : ∀ q : B.space, ((out q).1, (out q).2.1) = exits q.1)
    (hregister : ∀ q : B.space, HEq (out q).2.2 q.2) :
    Boundary.ExitRenaming (out.trans ((Equiv.sigmaEquivProd _ _).symm.trans
      ((Equiv.sigmaCongr data.symm (fun _ => Equiv.refl _)).trans
        (Boundary.graftSpaceEquiv H (fun _ => C)).symm))) where
  exits e := (Boundary.graftExitEquiv H (fun _ => C)).symm
    ⟨data.symm (exits e).1, (exits e).2⟩
  exits_inj := by
    intro e f h
    apply exits.injective
    have hh := (Boundary.graftExitEquiv H (fun _ => C)).symm.injective h
    apply Prod.ext
    · exact data.symm.injective (congrArg Sigma.fst hh)
    · exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  systems e := (Boundary.system_graftExitEquiv_symm H (fun _ => C) _).trans (hsystem e)
  fst q := (Boundary.graftSpaceEquiv_symm_fst H (fun _ => C)
    (data.symm (out q).1) (out q).2).trans
      (congrArg (fun z : D × C.Exit =>
        (Boundary.graftExitEquiv H (fun _ => C)).symm ⟨data.symm z.1, z.2⟩) (hexit q))
  snd q := (Boundary.graftSpaceEquiv_symm_snd_heq H (fun _ => C)
    (data.symm (out q).1) (out q).2).trans (hregister q)

/-- The analytical tail coordinates rename complete exits and preserve each terminal register. -/
def rawClassicalTailExitRenaming
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Boundary.ExitRenaming (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q) :=
  exitRenaming_graft
    (classicalTailSpaceEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)
    (classicalTailExitDataEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)
    (classicalTailExitEquiv n m ℓ ℓEV peSel leakEC)
    (fun e => (system_classicalTailExitDataEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q e).symm)
    (classicalTailSpaceEquiv_exit n m ℓ ℓEV peSel xSel leakEC ec δ Q)
    (classicalTailSpaceEquiv_snd_heq n m ℓ ℓEV peSel xSel leakEC ec δ Q)

/-- The terminal-derived key resource is the analytical tail resource in its output coordinates. -/
theorem rawClassicalTailOutputEquiv_resource
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (rho : Op (classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).boundary.space) :
    (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.ideal
      ((Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ
        Q) (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)).toLinearMap rho) =
    (Matrix.reindexLinearEquiv ℂ ℂ (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (rawClassicalTailOutputEquiv n m ℓ ℓEV peSel xSel leakEC ec δ Q)).toLinearMap
      (((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).outputLayout
        (by decide)).toBoundaryKeyLayout.ideal rho) :=
  BoundaryKeyLayout.ideal_reindexOp_of_exitRenaming
    (L₁ := ((classicalTail n m ℓ ℓEV peSel xSel leakEC ec δ Q).outputLayout
      (by decide)).toBoundaryKeyLayout)
    (L₂ := (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout)
    (OutputLayout.RegisterKeyed.toBoundaryKeyLayout _
      (classicalTail_outputLayout_registerKeyed n m ℓ ℓEV peSel xSel leakEC ec δ Q))
    (OutputLayout.RegisterKeyed.toBoundaryKeyLayout _
      (rawClassicalTailOutputLayout_registerKeyed n m ℓ ℓEV peSel leakEC))
    (rawClassicalTailExitRenaming n m ℓ ℓEV peSel xSel leakEC ec δ Q) rho
end QKD.BB84
