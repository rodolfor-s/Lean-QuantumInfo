import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Discard
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.TwoParty
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Quantum.Operators.Basic

/-! # Classical -/


open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

namespace PrivateAction

/-- Entrywise operation of a local `functionAndForget` action on a joint register.

For output rows `q` and `q'`, the acting-party coordinates must both equal `f a` for the same
forgotten input value `a`. The spectator coordinates of `q` and `q'` remain separate in the two
input indices of `rho`; in particular, this theorem does not discard spectator coherence. This
is the exact local tensor-with-identity operation of the finite-round LOCC instrument tree in
Chitambar et al., arXiv:1210.4583, Section II, specialized to the deterministic classical
postprocessing used in Nahar et al., arXiv:2403.11851, lines 914--919. -/
theorem liftedOperation_ofInstrument_functionAndForget_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} (i : P) {HH : Type}
    [Fintype HH] [DecidableEq HH]
    (f : R.reg i → HH) (rho : Quantum.Operators.Op R.total) (q q' : (R.set i HH).total) :
    ((PrivateAction.ofInstrument i
        (Instrument.functionAndForget f)).liftedOperation () rho) q q' =
      ∑ a : R.reg i,
        if ((R.splitAtSet i HH) q).1 = f a ∧
            ((R.splitAtSet i HH) q').1 = f a then
          rho
            ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2))
            ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q').2))
        else 0 := by
  classical
  let rhoqq : Quantum.Operators.Op (R.reg i) :=
    rho.submatrix
      (fun x => (R.splitAt i).symm
        (x, ((R.splitAtSet i HH) q).2))
      (fun y => (R.splitAt i).symm
        (y, ((R.splitAtSet i HH) q').2))
  have hlift
      (L : Instrument (R.reg i) (HH) Unit) :
      ((PrivateAction.ofInstrument i L).liftedOperation () rho) q q' =
        (L.operation () rhoqq)
          ((R.splitAtSet i HH) q).1
          ((R.splitAtSet i HH) q').1 := by
    exact Instrument.liftAt_operation_apply (R := R) i L () rho q q'
  rw [hlift (Instrument.functionAndForget f)]
  simp only [Instrument.functionAndForget_operation_apply, rhoqq,
    Matrix.submatrix_apply]

end PrivateAction

namespace TwoParty

variable {A B C D O : Type}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C]
variable [Fintype D] [DecidableEq D]
variable [Fintype O]

/-- Alice's successor operation preserves both independent Bob coordinates. -/
theorem _root_.LOCC.PrivateAction.successorOperation_alice_apply (I : Instrument A C O) (o : O)
    (rho : Op (system A B).total) (a a' : C) (b b' : B) :
    (PrivateAction.ofInstrument (R := system A B) .alice I).successorOperation o rho
        ((pairEquiv C B).symm (a, b)) ((pairEquiv C B).symm (a', b')) =
      I.operation o (rho.submatrix (fun x => (pairEquiv A B).symm (x, b))
        (fun x => (pairEquiv A B).symm (x, b'))) a a' := by
  change (I.liftAt (system A B) .alice).operation o rho
    (cast (congrArg MultipartiteSystem.total (set_alice A B C).symm)
      ((system C B).pairEquiv.symm (a, b)))
    (cast (congrArg MultipartiteSystem.total (set_alice A B C).symm)
      ((system C B).pairEquiv.symm (a', b'))) = _
  rw [MultipartiteSystem.cast_pairEquiv_symm
      (set_alice A B C).symm,
    MultipartiteSystem.cast_pairEquiv_symm
      (set_alice A B C).symm]
  exact Instrument.liftAt_alice_operation_apply (system A B) I o rho a a' b b'

/-- Bob's successor operation preserves both independent Alice coordinates. -/
theorem _root_.LOCC.PrivateAction.successorOperation_bob_apply (I : Instrument B D O) (o : O)
    (rho : Op (system A B).total) (a a' : A) (b b' : D) :
    (PrivateAction.ofInstrument (R := system A B) .bob I).successorOperation o rho
        ((pairEquiv A D).symm (a, b)) ((pairEquiv A D).symm (a', b')) =
      I.operation o (rho.submatrix (fun x => (pairEquiv A B).symm (a, x))
        (fun x => (pairEquiv A B).symm (a', x))) b b' := by
  change (I.liftAt (system A B) .bob).operation o rho
    (cast (congrArg MultipartiteSystem.total (set_bob A B D).symm)
      ((system A D).pairEquiv.symm (a, b)))
    (cast (congrArg MultipartiteSystem.total (set_bob A B D).symm)
      ((system A D).pairEquiv.symm (a', b'))) = _
  rw [MultipartiteSystem.cast_pairEquiv_symm
      (set_bob A B D).symm,
    MultipartiteSystem.cast_pairEquiv_symm
      (set_bob A B D).symm]
  exact Instrument.liftAt_bob_operation_apply (system A B) I o rho a a' b b'

/-- Alice's announced successor operation applies the instrument on her coordinate. -/
theorem _root_.LOCC.AnnouncedAction.successorOperation_alice_apply
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (I : Instrument A C O) (announce : O → Y) (o : O)
    (rho : Op (system A B).total) (a a' : C) (b b' : B) :
    (AnnouncedAction.ofInstrument (R := system A B) .alice I announce).successorOperation o rho
        ((pairEquiv C B).symm (a, b)) ((pairEquiv C B).symm (a', b')) =
      I.operation o (rho.submatrix (fun x => (pairEquiv A B).symm (x, b))
        (fun x => (pairEquiv A B).symm (x, b'))) a a' :=
  PrivateAction.successorOperation_alice_apply I o rho a a' b b'

/-- Bob's announced successor operation applies the instrument on his coordinate. -/
theorem _root_.LOCC.AnnouncedAction.successorOperation_bob_apply
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (I : Instrument B D O) (announce : O → Y) (o : O)
    (rho : Op (system A B).total) (a a' : A) (b b' : D) :
    (AnnouncedAction.ofInstrument (R := system A B) .bob I announce).successorOperation o rho
        ((pairEquiv A D).symm (a, b)) ((pairEquiv A D).symm (a', b')) =
      I.operation o (rho.submatrix (fun x => (pairEquiv A B).symm (a, x))
        (fun x => (pairEquiv A B).symm (a', x))) b b' :=
  PrivateAction.successorOperation_bob_apply I o rho a a' b b'

/-- Local function-and-forget operations read precisely the joint input diagonal. -/
theorem functionAndForget_pair_operation_apply (f : A → C) (g : B → D)
    (rho : Op (system A B).total) (c c' : C) (d d' : D) :
    (PrivateAction.ofInstrument (R := system C B) .bob
      (Instrument.functionAndForget g)).successorOperation ()
        ((PrivateAction.ofInstrument (R := system A B) .alice
          (Instrument.functionAndForget f)).successorOperation () rho)
          ((pairEquiv C D).symm (c, d)) ((pairEquiv C D).symm (c', d')) =
      ∑ b : B, if d = g b ∧ d' = g b then
        ∑ a : A, if c = f a ∧ c' = f a then
          rho ((pairEquiv A B).symm (a, b)) ((pairEquiv A B).symm (a, b))
        else 0
      else 0 := by
  rw [PrivateAction.successorOperation_bob_apply,
    Instrument.functionAndForget_operation_apply]
  apply Finset.sum_congr rfl
  intro b _
  split
  · change (PrivateAction.ofInstrument (R := system A B) .alice
          (Instrument.functionAndForget f)).successorOperation () rho
      ((pairEquiv C B).symm (c, b)) ((pairEquiv C B).symm (c', b)) = _
    rw [PrivateAction.successorOperation_alice_apply, Instrument.functionAndForget_operation_apply]
    rfl
  · rfl

/-- Two one-outcome private actions feed their normalized operations to the continuation. -/
theorem private_pair_denote_apply {End : MultipartiteSystem Party → Type 1}
    (I : Instrument A C Unit) (J : Instrument B D Unit) (k : Program (system C D) End)
    (rho : Op (system A B).total) (q q' : k.boundary.space) :
    ((PrivateAction.ofInstrument (R := system A B) .alice I).then <|
      (PrivateAction.ofInstrument (R := system C B) .bob J).then k).denote rho q q' =
      k.denote ((PrivateAction.ofInstrument (R := system C B) .bob J).successorOperation ()
        ((PrivateAction.ofInstrument (R := system A B) .alice I).successorOperation () rho))
          q q' := by
  dsimp +instances only [PrivateAction.ofInstrument]
  rw [Program.denote_priv_eq_sum_liftedOperation]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]
  rw [Program.denote_priv_eq_sum_liftedOperation]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]

/-- Terminating after both local functions gives their exact joint diagonal kernel. -/
theorem functionAndForget_pair_denote_apply {End : MultipartiteSystem Party → Type 1}
    (f : A → C) (g : B → D) (terminal : End (system C D))
    (rho : Op (system A B).total) (c c' : C) (d d' : D) :
    ((PrivateAction.ofInstrument (R := system A B) .alice (Instrument.functionAndForget f)).then <|
      (PrivateAction.ofInstrument (R := system C B) .bob (Instrument.functionAndForget g)).then
        (Program.done terminal)).denote rho
          ⟨(), (pairEquiv C D).symm (c, d)⟩ ⟨(), (pairEquiv C D).symm (c', d')⟩ =
      ∑ b : B, if d = g b ∧ d' = g b then
        ∑ a : A, if c = f a ∧ c' = f a then
          rho ((pairEquiv A B).symm (a, b)) ((pairEquiv A B).symm (a, b))
        else 0
      else 0 :=
  (private_pair_denote_apply (Instrument.functionAndForget f)
    (Instrument.functionAndForget g) (.done terminal) rho
      ⟨(), (pairEquiv C D).symm (c, d)⟩ ⟨(), (pairEquiv C D).symm (c', d')⟩).trans
      (functionAndForget_pair_operation_apply f g rho c c' d d')

/-- Retaining two computed classical values makes every distinct output pair vanish. -/
theorem functionAndForget_pair_denote_offDiagonal_zero
    {End : MultipartiteSystem Party → Type 1}
    (f : A → C) (g : B → D) (terminal : End (system C D))
    (rho : Op (system A B).total) (x y : (Boundary.leaf (system C D)).space)
    (hxy : x ≠ y) :
    ((PrivateAction.ofInstrument (R := system A B) .alice (Instrument.functionAndForget f)).then <|
      (PrivateAction.ofInstrument (R := system C B) .bob (Instrument.functionAndForget g)).then
        (Program.done terminal)).denote rho x y = 0 := by
  rcases x with ⟨⟨⟩, x⟩
  rcases y with ⟨⟨⟩, y⟩
  obtain ⟨⟨c, d⟩, rfl⟩ := (pairEquiv C D).symm.surjective x
  obtain ⟨⟨c', d'⟩, rfl⟩ := (pairEquiv C D).symm.surjective y
  refine (functionAndForget_pair_denote_apply f g terminal rho c c' d d').trans ?_
  apply Finset.sum_eq_zero
  intro b _
  split
  · rename_i hb
    apply Finset.sum_eq_zero
    intro a _
    split
    · rename_i ha
      exact False.elim (hxy (by rw [ha.1.trans ha.2.symm, hb.1.trans hb.2.symm]))
    · rfl
  · rfl

/-- Discarding both local registers returns the joint trace of any input operator. -/
theorem discard_pair_operation_apply (rho : Op (system A B).total) :
    (PrivateAction.ofInstrument (R := system Unit B) .bob
      (Instrument.discardToUnit B)).successorOperation ()
        ((PrivateAction.ofInstrument (R := system A B) .alice
          (Instrument.discardToUnit A)).successorOperation () rho)
          ((pairEquiv Unit Unit).symm ((), ())) ((pairEquiv Unit Unit).symm ((), ())) =
      ∑ b : B, ∑ a : A,
        rho ((pairEquiv A B).symm (a, b)) ((pairEquiv A B).symm (a, b)) := by
  rw [PrivateAction.successorOperation_bob_apply,
    Instrument.discardToUnit_operation_apply]
  apply Finset.sum_congr rfl
  intro b _
  change (PrivateAction.ofInstrument (R := system A B) .alice
          (Instrument.discardToUnit A)).successorOperation () rho
    ((pairEquiv Unit B).symm ((), b)) ((pairEquiv Unit B).symm ((), b)) = _
  rw [PrivateAction.successorOperation_alice_apply, Instrument.discardToUnit_operation_apply]
  rfl

/-- The declared discarded terminal contains exactly the joint trace. -/
theorem discard_pair_denote_apply {End : MultipartiteSystem Party → Type 1}
    (terminal : End (system Unit Unit)) (rho : Op (system A B).total) :
    ((PrivateAction.ofInstrument (R := system A B) .alice (Instrument.discardToUnit A)).then <|
      (PrivateAction.ofInstrument (R := system Unit B) .bob (Instrument.discardToUnit B)).then
        (Program.done terminal)).denote rho
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩
          ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩ =
      ∑ b : B, ∑ a : A,
        rho ((pairEquiv A B).symm (a, b)) ((pairEquiv A B).symm (a, b)) :=
  (private_pair_denote_apply (Instrument.discardToUnit A) (Instrument.discardToUnit B)
    (.done terminal) rho ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩
      ⟨(), (pairEquiv Unit Unit).symm ((), ())⟩).trans (discard_pair_operation_apply rho)

/-- Local function-and-forget actions substitute their values into a continuation's kernel. -/
theorem functionAndForget_pair_denote_kernel
    {End : MultipartiteSystem Party → Type 1}
    (f : A → C) (g : B → D) (k : Program (system C D) End)
    (q q' : k.boundary.space) (K : C → D → ℂ)
    (hK : ∀ tau, k.denote tau q q' =
      ∑ d, ∑ c, K c d * tau ((pairEquiv C D).symm (c, d))
        ((pairEquiv C D).symm (c, d))) (rho : Op (system A B).total) :
    ((PrivateAction.ofInstrument (R := system A B) .alice (Instrument.functionAndForget f)).then <|
      (PrivateAction.ofInstrument (R := system C B) .bob
        (Instrument.functionAndForget g)).then k).denote
        rho q q' =
      ∑ b, ∑ a, K (f a) (g b) * rho ((pairEquiv A B).symm (a, b))
        ((pairEquiv A B).symm (a, b)) := by
  refine (private_pair_denote_apply (Instrument.functionAndForget f)
    (Instrument.functionAndForget g) k rho q q').trans ?_
  refine (hK _).trans ?_
  refine (Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ =>
    congrArg (fun z : ℂ => K c d * z)
      (functionAndForget_pair_operation_apply f g rho c c d d)))).trans ?_
  simp only [and_self, Finset.mul_sum, mul_ite, mul_zero]
  let v := fun a b => rho ((pairEquiv A B).symm (a, b)) ((pairEquiv A B).symm (a, b))
  have hc (d : D) (b : B) :
      (∑ c, if d = g b then ∑ a, if c = f a then K c d * v a b else 0 else 0) =
        if d = g b then ∑ a, K (f a) d * v a b else 0 := by
    by_cases h : d = g b
    · simp only [ite_eq_left h]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · simp only [ite_eq_right h, Finset.sum_const_zero]
  calc
    _ = ∑ d, ∑ b, ∑ c,
        if d = g b then ∑ a, if c = f a then K c d * v a b else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c,
        if d = g b then ∑ a, if c = f a then K c d * v a b else 0 else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true, v]

end TwoParty

end LOCC
