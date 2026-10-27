import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-!
# Complete-path denotation of branch-dependent LOCC programs

This module flattens every finite `Program` into one certified instrument. A hidden branch records
raw outcomes, Kraus multiplicities, and the remaining hidden branch, while `Branch.exit` records
only the public exit. Its path Kraus matrix is injected into the corresponding exit block of the
heterogeneous output space.
-/

open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators Kronecker
open Matrix

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]
variable {Y : Type} [Fintype Y] [DecidableEq Y]

namespace Boundary

/-- Operators on a boundary are block diagonal when distinct complete exits have no cross terms. -/
def IsExitBlockDiagonal (B : Boundary P) (ρ : Op B.space) : Prop :=
  ∀ (e f : B.Exit) (a : (B.system e).total) (b : (B.system f).total),
    e ≠ f → ρ ⟨e, a⟩ ⟨f, b⟩ = 0

end Boundary

variable [SystemPresentation P]

/-- A local Kraus matrix in the continuation's successor coordinates. -/
noncomputable def PrivateAction.successorKraus {R : MultipartiteSystem P}
    (a : PrivateAction R) (o : a.Outcome) (r : a.instrument.krausIndex o) :
    Matrix (SystemPresentation.update R a.actor a.Output).total R.total ℂ :=
  (a.liftedKraus o r).submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total
      (SystemPresentation.update_eq_set R a.actor a.Output))) id

/-- Successor coordinates preserve completeness of a private action's Kraus family. -/
theorem PrivateAction.successorKraus_complete {R : MultipartiteSystem P} (a : PrivateAction R) :
    ∑ o, ∑ r, (a.successorKraus o r)ᴴ * a.successorKraus o r = 1 := by
  simp only [successorKraus, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact a.liftedKraus_complete

/-- An announced Kraus matrix in its public continuation's successor coordinates. -/
noncomputable def AnnouncedAction.successorKraus {R : MultipartiteSystem P}
    (a : AnnouncedAction R Y)
    (o : a.Outcome) (r : a.krausIndex o) :
    Matrix (SystemPresentation.update R a.actor (a.Output (a.announce o))).total R.total ℂ :=
  (a.liftedKraus o r).submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total
      (SystemPresentation.update_eq_set R a.actor (a.Output (a.announce o))))) id

/-- Successor coordinates preserve completeness of an announced action's Kraus family. -/
theorem AnnouncedAction.successorKraus_complete {R : MultipartiteSystem P}
    (a : AnnouncedAction R Y) :
    ∑ o, ∑ r, (a.successorKraus o r)ᴴ * a.successorKraus o r = 1 := by
  simp only [successorKraus, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact a.liftedKraus_complete

/-- The raw private-outcome operation in the continuation's successor coordinates. -/
noncomputable abbrev PrivateAction.successorOperation {R : MultipartiteSystem P}
    (a : PrivateAction R) (o : a.Outcome) :
    Op R.total →ₗ[ℂ] Op (SystemPresentation.update R a.actor a.Output).total :=
  ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg MultipartiteSystem.total
    (SystemPresentation.update_eq_set R a.actor a.Output))).symm (Equiv.cast (congrArg
      MultipartiteSystem.total
    (SystemPresentation.update_eq_set R a.actor a.Output))).symm).toLinearMap).comp
    (a.liftedOperation o)

/-- The raw announcement operation in its public branch's successor coordinates. -/
noncomputable abbrev AnnouncedAction.successorOperation {R : MultipartiteSystem P}
    (a : AnnouncedAction R Y) (o : a.Outcome) :
    Op R.total →ₗ[ℂ] Op (SystemPresentation.update R a.actor (a.Output (a.announce o))).total :=
  ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg MultipartiteSystem.total
    (SystemPresentation.update_eq_set R a.actor (a.Output (a.announce o))))).symm (Equiv.cast
    (congrArg MultipartiteSystem.total
    (SystemPresentation.update_eq_set R a.actor (a.Output (a.announce o))))).symm).toLinearMap).comp
      (a.liftedOperation o)

namespace Program

variable {End : MultipartiteSystem P → Type 1}

/-- The channel denoted by a branch-dependent LOCC program. -/
noncomputable def denote {R : MultipartiteSystem P} (p : Program R End) :
    Op R.total →ₗ[ℂ] Op p.boundary.space :=
  Syntax.rec (motive := fun R p => Op R.total →ₗ[ℂ] Op (boundary p).space)
    (fun {R} _ => (Matrix.reindexLinearEquiv ℂ ℂ (Boundary.leafSpaceEquiv R).symm
      (Boundary.leafSpaceEquiv R).symm).toLinearMap)
    (fun a _ result => ∑ o, ∑ r, result.comp (Matrix.conjLinearMap (a.successorKraus o r)))
    (fun a k result => ∑ o, ∑ r,
      (Matrix.conjLinearMap (Boundary.publicInclKraus (fun y => boundary (k y))
        (a.announce o))).comp
          ((result (a.announce o)).comp (Matrix.conjLinearMap (a.successorKraus o r)))) p

/-- Equal programs have equal denotations in their identified output spaces. -/
theorem denote_congr {R : MultipartiteSystem P} {p q : Program R End}
    (h : p = q) (rho : Op R.total) :
    (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg (fun r : Program R End => r.boundary.space)
      h)) (Equiv.cast (congrArg (fun r : Program R End => r.boundary.space) h))).toLinearMap
      (p.denote rho) = q.denote rho := by
  cases h
  rfl

/-- The finite hidden complete paths through a program.

Only raw outcomes and Kraus multiplicities occur here. Public continuation control still sees
only `A.announce o`, and a private continuation remains independent of `o` and `r`. -/
def Branch {R : MultipartiteSystem P} (p : Program R End) : Type :=
  match p with
  | @Syntax.done _ _ _ _ _ _ _ => Unit
  | @Syntax.announced _ _ _ _ _ _ _ _ _ A k =>
      Σ o : A.Outcome, Σ _r : A.krausIndex o, Branch (k (A.announce o))
  | @Syntax.priv _ _ _ _ _ _ A k =>
      Σ o : A.Outcome, Σ _r : A.instrument.krausIndex o, Branch k

/-- Complete hidden paths form a finite type. -/
instance instFintypeBranch {R : MultipartiteSystem P} (p : Program R End) : Fintype
    p.Branch :=
  match p with
  | @Syntax.done _ _ _ _ _ _ _ => inferInstanceAs (Fintype Unit)
  | @Syntax.announced _ _ _ _ _ _ _ _ _ A k =>
      @Sigma.instFintype A.Outcome
        (fun o => Σ _r : A.krausIndex o, Branch (k (A.announce o)))
        (fun o => @Sigma.instFintype (A.krausIndex o)
          (fun _r => Branch (k (A.announce o)))
          (fun _r => instFintypeBranch (k (A.announce o))) (A.finKrausIndex o))
        inferInstance
  | @Syntax.priv _ _ _ _ _ _ A k =>
      @Sigma.instFintype A.Outcome
        (fun o => Σ _r : A.instrument.krausIndex o, Branch k)
        (fun o => @Sigma.instFintype (A.instrument.krausIndex o)
          (fun _r => Branch k) (fun _r => instFintypeBranch k)
          (A.instrument.finKrausIndex o)) inferInstance

namespace Branch

/-- The complete public exit reached by a hidden branch. -/
def exit {R : MultipartiteSystem P} {p : Program R End} : p.Branch → p.boundary.Exit :=
  match p with
  | @Syntax.done _ _ _ _ _ _ _ => fun _ => ()
  | @Syntax.announced _ _ _ _ _ _ _ _ _ A k => fun b =>
      ⟨A.announce b.1, exit (p := k (A.announce b.1)) b.2.2⟩
  | @Syntax.priv _ _ _ _ _ _ _ k => fun b => exit (p := k) b.2.2

/-- The product of joint-register Kraus matrices along a hidden branch.

Later actions multiply on the left because these matrices act on column vectors from the right. -/
noncomputable def pathKraus {R : MultipartiteSystem P} {p : Program R End} :
    (b : p.Branch) → Matrix (p.boundary.system b.exit).total R.total ℂ :=
  match p with
  | @Syntax.done _ _ _ _ _ R _ => fun _ => (1 : Matrix R.total R.total ℂ)
  | @Syntax.announced _ _ _ _ _ _ _ _ _ A k => fun b =>
      pathKraus (p := k (A.announce b.1)) b.2.2 * A.successorKraus b.1 b.2.1
  | @Syntax.priv _ _ _ _ _ _ A k => fun b =>
      pathKraus (p := k) b.2.2 * A.successorKraus b.1 b.2.1

end Branch

/-- Compose a fixed earlier matrix with a complete dependent family of later matrices. -/
private theorem sum_path_comp {In Mid H : Type}
    [Fintype Mid] [DecidableEq Mid] [Fintype H]
    (Final : H → Type) [∀ h, Fintype (Final h)]
    (A : Matrix Mid In ℂ) (L : ∀ h, Matrix (Final h) Mid ℂ)
    (hL : ∑ h, (L h)ᴴ * L h = 1) :
    ∑ h, (L h * A)ᴴ * (L h * A) = Aᴴ * A := by
  calc
    _ = ∑ h, Aᴴ * ((L h)ᴴ * L h) * A := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (∑ h, Aᴴ * ((L h)ᴴ * L h)) * A := by
      rw [Matrix.sum_mul]
    _ = Aᴴ * (∑ h, (L h)ᴴ * L h) * A := by
      rw [Matrix.mul_sum]
    _ = Aᴴ * A := by rw [hL, Matrix.mul_one]

/-- Completeness of path Kraus matrices at a terminal program. -/
private theorem pathKraus_complete_done {R : MultipartiteSystem P} (value : End R) :
    ∑ b : (Program.done value : Program R End).Branch,
      (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  change ∑ _ : Unit, (1 : Op R.total)ᴴ * (1 : Op R.total) = (1 : Op R.total)
  simp

/-- Completeness of path Kraus matrices is preserved by an announced node. -/
private theorem pathKraus_complete_announced {R : MultipartiteSystem P}
    (A : AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End)
    (ih : ∀ y, ∑ b : (k y).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1) :
    ∑ b : (Program.announced A k).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  simp only [Branch]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  change ∑ o, ∑ r, ∑ b : (k (A.announce o)).Branch,
    (b.pathKraus * A.successorKraus o r)ᴴ * (b.pathKraus * A.successorKraus o r) = 1
  have hcomp (o : A.Outcome) (r : A.krausIndex o) :=
    sum_path_comp
      (Final := fun b : (k (A.announce o)).Branch =>
        (((fun y => (k y).boundary) (A.announce o)).system b.exit).total)
      (A.successorKraus o r) (fun b => b.pathKraus) (ih (A.announce o))
  simp_rw [hcomp]
  exact A.successorKraus_complete

/-- Completeness of path Kraus matrices is preserved by a private node. -/
private theorem pathKraus_complete_priv {R : MultipartiteSystem P}
    (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End)
    (ih : ∑ b : k.Branch, (b.pathKraus)ᴴ * b.pathKraus = 1) :
    ∑ b : (Program.priv A k).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  simp only [Branch]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  change ∑ o, ∑ r, ∑ b : k.Branch,
    (b.pathKraus * A.successorKraus o r)ᴴ * (b.pathKraus * A.successorKraus o r) = 1
  have hcomp (o : A.Outcome) (r : A.instrument.krausIndex o) :=
    sum_path_comp (Final := fun b : k.Branch => (k.boundary.system b.exit).total)
      (A.successorKraus o r) (fun b => b.pathKraus) ih
  simp_rw [hcomp]
  exact A.successorKraus_complete

/-- The path Kraus matrices of a complete program are complete on its input register. -/
theorem pathKraus_complete {R : MultipartiteSystem P} (p : Program R End) :
    ∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 :=
  match p with
  | .done value => pathKraus_complete_done value
  | @Syntax.announced _ _ _ _ _ _ Y finY decY A k =>
      @pathKraus_complete_announced P _ _ Y finY decY _ End _ A k
        (fun y => pathKraus_complete (k y))
  | .priv A k => pathKraus_complete_priv A k (pathKraus_complete k)

/-- A complete program has a complete public exit.

Completeness on the inhabited input register supplies a hidden path, whose public exit lies
in the declared boundary. This does not assert that every declared exit is reachable. -/
theorem nonempty_exit {R : MultipartiteSystem P} [Nonempty R.total] (p : Program R End) : Nonempty
    p.boundary.Exit := by
  classical
  have hsum : (∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus) ≠ 0 := by
    rw [p.pathKraus_complete]
    exact one_ne_zero
  obtain ⟨b, _⟩ := Finset.nonempty_of_sum_ne_zero hsum
  exact ⟨b.exit⟩

/-- A hidden branch's Kraus matrix with its final row embedded into the common boundary space. -/
noncomputable def kraus {R : MultipartiteSystem P} (p : Program R End) (b : p.Branch) :
    Matrix p.boundary.space R.total ℂ :=
  Boundary.exitKraus p.boundary b.exit * b.pathKraus

/-- The common-output Kraus matrix of an announced node factors as the selected public-block
inclusion, the continuation Kraus matrix, and the current local Kraus matrix.

This is the matrix form of public-outcome-controlled continuation for the finite-round LOCC
instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
@[simp] theorem kraus_announced {R : MultipartiteSystem P}
    (A : AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End)
    (o : A.Outcome) (r : A.krausIndex o) (b : (k (A.announce o)).Branch) :
    (Program.announced A k).kraus ⟨o, ⟨r, b⟩⟩ =
      Boundary.publicInclKraus (fun y => (k y).boundary) (A.announce o) *
        ((k (A.announce o)).kraus b * A.successorKraus o r) := by
  simp only [kraus, announced, boundary, Branch.exit, Branch.pathKraus,
    Boundary.exitKraus_announce]
  exact (Matrix.mul_assoc _ _ _).trans (congrArg (_ * ·) (Matrix.mul_assoc _ _ _).symm)

/-- The common-output Kraus matrix of a private node is the continuation Kraus matrix multiplied
by the current local Kraus matrix.

This is sequential composition at a non-announced node of the finite-round LOCC instrument tree
in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
@[simp] theorem kraus_priv {R : MultipartiteSystem P}
    (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End)
    (o : A.Outcome) (r : A.instrument.krausIndex o) (b : k.Branch) :
    (Program.priv A k).kraus ⟨o, ⟨r, b⟩⟩ =
      k.kraus b * A.successorKraus o r := by
  simp only [kraus, Branch.exit, Branch.pathKraus, Matrix.mul_assoc]
  rfl

/-- The common-output Kraus family of a complete program is complete. -/
theorem kraus_complete {R : MultipartiteSystem P} (p : Program R End) :
    ∑ b : p.Branch, (p.kraus b)ᴴ * p.kraus b = 1 := by
  calc
    _ = ∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [kraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Boundary.exitKraus p.boundary b.exit)ᴴ
        (Boundary.exitKraus p.boundary b.exit) b.pathKraus,
        Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
    _ = 1 := p.pathKraus_complete

/-- The complete-path instrument of a program. Its unique observed outcome is `Unit`; the public
exit is represented exactly once, by the corresponding summand of `p.boundary.space`. -/
noncomputable def toInstrument {R : MultipartiteSystem P} (p : Program R End) :
    Instrument R.total p.boundary.space Unit where
  krausIndex _ := p.Branch
  kraus _ := p.kraus
  complete := by simpa using p.kraus_complete


/-- Termination places the input operator in the unique terminal output block. -/
@[simp] theorem denote_done {R : MultipartiteSystem P} (value : End R) :
    (Program.done value).denote = (Matrix.reindexLinearEquiv ℂ ℂ (Boundary.leafSpaceEquiv R).symm
      (Boundary.leafSpaceEquiv R).symm).toLinearMap := rfl

/-- An announced node sums local operations followed by their public continuations. -/
theorem denote_announced {R : MultipartiteSystem P}
    (A : AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End) :
    (Program.announced A k).denote =
      ∑ o : A.Outcome, ∑ r : A.krausIndex o,
        (Matrix.conjLinearMap (Boundary.publicInclKraus (fun y => (k y).boundary)
          (A.announce o))).comp
          ((k (A.announce o)).denote.comp (Matrix.conjLinearMap (A.successorKraus o r))) := rfl

/-- Denotation of a private node sums the local operations followed by the same continuation. -/
theorem denote_priv {R : MultipartiteSystem P}
    (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End) :
    (Program.priv A k).denote =
      ∑ o : A.Outcome, ∑ r : A.instrument.krausIndex o,
        k.denote.comp (Matrix.conjLinearMap (A.successorKraus o r)) := rfl

/-- Denotation of a private node, compressed to the operation at each raw outcome. -/
theorem denote_priv_eq_sum_liftedOperation {R : MultipartiteSystem P}
    (A : PrivateAction R) (k : Program (SystemPresentation.update R A.actor A.Output) End) :
    (Program.priv A k).denote =
      ∑ o : A.Outcome, k.denote.comp
        (((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor A.Output))).symm
          (Equiv.cast (congrArg MultipartiteSystem.total
            (SystemPresentation.update_eq_set R A.actor A.Output))).symm).toLinearMap).comp
            (A.liftedOperation o)) := by
  rw [denote_priv]
  apply LinearMap.ext
  intro rho
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro o _
  rw [← map_sum]
  congr 1
  ext q q'
  simp only [PrivateAction.liftedOperation, krausMap_eq_sum_conjLinearMap, LinearMap.sum_apply,
    LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.sum_apply, Matrix.conjLinearMap_apply_apply, PrivateAction.successorKraus, id_eq]

/-- Denotation of an announced node, compressed to the operation at each raw outcome. -/
theorem denote_announced_eq_sum_liftedOperation {R : MultipartiteSystem P}
    (A : AnnouncedAction R Y)
    (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End) :
    (Program.announced A k).denote =
      ∑ o : A.Outcome,
        (Matrix.conjLinearMap (Boundary.publicInclKraus (fun y => (k y).boundary)
          (A.announce o))).comp
          ((k (A.announce o)).denote.comp
            (((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg MultipartiteSystem.total
              (SystemPresentation.update_eq_set R A.actor (A.Output (A.announce o))))).symm
              (Equiv.cast (congrArg MultipartiteSystem.total
                (SystemPresentation.update_eq_set R A.actor
                  (A.Output (A.announce o))))).symm).toLinearMap).comp
                (A.liftedOperation o))) := by
  rw [denote_announced]
  apply LinearMap.ext
  intro rho
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro o _
  rw [← map_sum, ← map_sum]
  congr 2
  ext q q'
  simp only [AnnouncedAction.liftedOperation, krausMap_eq_sum_conjLinearMap, LinearMap.sum_apply,
    LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.sum_apply, Matrix.conjLinearMap_apply_apply, AnnouncedAction.successorKraus, id_eq]

/-- The denotation is the sum of conjugations by all common-output path Kraus matrices. -/
theorem denote_eq_krausSum {R : MultipartiteSystem P} (p : Program R End) :
    p.denote = ∑ b : p.Branch, Matrix.conjLinearMap (p.kraus b) := by
  induction p with
  | @done S value =>
    have hkraus : (Program.done value).kraus () =
        Boundary.exitKraus (.leaf _) () := Matrix.mul_one _
    change (Program.done value).denote =
      ∑ b : Unit, Matrix.conjLinearMap ((Program.done value).kraus b)
    rw [Fintype.sum_unique, hkraus, denote_done]
    symm
    apply LinearMap.ext
    intro rho
    ext p q
    rcases p with ⟨⟨⟩, p⟩
    rcases q with ⟨⟨⟩, q⟩
    change S.total at p q
    let E : Matrix (Σ _ : Unit, S.total) S.total ℂ := Boundary.exitKraus (.leaf S) ()
    have hE (x : Σ _ : Unit, S.total) (y : S.total) :
        E x y = if x = ⟨(), y⟩ then 1 else 0 := rfl
    change (E * rho * Eᴴ) ⟨(), p⟩ ⟨(), q⟩ = rho p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hE]
  | priv A k ih =>
    rw [denote_priv, ih]
    symm
    simp only [Branch, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro r _
    simp only [kraus_priv]
    simp_rw [Matrix.conjLinearMap_mul]
    apply LinearMap.ext
    intro rho
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  | announced A k ih =>
    rw [denote_announced]
    simp_rw [ih]
    symm
    simp only [Branch, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro r _
    simp only [kraus_announced]
    simp_rw [Matrix.conjLinearMap_mul]
    apply LinearMap.ext
    intro rho
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]

/-- A matrix entry of a branch Kraus operator vanishes outside that branch's exit block. -/
theorem kraus_apply_eq_zero_of_exit_ne {R : MultipartiteSystem P}
    (p : Program R End)
    (b : p.Branch) {e : p.boundary.Exit} (h : e ≠ b.exit) (a : (p.boundary.system e).total) (x :
    R.total) :
    p.kraus b ⟨e, a⟩ x = 0 := by
  simp only [kraus, Matrix.mul_apply, Boundary.exitKraus_apply]
  apply Finset.sum_eq_zero
  intro q _
  rw [ite_eq_right]
  · simp
  · intro heq
    exact h (congrArg Sigma.fst heq)

/-- A program denotation has zero matrix entries between distinct complete public exits. -/
theorem denote_isExitBlockDiagonal {R : MultipartiteSystem P} (p : Program R End)
    (ρ : Op R.total) : Boundary.IsExitBlockDiagonal p.boundary (p.denote ρ) := by
  intro e f a c hef
  rw [p.denote_eq_krausSum]
  simp only [LinearMap.sum_apply, Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases he : e = b.exit
  · have hf : f ≠ b.exit := fun h => hef (he.trans h.symm)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [p.kraus_apply_eq_zero_of_exit_ne b hf c x, star_zero, mul_zero]
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [show (∑ j, p.kraus b ⟨e, a⟩ j * ρ j x) = 0 by
      apply Finset.sum_eq_zero
      intro j _
      rw [p.kraus_apply_eq_zero_of_exit_ne b he a j, zero_mul], zero_mul]

/-- **An announced node read inside one public block.** Let the announcement relabel raw
outcomes by the equivalence `e`. In the block `A.announce o`, the denotation is the continuation
`k (A.announce o)` applied to the lifted operation of `o`; all other outcomes enter different
public blocks. The continuation boundary may depend on the announced value. -/
theorem denote_then_publicSpaceEquiv_symm_apply {R : MultipartiteSystem P} {Pub : Type}
    [Fintype Pub] [DecidableEq Pub] (A : AnnouncedAction R Pub) (e : A.Outcome ≃ Pub)
    (he : ∀ o, A.announce o = e o)
    (k : ∀ y, Program (SystemPresentation.update R A.actor (A.Output y)) End) (ρ : Op R.total) (o
      : A.Outcome)
    (u v : ((k (A.announce o)).boundary).space) :
    (A.then k).denote ρ ((Boundary.publicSpaceEquiv (fun y => (k y).boundary)).symm ⟨A.announce
      o, u⟩)
        ((Boundary.publicSpaceEquiv (fun y => (k y).boundary)).symm ⟨A.announce o, v⟩) =
      (k (A.announce o)).denote
        ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor (A.Output (A.announce o))))).symm
          (Equiv.cast (congrArg MultipartiteSystem.total
            (SystemPresentation.update_eq_set R A.actor
              (A.Output (A.announce o))))).symm).toLinearMap
              (A.liftedOperation o ρ)) u v := by
  rw [denote_announced_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
  have hrow (w : ((k (A.announce o)).boundary).space) :
      Boundary.publicInclKraus (fun y => (k y).boundary) (A.announce o)
          ((Boundary.publicSpaceEquiv (fun y => (k y).boundary)).symm ⟨A.announce o, w⟩) =
      Pi.single w 1 := by
    funext w'
    rw [Boundary.publicInclKraus_apply, Equiv.apply_symm_apply, Pi.single_apply]
    exact if_congr (by rw [Sigma.mk.inj_iff, heq_eq_eq]; exact (and_iff_right rfl).trans eq_comm)
      rfl rfl
  have hrow_ne {other : A.Outcome} (hne : other ≠ o) (w : ((k (A.announce o)).boundary).space) :
      Boundary.publicInclKraus (fun y => (k y).boundary) (A.announce other)
          ((Boundary.publicSpaceEquiv (fun y => (k y).boundary)).symm ⟨A.announce o, w⟩) = 0 :=
    funext fun _ => Boundary.publicInclKraus_apply_eq_zero_of_fst_ne _ (by
      rw [Equiv.apply_symm_apply]
      exact fun h => hne (e.injective (by simpa only [he] using h)).symm) _
  rw [Fintype.sum_eq_single o]
  · rw [Matrix.conjLinearMap_apply_of_row_eq_single _ _ (hrow u) (hrow v), one_mul, star_one,
      mul_one]
  · intro other hne
    exact Matrix.conjLinearMap_apply_eq_zero_of_row_left _ _ (hrow_ne hne u) _

/-- Reading any public block decodes the raw outcome of a fixed-output instrument. -/
theorem denote_ofInstrument_publicSpaceEquiv_apply {R : MultipartiteSystem P}
    (actor : P) {Output Outcome : Type}
    [Fintype Output] [DecidableEq Output]
    [Fintype Outcome]
    (I : Instrument (R.reg actor) Output Outcome) (e : Outcome ≃ Y)
    (k : Y → Program (SystemPresentation.update R actor Output) End)
    (rho : Op R.total) (q : (Boundary.announce Y fun y => (k y).boundary).space) :
    let z := Boundary.publicSpaceEquiv (fun y => (k y).boundary) q
    ((AnnouncedAction.ofInstrument actor I e).then k).denote rho q q =
      (k z.1).denote
        ((AnnouncedAction.ofInstrument actor I e).successorOperation (e.symm z.1) rho)
          z.2 z.2 := by
  obtain ⟨⟨y, u⟩, rfl⟩ := (Boundary.publicSpaceEquiv (fun y => (k y).boundary)).symm.surjective q
  obtain ⟨o, rfl⟩ := e.surjective y
  change _ = (k (e o)).denote
    ((AnnouncedAction.ofInstrument actor I e).successorOperation (e.symm (e o)) rho) u u
  rw [e.symm_apply_apply]
  exact denote_then_publicSpaceEquiv_symm_apply (AnnouncedAction.ofInstrument actor I e)
    e (fun _ => rfl) k rho o u u

/-- An announced action preserves diagonal complete outputs of all its continuations. -/
theorem denote_announced_offDiagonal_zero {R : MultipartiteSystem P}
    (a : AnnouncedAction R Y) (e : a.Outcome ≃ Y)
    (he : ∀ o, a.announce o = e o)
    (k : ∀ y, Program (SystemPresentation.update R a.actor (a.Output y)) End)
    (hk : ∀ y rho u v, u ≠ v → (k y).denote rho u v = 0)
    (rho : Op R.total) (x y : (a.then k).boundary.space) (hxy : x ≠ y) :
    (a.then k).denote rho x y = 0 := by
  let c := Boundary.publicSpaceEquiv (fun y => (k y).boundary)
  obtain ⟨⟨i, x⟩, rfl⟩ := c.symm.surjective x
  obtain ⟨⟨j, y⟩, rfl⟩ := c.symm.surjective y
  by_cases hij : i = j
  · subst j
    have hs : Function.Surjective a.announce := by
      intro z
      obtain ⟨o, ho⟩ := e.surjective z
      exact ⟨o, (he o).trans ho⟩
    obtain ⟨o, rfl⟩ := hs i
    exact (denote_then_publicSpaceEquiv_symm_apply a e he k rho o x y).trans
      (hk _ _ x y (fun h => hxy (by cases h; rfl)))
  · exact (a.then k).denote_isExitBlockDiagonal rho
      ⟨i, x.1⟩ ⟨j, y.1⟩ x.2 y.2 (fun h => hij (congrArg Sigma.fst h))

/-- The complete-path instrument has the directly recursive denotation as its channel. -/
@[simp] theorem toInstrument_channel {R : MultipartiteSystem P} (p : Program R End) :
    p.toInstrument.channel = p.denote := by
  rw [denote_eq_krausSum]
  simp only [toInstrument, Instrument.channel_eq_sum, Instrument.operation,
    krausMap_eq_sum_conjLinearMap, Fintype.sum_unique]

/-- The program denotation is a channel on its natural input and output registers. -/
theorem isChannel_denote {R : MultipartiteSystem P} (p : Program R End) :
    Quantum.Channels.IsChannel p.denote := by
  rw [← p.toInstrument_channel]
  exact p.toInstrument.isChannel_channel

end Program
end LOCC
