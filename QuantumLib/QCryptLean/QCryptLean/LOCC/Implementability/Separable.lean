import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Implementability.ProductKraus
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Channels.Separable
import QCryptLean.Quantum.Operators.Basic

/-!
# Separable instruments denoted by branch-dependent programs

Every complete hidden path through a finite `Program` composes to one product Kraus matrix across
the parties. Grouping those paths by their public exit gives a dependent separable Kraus
presentation: different exits may have genuinely different final multipartite systems. The common
boundary space is used only to store the orthogonal exit blocks and is never treated as a party
product.

The construction formalizes the finite LOCC instrument trees of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2, together with the treewise
composition and coarse-graining described in Appendix A.
-/

open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Product matrices along complete paths -/

namespace Program

variable [SystemPresentation P] {End : MultipartiteSystem P → Type 1}

namespace Branch

/-- The party-local factors accumulated along one complete hidden path.

Later local actions multiply on the left, matching `Program.Branch.pathKraus`. This explicit
family is the version of multiplying the local Kraus operators along a measurement history
in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Appendix A. -/
noncomputable def partyKraus {R : MultipartiteSystem P} {p : Program R End} :
    (b : p.Branch) → (i : P) → Matrix ((p.boundary.system b.exit).reg i) (R.reg i) ℂ :=
  match p with
  | @Syntax.done _ _ _ _ _ R _ => fun _ i => (1 : Matrix (R.reg i) (R.reg i) ℂ)
  | @Syntax.announced _ _ _ _ _ R _ _ _ A _k => fun b i =>
      partyKraus b.2.2 i *
        (R.localFam A.actor (A.Output (A.announce b.1)) (A.kraus b.1 b.2.1) i).submatrix
          (Equiv.cast (congrArg (fun S => S.reg i)
            (SystemPresentation.update_eq_set R A.actor (A.Output (A.announce b.1))))) id
  | @Syntax.priv _ _ _ _ _ R A _k => fun b i =>
      partyKraus b.2.2 i *
        (R.localFam A.actor A.Output (A.instrument.kraus b.1 b.2.1) i).submatrix
          (Equiv.cast (congrArg (fun S => S.reg i)
            (SystemPresentation.update_eq_set R A.actor A.Output))) id

/-- The joint path Kraus matrix is exactly the product of its explicitly accumulated party
factors.

This is the treewise product-Kraus conclusion for a complete finite LOCC history in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem pathKraus_eq_famKraus {R : MultipartiteSystem P} {p : Program R End}
    (b : p.Branch) : b.pathKraus = Matrix.piTensorProduct (b.partyKraus) := by
  induction p with
  | done value =>
      rcases b with ⟨⟩
      simp [Program.Branch.pathKraus, partyKraus]
  | @announced R Y _ _ A k ih =>
      rcases b with ⟨o, r, b⟩
      simp only [Program.Branch.pathKraus, partyKraus]
      rw [ih (A.announce o) b, AnnouncedAction.successorKraus,
        A.liftedKraus_eq_famKraus,
        famKraus_submatrix_cast (SystemPresentation.update_eq_set R A.actor
    (A.Output (A.announce o))), Matrix.piTensorProduct_mul]
      rfl
  | @priv R A k ih =>
      rcases b with ⟨o, r, b⟩
      simp only [Program.Branch.pathKraus, partyKraus]
      rw [ih b, PrivateAction.successorKraus, A.liftedKraus_eq_famKraus,
        famKraus_submatrix_cast (SystemPresentation.update_eq_set R A.actor A.Output),
        Matrix.piTensorProduct_mul]
      rfl

end Branch

/-- Hidden program branches whose public exit is exactly `e`. -/
def ExitBranch {R : MultipartiteSystem P} (p : Program R End) (e : p.boundary.Exit) : Type :=
  {b : p.Branch // b.exit = e}

/-- Branches over a fixed exit form a finite type. -/
noncomputable instance instFintypeExitBranch {R : MultipartiteSystem P} (p : Program R End) (e :
    p.boundary.Exit) :
    Fintype (p.ExitBranch e) :=
  Fintype.subtype (Finset.univ.filter fun b => b.exit = e) (by simp)

/-- Grouping all hidden branches by their public exit neither loses nor duplicates a branch. -/
def exitBranchSigmaEquiv {R : MultipartiteSystem P} (p : Program R End) :
    (Σ e : p.boundary.Exit, p.ExitBranch e) ≃ p.Branch where
  toFun x := x.2.1
  invFun b := ⟨b.exit, ⟨b, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨e, b, h⟩
    subst e
    rfl
  right_inv _ := rfl

namespace ExitBranch

/-- The accumulated party factors of a branch, transported from its recorded exit to the fixed
exit indexing its fibre. -/
noncomputable def partyKraus {R : MultipartiteSystem P} {p : Program R End}
    {e : p.boundary.Exit} (b : p.ExitBranch e) (i : P) :
    Matrix ((p.boundary.system e).reg i) (R.reg i) ℂ :=
  (b.1.partyKraus i).submatrix
    (Equiv.cast (congrArg (fun f => (p.boundary.system f).reg i) b.2).symm) id

/-- Transporting a branch's product matrix to its fixed exit gives its path Kraus matrix at that
exit. -/
theorem famKraus_partyKraus_eq {R : MultipartiteSystem P} {p : Program R End}
    {e : p.boundary.Exit} (b : p.ExitBranch e) :
    Matrix.piTensorProduct b.partyKraus =
      b.1.pathKraus.submatrix
        (Equiv.cast (congrArg (fun f => (p.boundary.system f).total) b.2).symm) id := by
  rcases b with ⟨b, h⟩
  subst e
  exact b.pathKraus_eq_famKraus.symm

/-- Embedding the transported product matrix into its fixed exit block recovers the program's
common-output Kraus matrix. -/
theorem exitKraus_mul_famKraus_partyKraus {R : MultipartiteSystem P}
    {p : Program R End} {e : p.boundary.Exit} (b : p.ExitBranch e) :
    p.boundary.exitKraus e * Matrix.piTensorProduct b.partyKraus = p.kraus b.1 := by
  rcases b with ⟨b, h⟩
  subst e
  exact congrArg (p.boundary.exitKraus b.exit * ·)
    (famKraus_partyKraus_eq (⟨b, rfl⟩ : p.ExitBranch b.exit))

/-- The Gram matrix of a transported exit-fibre product matrix is the Gram matrix of the
underlying path Kraus matrix. -/
theorem famKraus_partyKraus_conjTranspose_mul_self {R : MultipartiteSystem P} {p :
    Program R End}
    {e : p.boundary.Exit} (b : p.ExitBranch e) :
    (Matrix.piTensorProduct b.partyKraus)ᴴ * Matrix.piTensorProduct b.partyKraus =
      b.1.pathKrausᴴ * b.1.pathKraus := by
  rcases b with ⟨b, h⟩
  subst e
  exact
    (congrArg (fun K => Kᴴ * K) b.pathKraus_eq_famKraus).symm

end ExitBranch

end Program

/-! ## Honest separability over a heterogeneous boundary -/

namespace Boundary

/-- A separable instrument presentation over a heterogeneous public boundary.

The Kraus index and the party-local output matrices depend on the public exit `e`; their product
matrix therefore targets the genuine multipartite system `B.system e`. Only then is it included
into the common classical-quantum output block `B.space`. The second conjunct is global Kraus
completeness, so this predicate certifies an instrument rather than merely a collection of separable
CP maps.

No party-product structure is assigned to `B.space`. This dependent formulation is the finite
outcome separable-instrument representation corresponding to the SEP definition and LOCC tree
coarse-graining in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and
Appendix A. -/
def IsSeparableInstrument {R : MultipartiteSystem P} (B : Boundary P)
    (Φ : Op R.total →ₗ[ℂ] Op B.space) : Prop :=
  ∃ (index : B.Exit → Type) (_ : ∀ e, Fintype (index e))
      (K : ∀ e, index e → ∀ i, Matrix ((B.system e).reg i) (R.reg i) ℂ),
    Φ = ∑ e, ∑ x, Matrix.conjLinearMap (B.exitKraus e * Matrix.piTensorProduct (K e x)) ∧
      ∑ e, ∑ x, (Matrix.piTensorProduct (K e x))ᴴ * Matrix.piTensorProduct (K e x) = 1

/-- Compress a boundary-valued map to the quantum block at one public exit. -/
noncomputable def exitOperation {R : MultipartiteSystem P} (B : Boundary P) (e : B.Exit)
    (Φ : Op R.total →ₗ[ℂ] Op B.space) :
    Op R.total →ₗ[ℂ] Op (B.system e).total :=
  (Matrix.conjLinearMap (B.exitKraus e)ᴴ).comp Φ

end Boundary

namespace Program

variable [SystemPresentation P] {End : MultipartiteSystem P → Type 1}

/-- The denotation of a program is the sum of its product-Kraus branch operations, grouped by
public exit.

This is the dependent-output/direct-sum analogue of the finite LOCC tree expansion and
public-outcome coarse-graining in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denote_eq_exitBranchSum {R : MultipartiteSystem P} (p : Program R End) :
    p.denote = ∑ e : p.boundary.Exit, ∑ b : p.ExitBranch e,
      Matrix.conjLinearMap (p.boundary.exitKraus e * Matrix.piTensorProduct b.partyKraus) := by
  rw [p.denote_eq_krausSum]
  calc
    _ = ∑ b : Σ e : p.boundary.Exit, p.ExitBranch e,
        Matrix.conjLinearMap (p.boundary.exitKraus b.1 * Matrix.piTensorProduct b.2.partyKraus) :=
      (Fintype.sum_equiv p.exitBranchSigmaEquiv _ _ fun b => by
        rw [ExitBranch.exitKraus_mul_famKraus_partyKraus]
        rfl).symm
    _ = ∑ e : p.boundary.Exit, ∑ b : p.ExitBranch e,
        Matrix.conjLinearMap (p.boundary.exitKraus e * Matrix.piTensorProduct b.partyKraus) :=
      Fintype.sum_sigma _

/-- The product Kraus matrices of all hidden branches, grouped by public exit, satisfy the global
completeness relation.

This is the dependent-output/direct-sum analogue of the branchwise completeness relation for the
finite LOCC tree expansion in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem ExitBranch.famKraus_partyKraus_complete {R : MultipartiteSystem P} (p :
    Program R End) :
    (∑ e : p.boundary.Exit, ∑ b : p.ExitBranch e,
    (Matrix.piTensorProduct b.partyKraus)ᴴ * Matrix.piTensorProduct b.partyKraus) = 1 := by
  calc
    _ = ∑ b : Σ e : p.boundary.Exit, p.ExitBranch e,
    (Matrix.piTensorProduct b.2.partyKraus)ᴴ * Matrix.piTensorProduct b.2.partyKraus :=
      (Fintype.sum_sigma _).symm
    _ = ∑ b : p.Branch, b.pathKrausᴴ * b.pathKraus :=
      Fintype.sum_equiv p.exitBranchSigmaEquiv _ _ fun b => by
        exact
          ExitBranch.famKraus_partyKraus_conjTranspose_mul_self b.2
    _ = 1 := p.pathKraus_complete

/-- Every finite branch-dependent LOCC program denotes a complete separable instrument over its
heterogeneous output boundary.

The proof groups complete hidden histories by public exit and uses
`Program.Branch.pathKraus_eq_famKraus`. It is the direct form of the finite LOCC tree
expansion in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Appendix A. -/
theorem denote_isSeparableInstrument {R : MultipartiteSystem P} (p : Program R End) :
    p.boundary.IsSeparableInstrument p.denote := by
  let K : ∀ e, p.ExitBranch e → ∀ i, Matrix ((p.boundary.system e).reg i) (R.reg i) ℂ :=
    fun _ b => b.partyKraus
  refine ⟨fun e => p.ExitBranch e, fun e => p.instFintypeExitBranch e, K, ?_, ?_⟩
  · simpa [K] using p.denote_eq_exitBranchSum
  · simpa [K] using ExitBranch.famKraus_partyKraus_complete p

/-- The CP operation associated with one public exit of a program. -/
noncomputable def denoteExit {R : MultipartiteSystem P} (p : Program R End) (e :
    p.boundary.Exit) :
    Op R.total →ₗ[ℂ] Op (p.boundary.system e).total :=
  p.boundary.exitOperation e p.denote

/-- The operation at a fixed public exit is the sum of the product-Kraus operations of precisely
the hidden branches in that exit fibre.

This is the fixed-exit part of the dependent-output/direct-sum generalization of the finite
LOCC tree expansion in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denoteExit_eq_exitBranchSum {R : MultipartiteSystem P} (p : Program R End) (e
    : p.boundary.Exit) :
    p.denoteExit e =
      ∑ b : p.ExitBranch e, Matrix.conjLinearMap (Matrix.piTensorProduct b.partyKraus) := by
  apply LinearMap.ext
  intro ρ
  simp only [denoteExit, Boundary.exitOperation, p.denote_eq_exitBranchSum,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single e]
  · apply Finset.sum_congr rfl
    intro b _
    rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]
    congr 1
    rw [← Matrix.mul_assoc, Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro b _
    rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]
    have horth : (p.boundary.exitKraus e)ᴴ * p.boundary.exitKraus f = 0 :=
      sigmaInclKraus_conjTranspose_mul_of_ne (fun z => (p.boundary.system z).total) hfe.symm
    rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
    simp [Matrix.conjLinearMap]
  · simp

/-- Reinserting every fixed-exit operation into its boundary block and summing recovers the full
program denotation.

This is the public-exit reassembly in the dependent-output/direct-sum generalization of the
finite LOCC tree coarse-graining in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denote_eq_exitKraus_comp_denoteExit_sum {R : MultipartiteSystem P}
    (p : Program R End) :
    p.denote =
      ∑ e : p.boundary.Exit, (Matrix.conjLinearMap (p.boundary.exitKraus e)).comp (p.denoteExit e)
    := by
  rw [p.denote_eq_exitBranchSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [p.denoteExit_eq_exitBranchSum]
  apply LinearMap.ext
  intro ρ
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]

end Program

namespace Boundary.IsSeparableInstrument

/-- Every exit operation of a separable boundary instrument is a separable fixed-system operation.

The result is only a CP exit operation in general. It is not asserted to be trace preserving :
only the sum over all exits satisfies the global completeness equation in
`Boundary.IsSeparableInstrument`. -/
theorem exitOperation_isSeparable {R : MultipartiteSystem P} {B : Boundary P}
    {Φ : Op R.total →ₗ[ℂ] Op B.space} (h : B.IsSeparableInstrument Φ) (e : B.Exit) :
    Quantum.Channels.IsSeparableOperation (B.exitOperation e Φ) := by
  obtain ⟨index, hindex, K, hΦ, _⟩ := h
  refine ⟨index e, hindex e, K e, ?_⟩
  rw [krausMap_eq_sum_conjLinearMap]
  apply LinearMap.ext
  intro ρ
  simp only [Boundary.exitOperation, hΦ, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single e]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]
    congr 1
    rw [← Matrix.mul_assoc, Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro x _
    rw [← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul]
    have horth : (B.exitKraus e)ᴴ * B.exitKraus f = 0 :=
      sigmaInclKraus_conjTranspose_mul_of_ne (fun z => (B.system z).total) hfe.symm
    rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
    simp [Matrix.conjLinearMap]
  · simp

end Boundary.IsSeparableInstrument

namespace Program

variable [SystemPresentation P] {End : MultipartiteSystem P → Type 1}

/-- The operation at every fixed public exit of a program is separable.

It is an individual CP, trace-nonincreasing branch in general; the theorem does not claim that a
single exit is CPTP. -/
theorem denoteExit_isSeparable {R : MultipartiteSystem P} (p : Program R End) (e :
    p.boundary.Exit) :
    Quantum.Channels.IsSeparableOperation (p.denoteExit e) :=
  (p.denote_isSeparableInstrument).exitOperation_isSeparable e

end Program

end LOCC
