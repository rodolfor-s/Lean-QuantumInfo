import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Boundary.Uniform
import QCryptLean.LOCC.Implementability.Separable
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.Uniform
import QCryptLean.LOCC.Transcript
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Channels.Separable

/-! # Uniform Separable -/


open scoped Matrix BigOperators Kronecker
open Matrix

noncomputable section

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]


namespace Boundary

/-- Every complete exit of a uniform boundary carries the defining multipartite system's register at
each party.

Like `Boundary.uniformSystemEquiv` this computes by recursion on the transcript word alone, so it
never transports across `Boundary.uniform_system`. -/
def uniformSystemRegEquiv (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit) (i : P) :
    ((uniform S T).system e).reg i ≃ (S).reg i :=
  match T with
  | .nil => Equiv.refl _
  | @TList.cons _ _ _ T => uniformSystemRegEquiv S T e.2 i

/-- The joint uniform-system identification acts party by party. -/
theorem uniformSystemEquiv_apply (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit)
    (q : ((uniform S T).system e).total) (i : P) :
    uniformSystemEquiv S T e q i = uniformSystemRegEquiv S T e i (q i) :=
  match T with
  | .nil => rfl
  | @TList.cons _ _ _ T => uniformSystemEquiv_apply S T e.2 q i

/-- `Boundary.uniformSystemEquiv` is the product of its party-local components. -/
theorem uniformSystemEquiv_eq_piCongrRight (S : MultipartiteSystem P) (T : TList)
    (e : (uniform S T).Exit) :
    uniformSystemEquiv S T e = Equiv.piCongrRight (uniformSystemRegEquiv S T e) :=
  Equiv.ext fun q => funext fun i => uniformSystemEquiv_apply S T e q i

end Boundary

namespace Program.ExitBranch

/-- Read the local factors at a uniform exit in the boundary's defining final system. -/
noncomputable def uniformPartyKraus {R S : MultipartiteSystem P} {T : TList}
    {t : (Boundary.uniform S T).Exit}
    (K : ∀ i, Matrix (((Boundary.uniform S T).system t).reg i) (R.reg i) ℂ) (i : P) :
    Matrix (S.reg i) (R.reg i) ℂ :=
  (K i).submatrix (Boundary.uniformSystemRegEquiv S T t i).symm id

/-- The uniform local coordinates multiply out to the joint uniform coordinates. -/
theorem famKraus_uniformPartyKraus {R S : MultipartiteSystem P} {T : TList}
    {t : (Boundary.uniform S T).Exit}
    (K : ∀ i, Matrix (((Boundary.uniform S T).system t).reg i) (R.reg i) ℂ) :
    Matrix.piTensorProduct (uniformPartyKraus K) =
    (Matrix.piTensorProduct K).submatrix (Boundary.uniformSystemEquiv S T t).symm id := by
  rw [Boundary.uniformSystemEquiv_eq_piCongrRight]
  rfl

end Program.ExitBranch

namespace TwoParty

open Quantum.Channels
open Program.ExitBranch (uniformPartyKraus)

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable (C D) in
/-- Natural output coordinates assigning the full public transcript to Bob. -/
def uniformBobEquiv (T : TList) :
    (Boundary.uniform (system C D) T).space ≃ C × (D × Transcript T) :=
  (Boundary.uniformSpaceEquiv (system C D) T).trans
    (((pairEquiv C D).prodCongr (Equiv.refl (Transcript T))).trans
    (Equiv.prodAssoc C D (Transcript T)))

/-- Bob's accumulated matrix with the complete classical transcript appended to its output. -/
noncomputable def recordedBobKraus {T : TList}
    {t : (Boundary.uniform (system C D) T).Exit}
    (K : ∀ i, Matrix (((Boundary.uniform (system C D) T).system t).reg i)
    ((system A B).reg i) ℂ) : Matrix (D × Transcript T) B ℂ :=
  Matrix.of fun p b => if p.2 = Boundary.uniformExitEquiv (system C D) T t then
    uniformPartyKraus K Party.bob p.1 b else 0

/-- Including one public exit is product Kraus after assigning its transcript to Bob. -/
theorem reindex_exitKraus_mul_piTensorProduct {T : TList}
    {t : (Boundary.uniform (system C D) T).Exit}
    (K : ∀ i, Matrix (((Boundary.uniform (system C D) T).system t).reg i)
    ((system A B).reg i) ℂ) :
    Matrix.reindex (uniformBobEquiv C D T) (pairEquiv A B)
    (Boundary.exitKraus (Boundary.uniform (system C D) T) t * Matrix.piTensorProduct K) =
        uniformPartyKraus K Party.alice ⊗ₖ recordedBobKraus K := by
  ext p q
  obtain ⟨⟨u, v⟩, rfl⟩ := (uniformBobEquiv C D T).surjective p
  change (Boundary.exitKraus _ t * Matrix.piTensorProduct K)
    ((uniformBobEquiv C D T).symm (uniformBobEquiv C D T ⟨u, v⟩))
    ((pairEquiv A B).symm q) = _
  rw [Equiv.symm_apply_apply]
  by_cases hu : u = t
  · subst u
    simp only [Matrix.mul_apply, Boundary.exitKraus_apply, ite_mul, one_mul, zero_mul,
      Sigma.mk.inj_iff, heq_eq_eq, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Matrix.piTensorProduct_apply]
    rw [show (Finset.univ : Finset Party) = {Party.alice, Party.bob} from rfl,
      Finset.prod_pair (by decide)]
    simp [uniformBobEquiv, recordedBobKraus, uniformPartyKraus,
      Boundary.uniformSystemEquiv_apply, pairEquiv]
  · simp [Matrix.mul_apply, Boundary.exitKraus_apply, hu,
      uniformBobEquiv, recordedBobKraus, pairEquiv]

/-- A uniform-output program is separable on natural registers with its transcript held by Bob. -/
theorem isSeparableChannel_uniformDenote
    {End : MultipartiteSystem Party → Type 1} {T : TList}
    (p : Program (system A B) End)
    (h : p.boundary = Boundary.uniform (system C D) T) :
    IsSeparableChannel
    ((Matrix.reindexLinearEquiv ℂ ℂ
    ((Equiv.cast (congrArg Boundary.space h)).trans (uniformBobEquiv C D T))
    ((Equiv.cast (congrArg Boundary.space h)).trans (uniformBobEquiv C D T))).toLinearMap.comp
    (p.denote.comp (Matrix.reindexLinearEquiv ℂ ℂ
    (pairEquiv A B).symm (pairEquiv A B).symm).toLinearMap)) := by
  classical
  let Φ := (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.cast (congrArg Boundary.space h))
    (Equiv.cast (congrArg Boundary.space h))).toLinearMap.comp p.denote
  have hΦ : (Boundary.uniform (system C D) T).IsSeparableInstrument Φ := by
    have transfer (E : Boundary Party) (he : p.boundary = E) :
        E.IsSeparableInstrument ((Matrix.reindexLinearEquiv ℂ ℂ
    (Equiv.cast (congrArg Boundary.space he))
    (Equiv.cast (congrArg Boundary.space he))).toLinearMap.comp p.denote) := by
      subst E
      exact p.denote_isSeparableInstrument
    exact transfer _ h
  obtain ⟨I, hI, K, hmap, _⟩ := hΦ
  let := hI
  let KA (x : Σ t, I t) := uniformPartyKraus (K x.1 x.2) Party.alice
  let KB (x : Σ t, I t) := recordedBobKraus (K x.1 x.2)
  have hsum : Φ = krausMap (fun x : Σ t, I t =>
      Boundary.exitKraus _ x.1 * Matrix.piTensorProduct (K x.1 x.2)) := by
    rw [krausMap_eq_sum_conjLinearMap, Fintype.sum_sigma]
    exact hmap
  have he : (Matrix.reindexLinearEquiv ℂ ℂ
    ((Equiv.cast (congrArg Boundary.space h)).trans (uniformBobEquiv C D T))
    ((Equiv.cast (congrArg Boundary.space h)).trans (uniformBobEquiv C D T))).toLinearMap.comp
    (p.denote.comp (Matrix.reindexLinearEquiv ℂ ℂ
    (pairEquiv A B).symm (pairEquiv A B).symm).toLinearMap) =
      krausMap (fun x => KA x ⊗ₖ KB x) := by
    change (Matrix.reindexLinearEquiv ℂ ℂ (uniformBobEquiv C D T)
      (uniformBobEquiv C D T)).toLinearMap.comp
      (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ
        (pairEquiv A B).symm (pairEquiv A B).symm).toLinearMap) = _
    rw [hsum, ← krausMap_reindex]
    congr 1
    funext x
    exact reindex_exitKraus_mul_piTensorProduct (K x.1 x.2)
  refine ⟨Σ t, I t, inferInstance, KA, KB, he, ?_⟩
  have hc := ((isChannel_reindex
    ((Equiv.cast (congrArg Boundary.space h)).trans (uniformBobEquiv C D T))).comp
    (p.isChannel_denote.comp (isChannel_reindex (pairEquiv A B).symm)))
  rw [he] at hc
  have hg := (isTracePreserving_krausMap_iff _).mp hc.2
  ext x y
  have heq := congrFun (congrFun hg x) y
  by_cases hxy : x = y <;> simpa only [Matrix.one_apply, ite_eq_left, ite_eq_right, hxy] using heq

end TwoParty
end LOCC
