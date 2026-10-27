import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Transcript
import QCryptLean.Quantum.Channels.Recording

/-! # Uniform -/


open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Boundary

/-- The boundary whose public announcement tree is `T` and whose every leaf is the multipartite
system `S`. -/
def uniform (S : MultipartiteSystem P) : TList → Boundary P := fun T =>
  match T with
  | .nil => .leaf S
  | @TList.cons Y instY decY T =>
      @Boundary.announce P _ _ Y instY decY fun _ => uniform S T

/-- Complete exits from a uniform boundary are exactly transcripts of its announcement word. -/
def uniformExitEquiv (S : MultipartiteSystem P) : (T : TList) → (uniform S T).Exit ≃ Transcript T :=
    fun T =>
  match T with
  | .nil => Equiv.refl Unit
  | @TList.cons Y _ _ T =>
      (Equiv.sigmaCongrRight fun _ : Y => uniformExitEquiv S T).trans
        (Equiv.sigmaEquivProd Y (Transcript T))

/-- **A uniform boundary declares a complete public exit exactly when its announcement word has
an inhabited transcript.**

An announcement alphabet may be empty — `TList.cons Empty .nil` has no transcript at all — so the
hypothesis is genuine and is not assumed of an arbitrary transcript word. -/
instance instNonemptyUniformExit (S : MultipartiteSystem P) (T : TList) [Nonempty (Transcript T)] :
    Nonempty (uniform S T).Exit :=
  (inferInstance : Nonempty (Transcript T)).elim fun t => ⟨(uniformExitEquiv S T).symm t⟩

/-- Every exit from a uniform boundary selects its defining final multipartite system. -/
@[simp] theorem uniform_system (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit) :
    (uniform S T).system e = S := by
  induction T with
  | nil => rfl
  | @cons Y _ _ T ih =>
      exact ih e.2

/-- Every complete exit of a uniform boundary has the defining terminal register, presented by
a recursive equivalence that computes without transporting across `uniform_system`. -/
def uniformSystemEquiv (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit) :
    ((uniform S T).system e).total ≃ S.total :=
  match T with
  | .nil => Equiv.refl _
  | @TList.cons _ _ _ T => uniformSystemEquiv S T e.2

/-- The output space of a uniform boundary is the final joint register paired with its complete
public transcript. -/
def uniformSpaceEquiv (S : MultipartiteSystem P) : (T : TList) →
    (uniform S T).space ≃ S.total × Transcript T := fun T =>
  match T with
  | .nil => (leafSpaceEquiv S).trans (Equiv.prodPUnit S.total).symm
  | @TList.cons Y _ _ T =>
      { toFun := fun x =>
          let z := uniformSpaceEquiv S T ⟨x.1.2, x.2⟩
          (z.1, (x.1.1, z.2))
        invFun := fun x =>
          let z := (uniformSpaceEquiv S T).symm (x.1, x.2.2)
          ⟨⟨x.2.1, z.1⟩, z.2⟩
        left_inv := by
          rintro ⟨⟨y, e⟩, q⟩
          exact congrArg
            (fun z : (uniform S T).space =>
              (⟨⟨y, z.1⟩, z.2⟩ : (uniform S (.cons Y T)).space))
            ((uniformSpaceEquiv S T).symm_apply_apply ⟨e, q⟩)
        right_inv := by
          rintro ⟨q, y, t⟩
          simp }

/-- The terminal-register component of `uniformSpaceEquiv` is the recursively computing
uniform-system equivalence. -/
@[simp] theorem uniformSpaceEquiv_fst (S : MultipartiteSystem P) (T : TList)
    (e : (uniform S T).Exit) (q : ((uniform S T).system e).total) :
    (uniformSpaceEquiv S T ⟨e, q⟩).1 = uniformSystemEquiv S T e q := by
  induction T with
  | nil =>
      rcases e with ⟨⟩
      rfl
  | @cons Y _ _ T ih =>
      rcases e with ⟨y, e⟩
      exact ih e q

/-- The transcript component of `uniformSpaceEquiv` is the complete-exit coordinate supplied by
`uniformExitEquiv`. -/
@[simp] theorem uniformSpaceEquiv_snd (S : MultipartiteSystem P) (T : TList)
    (e : (uniform S T).Exit) (q : ((uniform S T).system e).total) :
    (uniformSpaceEquiv S T ⟨e, q⟩).2 = uniformExitEquiv S T e := by
  induction T with
  | nil =>
      rcases e with ⟨⟩
      rfl
  | @cons Y _ _ T ih =>
      rcases e with ⟨y, e⟩
      rw [show uniformExitEquiv S (.cons Y T) ⟨y, e⟩ =
        (y, uniformExitEquiv S T e) by rfl]
      exact congrArg (fun t => (y, t)) (ih e q)

/-- In uniform coordinates, including public branch `y` is exactly the Kraus matrix that writes
`y` into the next transcript slot. -/
@[simp] theorem reindex_publicInclKraus_uniform
    (S : MultipartiteSystem P) (Y : Type) [Fintype Y] [DecidableEq Y] (T : TList) (y : Y) :
    Matrix.reindex (uniformSpaceEquiv S (.cons Y T)) (uniformSpaceEquiv S T)
        (publicInclKraus (fun _ : Y => uniform S T) y) =
      Quantum.Channels.writeKraus (A := S.total) (B := Transcript T) Y y := by
  apply Matrix.ext
  intro (p : S.total × Transcript (.cons Y T)) (q : S.total × Transcript T)
  change (if publicSpaceEquiv (fun _ : Y => uniform S T)
      ((uniformSpaceEquiv S (.cons Y T)).symm p) =
        ⟨y, (uniformSpaceEquiv S T).symm q⟩ then (1 : ℂ) else 0) =
    if p.1 = q.1 ∧ p.2.1 = y ∧ p.2.2 = q.2 then 1 else 0
  apply if_congr ?_ rfl rfl
  change (⟨p.2.1, (uniformSpaceEquiv S T).symm (p.1, p.2.2)⟩ :
    Σ _ : Y, (uniform S T).space) = ⟨y, (uniformSpaceEquiv S T).symm q⟩ ↔ _
  simp only [Sigma.mk.inj_iff, heq_eq_eq,
    (uniformSpaceEquiv S T).symm.injective.eq_iff, Prod.ext_iff]
  tauto

end Boundary
end LOCC
