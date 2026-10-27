import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Boundary.Graft
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom
import QCryptLean.LOCC.BoundaryKeyLayout.Relabel
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.SystemPresentation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.KeyEnd
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.OutputLayout.Graft
import QCryptLean.QKD.OutputLayout.RegisterKeyed
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-! # Complete Output -/


open Quantum.Operators (Op)

noncomputable section

namespace QKD.BB84

open LOCC QKD.BB84 LOCC.TwoParty

/-- Boundary attached to one complete late-public control: the retained classical tail on quota
success and the existing key-free Unit/Unit leaf on shortage. -/
def completeContinuationBoundary
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) : Boundary Party :=
  if Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e) then
    rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC
  else .leaf Measurement.lateSelectionAbortSystem

/-- **A quota-feasible announced control really runs the classical tail.**

The test is a predicate of the three public cells of stage 2 alone, read off the exit by
`lateSelectionExitEquiv`; this is the sense in which the announced values — and nothing
private — select the continuation. -/
theorem completeContinuationBoundary_of_hasQuotas
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (h : Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e)) :
    completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
      rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC := by
  simp [completeContinuationBoundary, h]

/-- **A short announced control really ends the run with no key register.** -/
theorem completeContinuationBoundary_of_shortage
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (h : ¬Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e)) :
    completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
      .leaf Measurement.lateSelectionAbortSystem := by
  simp [completeContinuationBoundary, h]

/-- Complete public output boundary, preserving all late basis/shuffle metadata and every later
PE, fused, and final-decision announcement. -/
noncomputable def boundary
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) : Boundary Party :=
  (Measurement.lateSelectionBoundary N nK mZ mX).graft
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)

/-- Expose an outer late-public exit together with the complete exit of its attached
quota-dependent continuation. -/
def exitEquiv
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    (boundary N nK mZ mX ℓ ℓEV leakEC).Exit ≃
      Σ e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit,
        (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e).Exit :=
  Boundary.graftExitEquiv _ _

/-- Key-free resource at the canonical Unit/Unit shortage leaf. -/
def lateSelectionAbortOutputLayout :
    QKD.OutputLayout (.leaf Measurement.lateSelectionAbortSystem) :=
  (Program.done KeyEnd.abort).outputLayout (by decide)

/-- Output layout for the continuation attached at one late-public exit. -/
noncomputable def completeContinuationOutputLayout
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    QKD.OutputLayout
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e) := by
  by_cases h : Sampling.HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX e)
  · exact QKD.OutputLayout.transport (by simp [completeContinuationBoundary, h])
      (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
  · exact QKD.OutputLayout.transport (by simp [completeContinuationBoundary, h])
      lateSelectionAbortOutputLayout

/-- The quota-dependent continuation layout keeps Alice as its named key owner. -/
theorem completeContinuationOutputLayout_alice
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC e).alice = .alice := by
  unfold completeContinuationOutputLayout
  split <;> exact QKD.OutputLayout.transport_alice _ _

/-- The quota-dependent continuation layout keeps Bob as its named key owner. -/
theorem completeContinuationOutputLayout_bob
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC e).bob = .bob := by
  unfold completeContinuationOutputLayout
  split <;> exact QKD.OutputLayout.transport_bob _ _

/-- Local Alice/Bob key ownership across quota success, shortage abort, and the final semantic
accept/abort flag, while preserving the complete public exit. -/
noncomputable def outputLayout
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    QKD.OutputLayout
      (boundary N nK mZ mX ℓ ℓEV leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC)


/-- At the literal late-selection exit of a raw control that meets every quota, the complete
continuation boundary is the raw classical-tail boundary
(`completeContinuationBoundary_of_hasQuotas` states this at an arbitrary exit). -/
theorem completeContinuationBoundary_success
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC :=
  QKD.BB84.completeContinuationBoundary_of_hasQuotas N nK mZ mX ℓ ℓEV leakEC _ (by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω from
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω)

/-- At the literal late-selection exit of a raw control with a quota shortage, the complete
continuation boundary is the key-free abort leaf (`completeContinuationBoundary_of_shortage`
states this at an arbitrary exit). -/
theorem completeContinuationBoundary_shortage
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      .leaf Measurement.lateSelectionAbortSystem :=
  QKD.BB84.completeContinuationBoundary_of_shortage N nK mZ mX ℓ ℓEV leakEC _ (by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω from
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω)

/-- At the literal successful late-selection exit, the continuation layout is the raw
classical-tail layout transported along `completeContinuationBoundary_success`. -/
theorem completeContinuationOutputLayout_success
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      QKD.OutputLayout.transport
        (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC ω hω).symm
        (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC) := by
  have hquota : Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω)) := by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω
      from (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω
  unfold QKD.BB84.completeContinuationOutputLayout
  rw [dite_eq_left hquota]

/-- Identifies the raw classical-tail output space with the continuation space at a
successful late-selection exit. -/
def successContinuationSpaceEquiv
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega) :
    RawClassicalTailOutput
        (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC ≃
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit
          N nK mZ mX omega)).space :=
  Equiv.cast
    (congrArg Boundary.space
      (completeContinuationBoundary_success
        N nK mZ mX ell ellEV leakEC omega homega).symm)

/-- The outer public exit of `lateSelectionAbortAt` is the literal exit determined by the same
raw control. -/
private theorem lateSelectionAbortAt_exit
    (N nK mZ mX : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 =
      Measurement.lateSelectionExit N nK mZ mX ω := by
  apply (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).injective
  calc
    QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 = ω := by
      rcases ω with ⟨a, b, order⟩
      rfl
    _ = QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) :=
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv ω).symm

/-- Prefix one successful raw control to a complete raw classical-tail output.  The construction is
choice-free: it uses the literal late-selection exit, the success boundary equality, and the
inverse outer graft-space equivalence. -/
def successCompleteOutputEmbedding
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC ↪
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space where
  toFun q :=
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)).symm
        ⟨Measurement.lateSelectionExit N nK mZ mX ω,
          Equiv.cast (congrArg Boundary.space
            (completeContinuationBoundary_success
              N nK mZ mX ℓ ℓEV leakEC ω hω).symm) q⟩
  inj' := by
    intro q r hqr
    have hpair := congrArg
      (Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)) hqr
    simp only [Equiv.apply_symm_apply] at hpair
    exact (Equiv.cast (congrArg Boundary.space
      (completeContinuationBoundary_success
        N nK mZ mX ℓ ℓEV leakEC ω hω).symm)).injective
          (eq_of_heq (Sigma.mk.inj_iff.mp hpair).2)

/-- Applying the outer graft equivalence to a successful embedded tail returns the literal public
exit and the explicit success-child coordinate.  This is the implementation form of the successful
public-tree branch; the structural protocol context is Chitambar et al., arXiv:1210.4583, §II. -/
theorem graftSpaceEquiv_successCompleteOutputEmbedding
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (q : RawClassicalTailOutput
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary
          N nK mZ mX ell ellEV leakEC)
        (successCompleteOutputEmbedding
          N nK mZ mX ell ellEV leakEC omega homega q) =
      ⟨Measurement.lateSelectionExit N nK mZ mX omega,
        successContinuationSpaceEquiv
          N nK mZ mX ell ellEV leakEC omega homega q⟩ := by
  apply Equiv.apply_symm_apply

/-- The inverse graft map on the literal successful fibre is exactly the successful complete-output
embedding after the explicit child-space transport.  This is an implementation coordinate
identity. -/
theorem graftSpaceEquiv_symm_success_fibre
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (c :
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit
          N nK mZ mX omega)).space) :
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC)).symm
        ⟨Measurement.lateSelectionExit N nK mZ mX omega, c⟩ =
      successCompleteOutputEmbedding
        N nK mZ mX ell ellEV leakEC omega homega
        ((successContinuationSpaceEquiv
          N nK mZ mX ell ellEV leakEC omega homega).symm c) := by
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary
      N nK mZ mX ell ellEV leakEC)
  apply G.injective
  rw [G.apply_symm_apply,
    graftSpaceEquiv_successCompleteOutputEmbedding]
  rw [(successContinuationSpaceEquiv
    N nK mZ mX ell ellEV leakEC omega homega).apply_symm_apply]

/-- An ambient complete output lies in the successful embedding precisely when its outer public exit
is the literal exit for that raw control.  This is the implementation range characterization of the
successful fixed-quota public-tree fibre, not a reachability statement. -/
theorem mem_range_successCompleteOutputEmbedding_iff
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (y :
      (QKD.BB84.boundary
        N nK mZ mX ell ellEV leakEC).space) :
    y ∈ Set.range
        (successCompleteOutputEmbedding
          N nK mZ mX ell ellEV leakEC omega homega) ↔
      (Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary
          N nK mZ mX ell ellEV leakEC) y).1 =
        Measurement.lateSelectionExit N nK mZ mX omega := by
  constructor
  · rintro ⟨q, rfl⟩
    exact congrArg Sigma.fst
      (graftSpaceEquiv_successCompleteOutputEmbedding
        N nK mZ mX ell ellEV leakEC omega homega q)
  · intro hy
    let G := Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC)
    let E := successContinuationSpaceEquiv
      N nK mZ mX ell ellEV leakEC omega homega
    rcases hGy : G y with ⟨e, c⟩
    have he : e = Measurement.lateSelectionExit N nK mZ mX omega := by
      change (G y).1 = Measurement.lateSelectionExit N nK mZ mX omega at hy
      exact (congrArg Sigma.fst hGy).symm.trans hy
    subst e
    refine ⟨E.symm c, ?_⟩
    rw [← graftSpaceEquiv_symm_success_fibre
      N nK mZ mX ell ellEV leakEC omega homega c]
    apply G.injective
    rw [G.apply_symm_apply, hGy]

/-- Prefix one successful raw control to a complete raw classical-tail exit. -/
def successExitMap
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).Exit →
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit :=
  fun e =>
    (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm
      ⟨Measurement.lateSelectionExit N nK mZ mX ω,
        Equiv.cast (congrArg Boundary.Exit
          (completeContinuationBoundary_success
            N nK mZ mX ℓ ℓEV leakEC ω hω).symm) e⟩

/-- The successful complete-exit prefix map is injective. -/
theorem successExitMap_injective
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    Function.Injective
      (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω) := by
  intro e f hef
  have hpair := congrArg
    (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC) hef
  simp only [successExitMap, Equiv.apply_symm_apply] at hpair
  exact (Equiv.cast (congrArg Boundary.Exit
    (completeContinuationBoundary_success
      N nK mZ mX ℓ ℓEV leakEC ω hω).symm)).injective
        (eq_of_heq (Sigma.mk.inj_iff.mp hpair).2)

/-- The complete exit of the successful point embedding is the literal prefixed exit. -/
theorem successCompleteOutputEmbedding_exit
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1 =
      successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω q.1 := by
  have cast_graft_exit (B : Boundary Party) (C : B.Exit → Boundary Party)
      {D : Boundary Party} (e : B.Exit) (h : D = C e) (r : D.space) :
      ((Boundary.graftSpaceEquiv B C).symm
        ⟨e, Equiv.cast (congrArg Boundary.space h) r⟩).1 =
        (Boundary.graftExitEquiv B C).symm
          ⟨e, Equiv.cast (congrArg Boundary.Exit h) r.1⟩ := by
    subst D
    exact Boundary.graftSpaceEquiv_symm_fst B C e r
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let e := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  have hspec := cast_graft_exit B C e h q
  delta successCompleteOutputEmbedding successExitMap QKD.BB84.exitEquiv
  delta QKD.BB84.boundary
  with_reducible_and_instances exact hspec

/-- Prefixing a successful raw control preserves the actual output disposition. -/
theorem successExitMap_disposition
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) =
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).disposition e := by
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let g := Boundary.graftExitEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
  delta QKD.BB84.outputLayout successExitMap QKD.BB84.exitEquiv
  delta QKD.BB84.boundary QKD.OutputLayout.graftFixedParties
  with_reducible_and_instances
    change (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (g (g.symm ⟨outer, Equiv.cast (congrArg Boundary.Exit h) e⟩)).1).disposition
          (g (g.symm ⟨outer, Equiv.cast (congrArg Boundary.Exit h) e⟩)).2 = _
  rw [g.apply_symm_apply]
  rw [show QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC outer =
      QKD.OutputLayout.transport h (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX)
        ℓ ℓEV (@Sampling.packedPESel nK mZ mX) leakEC) from
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω]
  exact QKD.OutputLayout.transport_disposition h _ e

/-- On an accepting raw classical-tail point, the successful complete-output embedding preserves
Alice's and Bob's key coordinates in that order.  The target acceptance proof is derived from
the source acceptance proof through `successExitMap_disposition`. -/
theorem successCompleteOutputEmbedding_acceptedKeys
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (haccept :
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).disposition q.1 = .accept ℓ) :
    let V := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω
    let L := (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout
    let R := (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
    let htarget : L.disposition (V q).1 = .accept ℓ := by
      change (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (V q).1 = .accept ℓ
      rw [successCompleteOutputEmbedding_exit]
      rw [successExitMap_disposition]
      exact haccept
    ((L.acceptCoordinates htarget (V q).2).1,
      (L.acceptCoordinates htarget (V q).2).2.1) =
      ((R.acceptCoordinates haccept q.2).1,
        (R.acceptCoordinates haccept q.2).2.1) := by
  have accepted_pair {B₁ B₂ : Boundary Party}
      (L₁ : QKD.OutputLayout B₁) (L₂ : QKD.OutputLayout B₂)
      (x : B₁.space) (y : B₂.space)
      (h₁ : L₁.disposition x.1 = .accept ℓ)
      (h₂ : L₂.disposition y.1 = .accept ℓ)
      (hk : (L₁.coordinates x.1 x.2).1 ≍ (L₂.coordinates y.1 y.2).1 ∧
        (L₁.coordinates x.1 x.2).2.1 ≍ (L₂.coordinates y.1 y.2).2.1) :
      ((L₁.toBoundaryKeyLayout.acceptCoordinates h₁ x.2).1,
        (L₁.toBoundaryKeyLayout.acceptCoordinates h₁ x.2).2.1) =
      ((L₂.toBoundaryKeyLayout.acceptCoordinates h₂ y.2).1,
        (L₂.toBoundaryKeyLayout.acceptCoordinates h₂ y.2).2.1) := by
    apply Prod.ext
    · exact BoundaryKeyLayout.acceptCoordinates_fst_eq_of_coordinates_fst_heq
        L₁.toBoundaryKeyLayout L₂.toBoundaryKeyLayout h₁ h₂ x.2 y.2 hk.1
    · exact BoundaryKeyLayout.acceptCoordinates_snd_fst_eq_of_coordinates_snd_fst_heq
        L₁.toBoundaryKeyLayout L₂.toBoundaryKeyLayout h₁ h₂ x.2 y.2 hk.2
  have transport_keys {B C : Boundary Party} (h : B = C)
      (L : QKD.OutputLayout B) (r : B.space) :
      let x := Equiv.cast (congrArg Boundary.space h) r
      ((QKD.OutputLayout.transport h L).coordinates x.1 x.2).1 ≍
          (L.coordinates r.1 r.2).1 ∧
        ((QKD.OutputLayout.transport h L).coordinates x.1 x.2).2.1 ≍
          (L.coordinates r.1 r.2).2.1 := by
    cases h
    exact ⟨HEq.rfl, HEq.rfl⟩
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let qc := Equiv.cast (congrArg Boundary.space h) q
  have hLc : Lc outer = QKD.OutputLayout.transport h R :=
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω
  have hc := transport_keys h R q
  rw [← hLc] at hc
  have hp : successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q =
      (Boundary.graftSpaceEquiv B C).symm ⟨outer, qc⟩ := by
    delta successCompleteOutputEmbedding QKD.BB84.boundary
    with_reducible_and_instances rfl
  have hg := QKD.OutputLayout.graftFixedParties_coordinates_keys_heq B C Lc .alice .bob
    (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer qc
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q) hp
  let L := QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC
  let x := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q
  have htarget : L.disposition x.1 = .accept ℓ := by
    change (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
      (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1 = _
    rw [successCompleteOutputEmbedding_exit, successExitMap_disposition]
    exact haccept
  have hk :
      ((QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2).1 ≍
          (R.coordinates q.1 q.2).1 ∧
      ((QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2).2.1 ≍
          (R.coordinates q.1 q.2).2.1 := by
    delta QKD.BB84.outputLayout
    delta QKD.BB84.boundary
    with_reducible_and_instances exact ⟨hg.1.trans hc.1, hg.2.trans hc.2⟩
  with_reducible_and_instances
    exact accepted_pair L R x q htarget haccept hk

/-- The raw-tail and complete actual residual types agree at the explicit successful exit map.
This is the well-typedness law for the residual-coordinate embedding; it is a named obligation,
not a caller premise. -/
theorem successExitMap_residual_type
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.Residual e =
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV
        leakEC).toBoundaryKeyLayout.Residual
          (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) := by
  have cast_graft_residual (B : Boundary Party) (C : B.Exit → Boundary Party)
      (L : ∀ e, QKD.OutputLayout (C e)) (a b : Party) (hab : a ≠ b)
      (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
      {D : Boundary Party} (e : B.Exit) (h : D = C e) (R : QKD.OutputLayout D)
      (hL : L e = QKD.OutputLayout.transport h R) (f : D.Exit) :
      R.Residual f =
        (QKD.OutputLayout.graftFixedParties a b hab L hA hB).Residual
          ((Boundary.graftExitEquiv B C).symm
            ⟨e, Equiv.cast (congrArg Boundary.Exit h) f⟩) := by
    subst D
    exact (congrArg (fun M : QKD.OutputLayout (C e) => M.Residual f) hL).symm.trans
      (QKD.OutputLayout.graftFixedParties_residual B C L a b hab hA hB e f).symm
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  have hLc : Lc outer = QKD.OutputLayout.transport h R :=
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω
  have hspec := cast_graft_residual B C Lc .alice .bob (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer h R hLc e
  delta QKD.OutputLayout.toBoundaryKeyLayout QKD.BB84.outputLayout
  delta successExitMap QKD.BB84.exitEquiv QKD.BB84.boundary
  with_reducible_and_instances exact hspec

/-- The explicit residual-coordinate embedding at one successful raw classical-tail exit.  It
depends only on the raw control, source exit, and source residual; it does not inspect either key
or a complete source output. -/
def successResidualEmbedding
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.Residual e ↪
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV
        leakEC).toBoundaryKeyLayout.Residual
          (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) :=
  (Equiv.cast (successExitMap_residual_type
    N nK mZ mX ℓ ℓEV leakEC ω hω e)).toEmbedding

/-- The residual read from the embedded point is the image of the raw residual under the explicit
residual-coordinate map, at the same complete actual exit. -/
theorem successCompleteOutputEmbedding_residual
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    let V := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω
    let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC
    let L := QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC
    let hexit : (V q).1 = successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω q.1 :=
      successCompleteOutputEmbedding_exit N nK mZ mX ℓ ℓEV leakEC ω hω q
    successResidualEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q.1
        (R.coordinates q.1 q.2).2.2 =
      Equiv.cast (congrArg L.toBoundaryKeyLayout.Residual hexit)
        (L.coordinates (V q).1 (V q).2).2.2 := by
  apply (Equiv.cast (successExitMap_residual_type
    N nK mZ mX ℓ ℓEV leakEC ω hω q.1)).symm.injective
  apply Prod.ext
  · apply Prod.ext <;> exact Unit.ext _ _
  · funext i
    rcases i with ⟨⟨p, hp⟩, hpb⟩
    cases p with
    | alice => exact (hp rfl).elim
    | bob => exact (hpb (Subtype.ext rfl)).elim

/-- The complete output layout reads, at a successfully embedded tail, exactly the output
coordinates of the raw classical tail. -/
theorem successCompleteOutputEmbedding_coordinates_heq
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2 ≍
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).coordinates q.1 q.2 := by
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let qc := Equiv.cast (congrArg Boundary.space h) q
  have hc := QKD.OutputLayout.transport_coordinates_heq h R q
  rw [← show Lc outer = QKD.OutputLayout.transport h R from
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω] at hc
  have hp : successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q =
      (Boundary.graftSpaceEquiv B C).symm ⟨outer, qc⟩ := by
    delta successCompleteOutputEmbedding QKD.BB84.boundary
    with_reducible_and_instances rfl
  have hg := QKD.OutputLayout.graftFixedParties_coordinates_heq B C Lc .alice .bob (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer qc
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q) hp
  delta QKD.BB84.outputLayout
  delta QKD.BB84.boundary
  with_reducible_and_instances exact hg.trans hc

/-- **The successful complete-output embedding is a morphism of key layouts** from the raw
classical tail to the complete output.  Its exit renaming is `successExitMap`, and the complete
layout has the disposition, residual type and coordinates of the raw classical tail on its
image. -/
def successCompleteOutputHom
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    BoundaryKeyLayout.Hom
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout :=
  BoundaryKeyLayout.Hom.ofHEq (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap_injective N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successCompleteOutputEmbedding_exit N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap_disposition N nK mZ mX ℓ ℓEV leakEC ω hω)
    (fun e => (successExitMap_residual_type N nK mZ mX ℓ ℓEV leakEC ω hω e).symm)
    (successCompleteOutputEmbedding_coordinates_heq N nK mZ mX ℓ ℓEV leakEC ω hω)

@[simp] theorem coe_successCompleteOutputHom
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    ⇑(successCompleteOutputHom N nK mZ mX ℓ ℓEV leakEC ω hω) =
      ⇑(successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω) :=
  rfl

/-- The metadata-bearing complete output for a quota shortage.  Its outer exit is read from the
actual `lateSelectionAbortAt` point, while its child coordinate is the unique Unit/Unit abort
payload. -/
def shortageCompleteOutput
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space :=
  let outer := Measurement.lateSelectionAbortAt N nK mZ mX ω hω
  let houter := lateSelectionAbortAt_exit N nK mZ mX ω hω
  let hchild : QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC outer.1 =
      .leaf Measurement.lateSelectionAbortSystem := by
    rw [houter]
    exact completeContinuationBoundary_shortage N nK mZ mX ℓ ℓEV leakEC ω hω
  (Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)).symm
      ⟨outer.1,
        Equiv.cast (congrArg Boundary.space hchild.symm)
          ((Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).symm
            ((TwoParty.pairEquiv Unit Unit).symm ((), ())))⟩

/-- The shortage complete output recovers the original raw control at its outer public exit. -/
theorem shortageCompleteOutput_rawControl
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC)
          (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1).1 =
      ω := by
  have recover (B : Boundary Party) (C : B.Exit → Boundary Party)
      {T : Type} (f : B.Exit → T) (z : Σ e : B.Exit, (C e).space)
      (t : T) (hz : f z.1 = t) :
      f ((Boundary.graftExitEquiv B C
        ((Boundary.graftSpaceEquiv B C).symm z).1).1) = t := by
    rw [← Boundary.graftSpaceEquiv_fst, Equiv.apply_symm_apply]
    exact hz
  have hlast : QKD.BB84.lateSelectionExitEquiv N nK mZ mX
      (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 = ω := by
    rw [lateSelectionAbortAt_exit]
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω
  delta shortageCompleteOutput QKD.BB84.exitEquiv QKD.BB84.boundary
  with_reducible_and_instances
    exact recover (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX) _ ω hlast

/-- The actual complete-output disposition at the metadata-bearing shortage point is abort. -/
theorem shortageCompleteOutput_disposition
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1 = .abort := by
  have graft_disposition (B : Boundary Party) (C : B.Exit → Boundary Party)
      (L : ∀ e, QKD.OutputLayout (C e)) (a b : Party) (hab : a ≠ b)
      (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
      (e : (B.graft C).Exit) :
      (QKD.OutputLayout.graftFixedParties a b hab L hA hB).disposition e =
        (L (Boundary.graftExitEquiv B C e).1).disposition
          (Boundary.graftExitEquiv B C e).2 := by
    rfl
  have hshort : ¬Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC)
          (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1).1) := by
    rw [shortageCompleteOutput_rawControl]
    exact hω
  delta QKD.BB84.exitEquiv at hshort
  delta QKD.BB84.outputLayout
  refine (graft_disposition (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC) .alice .bob
    (by decide) _ _ _).trans ?_
  unfold QKD.BB84.completeContinuationOutputLayout
  split
  · rename_i hquota
    exact (hshort hquota).elim
  · have transport_disposition {B C : Boundary Party} (h : B = C)
        (L : QKD.OutputLayout B) (x : C.Exit) :
        (QKD.OutputLayout.transport h L).disposition x =
          L.disposition (h.symm ▸ x) := by
      cases h
      rfl
    rw [transport_disposition]
    rfl

section ShortageFibre

open QKD.BB84.Measurement QKD.BB84.Sampling

/-- Every point over a fixed shortage exit is the literal metadata-bearing shortage output. -/
theorem graftSpaceEquiv_symm_shortage_fibre
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (c : (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space) :
    let G := Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
    G.symm ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, c⟩ =
      shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort := by
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  let s := shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort
  have hsubLit : Subsingleton
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX omega)).space := by
    rw [completeContinuationBoundary_shortage
      N nK mZ mX ell ellEV leakEC omega hshort]
    constructor
    intro u v
    apply (Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).injective
    apply (TwoParty.pairEquiv Unit Unit).injective
    apply Prod.ext
    · exact Unit.ext _ _
    · exact Unit.ext _ _
  have hsub : Subsingleton
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
        ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space := by
    exact hsubLit
  have hfst : (G s).1 =
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega := by
    apply (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).injective
    rw [(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply]
    dsimp only [G, s]
    refine (congrArg (lateSelectionExitEquiv N nK mZ mX)
      (Boundary.graftSpaceEquiv_fst (lateSelectionBoundary N nK mZ mX)
        (completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort))).trans ?_
    exact shortageCompleteOutput_rawControl N nK mZ mX ell ellEV leakEC omega hshort
  apply G.injective
  rw [G.apply_symm_apply]
  generalize hgs : G s = gs
  rcases gs with ⟨e, d⟩
  have he : e = (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega := by
    exact (congrArg Sigma.fst hgs).symm.trans hfst
  subst e
  have hcd : c = d := hsub.elim _ _
  subst d
  rfl

end ShortageFibre

/-- The canonical complete output has a public exit in either quota branch. -/
instance boundaryExitNonempty (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Nonempty (boundary N nK mZ mX ℓ ℓEV leakEC).Exit := by
  classical
  let control : Sampling.RawControl N := Classical.choice inferInstance
  let e := Measurement.lateSelectionExit N nK mZ mX control
  apply Nonempty.map (exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm
  refine ⟨⟨e, ?_⟩⟩
  unfold completeContinuationBoundary
  split
  · let data : ClassicalTailData (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC :=
      ⟨fun _ => 0, fun _ => 0, Classical.choice inferInstance, 0, 0⟩
    exact (Boundary.graftExitEquiv _ _).symm
      ⟨(classicalTailExitEquiv _ _ _ _ _ _).symm data, ⟨1, ()⟩⟩
  · exact ()

/-- The canonical complete output space is inhabited. -/
theorem boundary_space_nonempty (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Nonempty (boundary N nK mZ mX ℓ ℓEV leakEC).space := by
  let : ∀ e, Nonempty ((boundary N nK mZ mX ℓ ℓEV leakEC).system e).total :=
    (outputLayout N nK mZ mX ℓ ℓEV leakEC).nonempty_system_total
  infer_instance

/-- The canonical complete output has a nonzero finite coordinate cardinality. -/
theorem boundary_card_ne_zero (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Fintype.card (boundary N nK mZ mX ℓ ℓEV leakEC).space ≠ 0 := by
  let := boundary_space_nonempty N nK mZ mX ℓ ℓEV leakEC
  exact Fintype.card_ne_zero

/-- The canonical output dimension is nonzero. -/
theorem neZero_card_boundary_space (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    NeZero (Fintype.card (boundary N nK mZ mX ℓ ℓEV leakEC).space) :=
  ⟨boundary_card_ne_zero N nK mZ mX ℓ ℓEV leakEC⟩

/-- Decode the actual quota branch into the analytical tail or shortage coordinates. -/
def quotaSpaceEquiv (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) (control : Sampling.RawControl N) :
    (if h : Sampling.HasQuotas nK mZ mX control then
      (retainAlice (Sampling.selectedEmbedding control h)).then <|
        (retainBob (Sampling.selectedEmbedding control h)).then <|
          (forgetAliceBases N (nK + mZ + mX)).then <|
            (forgetBobBases N (nK + mZ + mX)).then <|
              classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                Sampling.packedPESel Sampling.packedXSel leakEC ec δ Q
    else (discardAlice (A := Measurement.CompletedLocalRecord N)
      (B := Measurement.CompletedLocalRecord N)).then
        (discardBob.then (.done KeyEnd.abort))).boundary.space ≃
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX control)).space := by
  by_cases h : Sampling.HasQuotas nK mZ mX control
  · refine (Equiv.cast (congrArg Boundary.space ?_)).trans <|
      (rawClassicalTailOutputEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        Sampling.packedPESel Sampling.packedXSel leakEC ec δ Q).trans <|
          Equiv.cast (congrArg Boundary.space
            (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC control h).symm)
    rw [dite_eq_left h]
    rfl
  · refine Equiv.cast (congrArg Boundary.space ?_)
    rw [dite_eq_right h]
    exact (completeContinuationBoundary_shortage N nK mZ mX ℓ ℓEV leakEC control h).symm

/-- Flatten three public control cells and decode their continuation coordinates. -/
private def controlSpaceEquiv {N : ℕ} (D : Sampling.RawControl N → Boundary Party)
    (H : Boundary Party) (exit : H.Exit ≃ Sampling.RawControl N) (C : H.Exit → Boundary Party)
    (T : ∀ control, (D control).space ≃ (C (exit.symm control)).space) :
    (Boundary.announce (Fin N → Measurement.Basis) (fun a =>
      Boundary.announce (Fin N → Measurement.Basis) (fun b =>
        Boundary.announce (Sampling.Shuffle a b) (fun order => D ⟨a, b, order⟩)))).space ≃
      (H.graft C).space :=
  let coords :
      (Boundary.announce (Fin N → Measurement.Basis) (fun a =>
        Boundary.announce (Fin N → Measurement.Basis) (fun b =>
          Boundary.announce (Sampling.Shuffle a b) (fun order => D ⟨a, b, order⟩)))).space ≃
        Σ control : Sampling.RawControl N, (D control).space :=
    { toFun := fun q => ⟨⟨q.1.1, q.1.2.1, q.1.2.2.1⟩, ⟨q.1.2.2.2, q.2⟩⟩
      invFun := fun q => ⟨⟨q.1.a, q.1.b, q.1.order, q.2.1⟩, q.2.2⟩
      left_inv := fun ⟨⟨_, _, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _, _⟩, ⟨_, _⟩⟩ => rfl }
  coords.trans ((Equiv.sigmaCongrRight T).trans
    ((Equiv.sigmaCongrLeft exit.symm).trans (Boundary.graftSpaceEquiv H C).symm))

open Measurement Sampling FiniteKey

/-- The actual construction retains exactly the complete analytical output coordinates. -/
def constructionSpaceEquiv
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) :
    (construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).boundary.space ≃
      (boundary N nK mZ mX ℓ ℓEV leakEC).space :=
  let k (control : RawControl N) :
      Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
        (KeyEnd Party.alice Party.bob) :=
    if h : HasQuotas nK mZ mX control then
      (retainAlice (selectedEmbedding control h)).then <|
        (retainBob (selectedEmbedding control h)).then <|
          (forgetAliceBases N (nK + mZ + mX)).then <|
            (forgetBobBases N (nK + mZ + mX)).then <|
              classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                packedPESel packedXSel leakEC ec δ Q
    else discardAlice.then (discardBob.then (.done KeyEnd.abort))
  let publicPrefix := (announceAliceBases N).then fun a => (announceBobBases N).then fun b =>
    (announceShuffle a b).then fun order => k ⟨a, b, order⟩
  let M := Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB Unit N publicPrefix))
  M.trans (controlSpaceEquiv (fun control => (k control).boundary)
      (lateSelectionBoundary N nK mZ mX) (lateSelectionExitEquiv N nK mZ mX)
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
      (quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q))

section
open Measurement Sampling

/-- A public control branch passes the corresponding three local operations to its continuation. -/
theorem construction_public_denote {End : MultipartiteSystem Party → Type 1} (N : ℕ)
    (k : RawControl N → Program (system (CompletedLocalRecord N) (CompletedLocalRecord N)) End)
    (rho : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total)
    (omega : RawControl N) (q q' : (k omega).boundary.space) :
    ((announceAliceBases N).then fun a =>
      (announceBobBases N).then fun b =>
        (announceShuffle a b).then fun order => k ⟨a, b, order⟩).denote rho
          ⟨⟨omega.a, omega.b, omega.order, q.1⟩, q.2⟩
          ⟨⟨omega.a, omega.b, omega.order, q'.1⟩, q'.2⟩ =
      (k omega).denote ((announceShuffle omega.a omega.b).successorOperation omega.order
        ((announceBobBases N).successorOperation omega.b
          ((announceAliceBases N).successorOperation omega.a rho))) q q' := by
  rcases omega with ⟨a, b, order⟩
  refine (Program.denote_then_publicSpaceEquiv_symm_apply
    (announceAliceBases N) (Equiv.refl _) (fun _ => rfl)
    (fun a => (announceBobBases N).then fun b =>
      (announceShuffle a b).then fun order => k ⟨a, b, order⟩)
    rho a ⟨⟨b, order, q.1⟩, q.2⟩ ⟨⟨b, order, q'.1⟩, q'.2⟩).trans ?_
  refine (Program.denote_then_publicSpaceEquiv_symm_apply
    (announceBobBases N) (Equiv.refl _) (fun _ => rfl)
    (fun b => (announceShuffle a b).then fun order => k ⟨a, b, order⟩)
    _ b ⟨⟨order, q.1⟩, q.2⟩ ⟨⟨order, q'.1⟩, q'.2⟩).trans ?_
  exact Program.denote_then_publicSpaceEquiv_symm_apply
    (announceShuffle a b) (Equiv.refl _) (fun _ => rfl)
    (fun order => k ⟨a, b, order⟩) _ order q q'

end

/-- The quota continuation ends with owned keys or discarded registers. -/
private theorem quota_outputLayout_registerKeyed
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) (control : Sampling.RawControl N) :
    ((if h : Sampling.HasQuotas nK mZ mX control then
      (retainAlice (Sampling.selectedEmbedding control h)).then <|
        (retainBob (Sampling.selectedEmbedding control h)).then <|
          (forgetAliceBases N (nK + mZ + mX)).then <|
            (forgetBobBases N (nK + mZ + mX)).then <|
              classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                Sampling.packedPESel Sampling.packedXSel leakEC ec δ Q
    else (discardAlice (A := Measurement.CompletedLocalRecord N)
      (B := Measurement.CompletedLocalRecord N)).then
        (discardBob.then (.done KeyEnd.abort))).outputLayout (by decide)).RegisterKeyed := by
  by_cases h : Sampling.HasQuotas nK mZ mX control
  · rw [dite_eq_left h]
    exact classicalTail_outputLayout_registerKeyed _ _ _ _ _ _ _ _ _ _
  · rw [dite_eq_right h]
    refine ⟨OutputLayout.residual_subsingleton _ rfl rfl
      (fun _ => inferInstanceAs (Subsingleton Unit))
      (fun _ => inferInstanceAs (Subsingleton Unit)), ?_, ?_⟩
    · intro e q
      rfl
    · intro e q
      rfl

/-- Every completed construction branch keeps only its owned keys or two discarded registers. -/
theorem construction_outputLayout_registerKeyed
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ) :
    ((construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).outputLayout
      (by decide)).RegisterKeyed := by
  have hAnnounce {R : MultipartiteSystem Party} {Y : Type} [Fintype Y] [DecidableEq Y]
      (a : AnnouncedAction R Y)
      (k : ∀ y, Program (SystemPresentation.update R a.actor (a.Output y))
        (KeyEnd Party.alice Party.bob))
      (hk : ∀ y, ((k y).outputLayout (by decide)).RegisterKeyed) :
      ((a.then k).outputLayout (by decide)).RegisterKeyed :=
    ⟨fun e => (hk e.1).residual e.2,
      fun e q => (hk e.1).aliceKey e.2 q, fun e q => (hk e.1).bobKey e.2 q⟩
  have hMeasure (F : Type) [Fintype F] [DecidableEq F] (r : ℕ)
      (k : Program (system (Measurement.streamRegister (Measurement.finishAcc F r) 0)
        (Measurement.streamRegister (Measurement.finishAcc F r) 0))
        (KeyEnd Party.alice Party.bob))
      (hk : (k.outputLayout (by decide)).RegisterKeyed) :
      ((measureRounds pA pB F r k).outputLayout (by decide)).RegisterKeyed := by
    induction r generalizing F with
    | zero => exact hk
    | succ r ih => exact ih (F × Measurement.StoredRecord) k hk
  unfold construction
  apply hMeasure
  apply hAnnounce
  intro a
  apply hAnnounce
  intro b
  apply hAnnounce
  intro order
  exact quota_outputLayout_registerKeyed N nK mZ mX ℓ ℓEV leakEC ec δ Q ⟨a, b, order⟩

open Measurement Sampling FiniteKey
/-- Expose the coordinate composition without unfolding its applied inverse. -/
private theorem constructionSpaceEquiv_eq
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ) :
    let k (control : RawControl N) :
        Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
          (KeyEnd Party.alice Party.bob) :=
      if h : HasQuotas nK mZ mX control then
        (retainAlice (selectedEmbedding control h)).then <|
          (retainBob (selectedEmbedding control h)).then <|
            (forgetAliceBases N (nK + mZ + mX)).then <|
              (forgetBobBases N (nK + mZ + mX)).then <|
                classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                  packedPESel packedXSel leakEC ec δ Q
      else discardAlice.then (discardBob.then (.done KeyEnd.abort))
    let publicPrefix := (announceAliceBases N).then fun a => (announceBobBases N).then fun b =>
      (announceShuffle a b).then fun order => k ⟨a, b, order⟩
    let M := Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB Unit N publicPrefix))
    constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q =
      M.trans (controlSpaceEquiv (fun control => (k control).boundary)
        (lateSelectionBoundary N nK mZ mX) (lateSelectionExitEquiv N nK mZ mX)
        (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
        (quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q)) := rfl

/-- Branchwise register-preserving coordinates preserve registers after public control. -/
private def controlExitRenaming {N : ℕ}
    (D : RawControl N → Boundary Party) (H : Boundary Party)
    (exit : H.Exit ≃ RawControl N) (C : H.Exit → Boundary Party)
    (T : ∀ control, (D control).space ≃ (C (exit.symm control)).space)
    (h : ∀ control, Boundary.ExitRenaming (T control)) :
    Boundary.ExitRenaming (controlSpaceEquiv D H exit C T) := by
  let flat :
      (Boundary.announce (Fin N → Basis) (fun a =>
        Boundary.announce (Fin N → Basis) (fun b =>
          Boundary.announce (Shuffle a b) (fun order => D ⟨a, b, order⟩)))).Exit ≃
        Σ control : RawControl N, (D control).Exit :=
    { toFun := fun e => ⟨⟨e.1, e.2.1, e.2.2.1⟩, e.2.2.2⟩
      invFun := fun e => ⟨e.1.a, e.1.b, e.1.order, e.2⟩
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl }
  let G : (Σ control : RawControl N, (D control).Exit) → Σ e : H.Exit, (C e).Exit :=
    fun x => ⟨exit.symm x.1, (h x.1).exits x.2⟩
  have hG : Function.Injective G := by
    rintro ⟨c, e⟩ ⟨d, f⟩ he
    have hcd : c = d := exit.symm.injective (congrArg Sigma.fst he)
    subst d
    have hef : (h c).exits e = (h c).exits f := eq_of_heq (Sigma.mk.inj he).2
    exact congrArg (Sigma.mk c) ((h c).exits_inj hef)
  let E := (Boundary.graftExitEquiv H C).symm ∘ G ∘ flat
  refine ⟨E, (Boundary.graftExitEquiv H C).symm.injective.comp
    (hG.comp flat.injective), ?_, ?_, ?_⟩
  · intro e
    exact (Boundary.system_graftExitEquiv_symm H C
      ⟨exit.symm (flat e).1, (h (flat e).1).exits (flat e).2⟩).trans
        ((h (flat e).1).systems (flat e).2)
  · intro q
    let control : RawControl N := ⟨q.1.1, q.1.2.1, q.1.2.2.1⟩
    let z : (D control).space := ⟨q.1.2.2.2, q.2⟩
    exact (Boundary.graftSpaceEquiv_symm_fst H C (exit.symm control) (T control z)).trans
      (congrArg (fun e => (Boundary.graftExitEquiv H C).symm ⟨exit.symm control, e⟩)
        ((h control).fst z))
  · intro q
    let control : RawControl N := ⟨q.1.1, q.1.2.1, q.1.2.2.1⟩
    let z : (D control).space := ⟨q.1.2.2.2, q.2⟩
    exact (Boundary.graftSpaceEquiv_symm_snd_heq H C (exit.symm control)
      (T control z)).trans ((h control).snd z)

/-- The canonical complete output stores precisely the two owned registers. -/
theorem outputLayout_registerKeyed (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    (outputLayout N nK mZ mX ℓ ℓEV leakEC).RegisterKeyed := by
  have hTransport {B C : Boundary Party} (h : B = C) (L : OutputLayout B)
      (hL : L.RegisterKeyed) : (L.transport h).RegisterKeyed := by
    cases h
    exact hL
  have hAbort : lateSelectionAbortOutputLayout.RegisterKeyed := by
    refine ⟨OutputLayout.residual_subsingleton _ rfl rfl
      (fun _ => inferInstanceAs (Subsingleton Unit))
      (fun _ => inferInstanceAs (Subsingleton Unit)), ?_, ?_⟩
    · intro e q
      rfl
    · intro e q
      rfl
  apply OutputLayout.registerKeyed_graftFixedParties
  intro e
  unfold completeContinuationOutputLayout
  split
  · exact hTransport _ _ (rawClassicalTailOutputLayout_registerKeyed _ _ _ _ _ _)
  · exact hTransport _ _ hAbort

/-- Quota coordinates rename exits while preserving their final multipartite registers. -/
def quotaExitRenaming (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (δ Q : ℝ) (control : RawControl N) :
    Boundary.ExitRenaming (quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q control) := by
  by_cases h : HasQuotas nK mZ mX control
  · simp only [quotaSpaceEquiv, dite_eq_left h]
    exact (Boundary.ExitRenaming.cast (by rw [dite_eq_left h]; rfl)).trans
      ((rawClassicalTailExitRenaming (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      packedPESel packedXSel leakEC ec δ Q).trans (Boundary.ExitRenaming.cast
        (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC control h).symm))
  · simp only [quotaSpaceEquiv, dite_eq_right h]
    exact Boundary.ExitRenaming.cast (by
      rw [dite_eq_right h]
      exact (completeContinuationBoundary_shortage N nK mZ mX ℓ ℓEV leakEC control h).symm)

/-- The complete analytical coordinates rename exits and preserve every final register. -/
def constructionExitRenaming
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ) :
    Boundary.ExitRenaming (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q) := by
  let k (control : RawControl N) :
      Program (system (CompletedLocalRecord N) (CompletedLocalRecord N))
        (KeyEnd Party.alice Party.bob) :=
    if h : HasQuotas nK mZ mX control then
      (retainAlice (selectedEmbedding control h)).then <|
        (retainBob (selectedEmbedding control h)).then <|
          (forgetAliceBases N (nK + mZ + mX)).then <|
            (forgetBobBases N (nK + mZ + mX)).then <|
              classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                packedPESel packedXSel leakEC ec δ Q
    else discardAlice.then (discardBob.then (.done KeyEnd.abort))
  let publicPrefix := (announceAliceBases N).then fun a => (announceBobBases N).then fun b =>
    (announceShuffle a b).then fun order => k ⟨a, b, order⟩
  let M := Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB Unit N publicPrefix))
  rw [constructionSpaceEquiv_eq]
  exact (Boundary.ExitRenaming.cast (measureRounds_boundary pA pB Unit N publicPrefix)).trans
    (controlExitRenaming (fun control => (k control).boundary)
      (lateSelectionBoundary N nK mZ mX) (lateSelectionExitEquiv N nK mZ mX)
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
      (quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q)
      (quotaExitRenaming N nK mZ mX ℓ ℓEV leakEC ec δ Q))

/-- The construction's terminal key resource is the canonical resource in its output coordinates. -/
theorem constructionSpaceEquiv_resource
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (rho : Op (construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).boundary.space) :
    (outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout.ideal
      ((Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)
        (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)).toLinearMap rho) =
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)
      (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)).toLinearMap
      (((construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).outputLayout
        (by decide)).toBoundaryKeyLayout.ideal rho) :=
  BoundaryKeyLayout.ideal_reindexOp_of_exitRenaming
    (L₁ := ((construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).outputLayout
      (by decide)).toBoundaryKeyLayout)
    (L₂ := (outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout)
    (OutputLayout.RegisterKeyed.toBoundaryKeyLayout _
      (construction_outputLayout_registerKeyed pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q))
    (OutputLayout.RegisterKeyed.toBoundaryKeyLayout _
      (outputLayout_registerKeyed N nK mZ mX ℓ ℓEV leakEC))
    (constructionExitRenaming pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q) rho

/-- Forward coordinates cancel the measurement presentation and the continuation decoder. -/
private theorem controlSpaceEquiv_cast_apply {N : ℕ} {S : Type}
    (D : RawControl N → Boundary Party) (H : Boundary Party)
    (exit : H.Exit ≃ RawControl N) (C : H.Exit → Boundary Party)
    (T : ∀ control, (D control).space ≃ (C (exit.symm control)).space)
    (M : S ≃ (Boundary.announce (Fin N → Basis) (fun a =>
      Boundary.announce (Fin N → Basis) (fun b =>
        Boundary.announce (Shuffle a b) (fun order => D ⟨a, b, order⟩)))).space)
    (omega : RawControl N) (z : (D omega).space) :
    (M.trans (controlSpaceEquiv D H exit C T))
      (M.symm ⟨⟨omega.a, omega.b, omega.order, z.1⟩,
        z.2⟩) =
      (Boundary.graftSpaceEquiv H C).symm ⟨exit.symm omega, T omega z⟩ := by
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- Public coordinates evaluate the measured state in the selected continuation. -/
private theorem controlSpaceEquiv_denote
    {End : MultipartiteSystem Party → Type 1} (pA pB : PMF Basis) (N : ℕ)
    (k : RawControl N → Program (system (CompletedLocalRecord N) (CompletedLocalRecord N)) End)
    (H : Boundary Party) (exit : H.Exit ≃ RawControl N) (C : H.Exit → Boundary Party)
    (T : ∀ control, (k control).boundary.space ≃ (C (exit.symm control)).space)
    (rho : Op (weightedStreamSystem Unit N).total) (omega : RawControl N)
    (qa qb : (C (exit.symm omega)).space) :
    let publicPrefix := (announceAliceBases N).then fun a => (announceBobBases N).then fun b =>
      (announceShuffle a b).then fun order => k ⟨a, b, order⟩
    let M := Equiv.cast (congrArg Boundary.space (measureRounds_boundary pA pB Unit N publicPrefix))
    let F := M.trans (controlSpaceEquiv (fun control => (k control).boundary) H exit C T)
    let G := Boundary.graftSpaceEquiv H C
    (Matrix.reindexLinearEquiv ℂ ℂ F F).toLinearMap ((measureRounds pA pB Unit N
      publicPrefix).denote rho)
      (G.symm ⟨exit.symm omega, qa⟩) (G.symm ⟨exit.symm omega, qb⟩) =
      (k omega).denote ((announceShuffle omega.a omega.b).successorOperation omega.order
        ((announceBobBases N).successorOperation omega.b
          ((announceAliceBases N).successorOperation omega.a (measurementState pA pB Unit N rho))))
        ((T omega).symm qa) ((T omega).symm qb) := by
  intro publicPrefix M F G
  have hPoint (z : (k omega).boundary.space) :
      F (M.symm ⟨⟨omega.a, omega.b, omega.order, z.1⟩, z.2⟩) =
        G.symm ⟨exit.symm omega, T omega z⟩ :=
    controlSpaceEquiv_cast_apply (fun control => (k control).boundary) H exit C T M omega z
  have hCancel {A B : Type} (E : A ≃ B) (sigma : Op A) (a b : A) :
      (Matrix.reindexLinearEquiv ℂ ℂ E E).toLinearMap sigma (E a) (E b) = sigma a b :=
    congrArg₂ sigma (E.symm_apply_apply a) (E.symm_apply_apply b)
  obtain ⟨za, rfl⟩ := (T omega).surjective qa
  obtain ⟨zb, rfl⟩ := (T omega).surjective qb
  simp only [Equiv.symm_apply_apply]
  refine (congrArg₂ ((Matrix.reindexLinearEquiv ℂ ℂ F F).toLinearMap ((measureRounds pA pB Unit N
    publicPrefix).denote rho))
    (hPoint za) (hPoint zb)).symm.trans ?_
  refine (hCancel F _ _ _).trans ?_
  refine (congrFun (congrFun (LinearMap.congr_fun
    (measureRounds_then_denote pA pB Unit N publicPrefix) rho)
      ⟨⟨omega.a, omega.b, omega.order, za.1⟩, za.2⟩)
      ⟨⟨omega.a, omega.b, omega.order, zb.1⟩, zb.2⟩).trans ?_
  exact construction_public_denote N k (measurementState pA pB Unit N rho) omega za zb

/-- A complete public-control fibre executes its actual quota continuation. -/
theorem construction_denote_control
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (rho : Op (weightedStreamSystem Unit N).total) (omega : RawControl N)
    (qa qb : (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
      (lateSelectionExit N nK mZ mX omega)).space) :
    let G := Boundary.graftSpaceEquiv (lateSelectionBoundary N nK mZ mX)
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
    (Matrix.reindexLinearEquiv ℂ ℂ (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)
      (constructionSpaceEquiv pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q)).toLinearMap
      ((construction pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).denote rho)
      (G.symm ⟨lateSelectionExit N nK mZ mX omega, qa⟩)
      (G.symm ⟨lateSelectionExit N nK mZ mX omega, qb⟩) =
      ((fun control : RawControl N =>
        if h : HasQuotas nK mZ mX control then
          (retainAlice (selectedEmbedding control h)).then <|
            (retainBob (selectedEmbedding control h)).then <|
              (forgetAliceBases N (nK + mZ + mX)).then <|
                (forgetBobBases N (nK + mZ + mX)).then <|
                  classicalTail (nK + mZ + mX) (mZ + mX) ℓ ℓEV
                    packedPESel packedXSel leakEC ec δ Q
        else discardAlice.then (discardBob.then (.done KeyEnd.abort))) omega).denote
        ((announceShuffle omega.a omega.b).successorOperation omega.order
        ((announceBobBases N).successorOperation omega.b
          ((announceAliceBases N).successorOperation omega.a (measurementState pA pB Unit N rho))))
        ((quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q omega).symm qa)
        ((quotaSpaceEquiv N nK mZ mX ℓ ℓEV leakEC ec δ Q omega).symm qb) := by
  apply controlSpaceEquiv_denote

end QKD.BB84
