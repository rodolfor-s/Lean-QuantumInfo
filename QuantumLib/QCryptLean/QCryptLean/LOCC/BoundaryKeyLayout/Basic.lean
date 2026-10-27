import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Boundary.ExitBlock
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.SharedKeyReplacement
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-! # Basic -/


open Quantum.Channels (
  krausMap_eq_sum_conjLinearMap)

open scoped Matrix BigOperators

open Matrix

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace BoundaryKeyLayout

/-- Whether a complete public exit aborts or accepts a key of the given bit length. -/
inductive Disposition where
  | abort
  | accept (length : ℕ)
deriving DecidableEq

/-- The key alphabet present at one exit. Abort has no nontrivial key coordinate. -/
def Disposition.Key (d : Disposition) : Type :=
  match d with
  | .abort => Unit
  | .accept ℓ => (Fin ℓ → Fin 2)

/-- Every exit key alphabet is finite. -/
instance (d : Disposition) : Fintype d.Key := by
  cases d with
  | abort => change Fintype Unit; infer_instance
  | accept ℓ => change Fintype ((Fin ℓ → Fin 2)); infer_instance

/-- Equality of key values is decidable at every exit. -/
instance (d : Disposition) : DecidableEq d.Key := by
  cases d with
  | abort => change DecidableEq Unit; infer_instance
  | accept ℓ => change DecidableEq ((Fin ℓ → Fin 2)); infer_instance

/-- Every exit key alphabet is inhabited. -/
instance (d : Disposition) : Nonempty d.Key := by
  cases d with
  | abort => change Nonempty Unit; infer_instance
  | accept ℓ => change Nonempty (Fin ℓ → Fin 2); infer_instance

end BoundaryKeyLayout

/-- Explicit per-exit decomposition into Alice's key, Bob's key, and all retained data.

On abort, the two key factors are `Unit`; the concrete leaf register need only be explicitly
equivalent to `Unit × Unit × Residual e`. Thus multipartite systems built from one-dimensional
`Fin 1` party registers are admitted without any definitional identification with `Unit`.

This is the heterogeneous finite-type encoding of the event-dependent QKD outputs in
arXiv:0809.3019, lines 423-448, and arXiv:2403.11851, lines 549-586. -/
structure BoundaryKeyLayout (B : Boundary P) where
  /-- Abort/accept status and accepted key length for every complete public history. -/
  disposition : B.Exit → BoundaryKeyLayout.Disposition
  /-- Every retained private register at the selected exit. -/
  Residual : B.Exit → Type
  /-- Retained coordinate types are finite. -/
  [finResidual : ∀ e, Fintype (Residual e)]
  /-- Equality of retained coordinates is decidable. -/
  [decResidual : ∀ e, DecidableEq (Residual e)]
  /-- Explicit leaf coordinates; no basis map is recovered by choice. -/
  coordinates : ∀ e, (B.system e).total ≃
    (disposition e).Key × (disposition e).Key × Residual e

attribute [instance] BoundaryKeyLayout.finResidual BoundaryKeyLayout.decResidual

namespace BoundaryKeyLayout

variable {B : Boundary P} (L : BoundaryKeyLayout B)

/-- The complete heterogeneous boundary space in the key and residual coordinates supplied at
each public exit. -/
def spaceCoordinates : B.space ≃
    Σ e : B.Exit, (L.disposition e).Key × (L.disposition e).Key × L.Residual e :=
  Equiv.sigmaCongrRight fun e => L.coordinates e

/-- `spaceCoordinates` preserves the public exit and applies the selected leaf coordinates. -/
@[simp] theorem spaceCoordinates_apply (x : B.space) :
    L.spaceCoordinates x = ⟨x.1, L.coordinates x.1 x.2⟩ :=
  rfl

/-- The inverse coordinate map preserves the selected exit and decodes its leaf coordinates. -/
@[simp] theorem spaceCoordinates_symm_apply (e : B.Exit)
    (c : (L.disposition e).Key × (L.disposition e).Key × L.Residual e) :
    L.spaceCoordinates.symm ⟨e, c⟩ = ⟨e, (L.coordinates e).symm c⟩ :=
  rfl

/-- Specialize an accepted leaf's explicit coordinates to its concrete `(Fin ℓ → Fin 2)` keys. -/
def acceptCoordinates {e : B.Exit} {ℓ : ℕ} (h : L.disposition e = .accept ℓ) :
    (B.system e).total ≃ (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × L.Residual e :=
  let hKey : (L.disposition e).Key = (Fin ℓ → Fin 2) := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  (L.coordinates e).trans
    (Equiv.prodCongr (Equiv.cast hKey)
      (Equiv.prodCongr (Equiv.cast hKey) (Equiv.refl _)))

private theorem prod_mk_heq {A B C D : Type} {a : A} {b : B} {c : C} {d : D}
    (ha : a ≍ c) (hb : b ≍ d) : (a, b) ≍ (c, d) := by
  cases ha
  cases hb
  rfl

/-- Specializing an accepting exit changes only the key-coordinate types, not the represented
coordinate value. -/
theorem acceptCoordinates_heq_coordinates {e : B.Exit} {ℓ : ℕ}
    (h : L.disposition e = .accept ℓ) (q : (B.system e).total) :
    L.acceptCoordinates h q ≍ L.coordinates e q := by
  unfold acceptCoordinates
  rcases hc : L.coordinates e q with ⟨ka, kb, r⟩
  simp only [Equiv.trans_apply, hc]
  let hKey : (L.disposition e).Key = (Fin ℓ → Fin 2) := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  change (cast hKey ka, cast hKey kb, r) ≍ (ka, kb, r)
  have hka : cast hKey ka ≍ ka := by simp
  have hkb : cast hKey kb ≍ kb := by simp
  exact prod_mk_heq hka (prod_mk_heq hkb (heq_of_eq rfl))

/-- Project accepted coordinates to Alice's key while retaining the event-dependent key type
used for QKD output in arXiv:2403.11851, lines 394--400 and 549--586. -/
theorem acceptCoordinates_fst_heq_coordinates_fst {e : B.Exit} {ℓ : ℕ}
    (h : L.disposition e = .accept ℓ) (q : (B.system e).total) :
    (L.acceptCoordinates h q).1 ≍ (L.coordinates e q).1 := by
  unfold acceptCoordinates
  rcases hc : L.coordinates e q with ⟨ka, kb, r⟩
  simp only [Equiv.trans_apply, hc]
  let hKey : (L.disposition e).Key = (Fin ℓ → Fin 2) := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  change cast hKey ka ≍ ka
  simp

/-- Project accepted coordinates to Bob's key while retaining the event-dependent key type
used for QKD output in arXiv:0809.3019, lines 423--448. -/
theorem acceptCoordinates_snd_fst_heq_coordinates_snd_fst {e : B.Exit} {ℓ : ℕ}
    (h : L.disposition e = .accept ℓ) (q : (B.system e).total) :
    (L.acceptCoordinates h q).2.1 ≍ (L.coordinates e q).2.1 := by
  unfold acceptCoordinates
  rcases hc : L.coordinates e q with ⟨ka, kb, r⟩
  simp only [Equiv.trans_apply, hc]
  let hKey : (L.disposition e).Key = (Fin ℓ → Fin 2) := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  change cast hKey kb ≍ kb
  simp

/-- Specializing an accepting exit does not touch the retained coordinate. -/
theorem acceptCoordinates_snd_snd {e : B.Exit} {ℓ : ℕ}
    (h : L.disposition e = .accept ℓ) (q : (B.system e).total) :
    (L.acceptCoordinates h q).2.2 = (L.coordinates e q).2.2 := rfl

/-- Equality of unspecialized Alice-key coordinates transports to equality after both layouts are
specialized to the same accepted key length. This projects the event-dependent accepted output
of arXiv:2403.11851, lines 394--400 and 549--586, onto Alice's key. -/
theorem acceptCoordinates_fst_eq_of_coordinates_fst_heq
    {B₁ B₂ : Boundary P}
    (L₁ : BoundaryKeyLayout B₁) (L₂ : BoundaryKeyLayout B₂)
    {e₁ : B₁.Exit} {e₂ : B₂.Exit} {ℓ : ℕ}
    (h₁ : L₁.disposition e₁ = .accept ℓ)
    (h₂ : L₂.disposition e₂ = .accept ℓ)
    (q₁ : (B₁.system e₁).total) (q₂ : (B₂.system e₂).total)
    (hcoord : (L₁.coordinates e₁ q₁).1 ≍
      (L₂.coordinates e₂ q₂).1) :
    (L₁.acceptCoordinates h₁ q₁).1 =
      (L₂.acceptCoordinates h₂ q₂).1 := by
  apply eq_of_heq
  exact (L₁.acceptCoordinates_fst_heq_coordinates_fst h₁ q₁).trans
    (hcoord.trans (L₂.acceptCoordinates_fst_heq_coordinates_fst h₂ q₂).symm)

/-- Equality of unspecialized Bob-key coordinates transports to equality after both layouts are
specialized to the same accepted key length. This projects the event-dependent accepted output
of arXiv:2403.11851, lines 394--400 and 549--586, onto Bob's key. -/
theorem acceptCoordinates_snd_fst_eq_of_coordinates_snd_fst_heq
    {B₁ B₂ : Boundary P}
    (L₁ : BoundaryKeyLayout B₁) (L₂ : BoundaryKeyLayout B₂)
    {e₁ : B₁.Exit} {e₂ : B₂.Exit} {ℓ : ℕ}
    (h₁ : L₁.disposition e₁ = .accept ℓ)
    (h₂ : L₂.disposition e₂ = .accept ℓ)
    (q₁ : (B₁.system e₁).total) (q₂ : (B₂.system e₂).total)
    (hcoord : (L₁.coordinates e₁ q₁).2.1 ≍
      (L₂.coordinates e₂ q₂).2.1) :
    (L₁.acceptCoordinates h₁ q₁).2.1 =
      (L₂.acceptCoordinates h₂ q₂).2.1 := by
  apply eq_of_heq
  exact (L₁.acceptCoordinates_snd_fst_heq_coordinates_snd_fst h₁ q₁).trans
    (hcoord.trans
      (L₂.acceptCoordinates_snd_fst_heq_coordinates_snd_fst h₂ q₂).symm)

/-- One leaf key-replacement Kraus matrix in the layout's explicit coordinates.

The hidden index is `(fresh, oldAlice, oldBob)`. The output keys are both `fresh`, the two input
keys are discarded, and the residual coordinate is preserved. The normalization is
`1 / sqrt (card Key)`, as in the fresh-key Kraus family for the conventional QKD ideal preceding
Definition 4 of arXiv:2403.11851, lines 394-400. -/
noncomputable def leafIdealKraus (e : B.Exit)
    (r : (L.disposition e).Key × (L.disposition e).Key × (L.disposition e).Key) :
    Op (B.system e).total :=
  (SharedKeyReplacement.kraus (R := L.Residual e) r).submatrix
    (L.coordinates e) (L.coordinates e)

/-- Exact coordinate support and normalization of one leaf ideal Kraus matrix. -/
@[simp] theorem leafIdealKraus_apply (e : B.Exit)
    (r : (L.disposition e).Key × (L.disposition e).Key × (L.disposition e).Key)
    (out input : (B.system e).total) :
    L.leafIdealKraus e r out input =
      (((Real.sqrt (Fintype.card ((L.disposition e).Key) : ℝ))⁻¹ : ℝ) : ℂ) *
      if (L.coordinates e out).1 = r.1 ∧ (L.coordinates e out).2.1 = r.1 ∧
          (L.coordinates e input).1 = r.2.1 ∧
          (L.coordinates e input).2.1 = r.2.2 ∧
          (L.coordinates e out).2.2 = (L.coordinates e input).2.2 then 1 else 0 := by
  simp [leafIdealKraus, SharedKeyReplacement.kraus,
    SharedKeyReplacement.weight, Matrix.submatrix_apply]

/-- The key-replacement Kraus family is complete on one exit leaf.

This is the finite operator-sum trace-preservation criterion from arXiv:1504.00233,
lines 879-894: the sum over fresh keys cancels the squared `1 / sqrt (card Key)` normalization. -/
theorem leafIdealKraus_complete (e : B.Exit) :
    ∑ r, (L.leafIdealKraus e r)ᴴ * L.leafIdealKraus e r = 1 := by
  simp only [leafIdealKraus, Matrix.conjTranspose_submatrix]
  simp_rw [Matrix.submatrix_mul_equiv]
  ext i j
  have hc := congrFun (congrFun
    (SharedKeyReplacement.kraus_complete
      (K := (L.disposition e).Key) (R := L.Residual e))
      (L.coordinates e i)) (L.coordinates e j)
  simpa [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply] using hc

/-- Lift one leaf resource to an endomorphism of the heterogeneous boundary space.

The matrix is exactly `J_e * L * J_eᴴ`: input extraction, the per-exit resource, and output
inclusion. -/
noncomputable def ambientKraus
    (r : Σ e : B.Exit, (L.disposition e).Key × (L.disposition e).Key ×
      (L.disposition e).Key) : Op B.space :=
  Boundary.exitKraus B r.1 * L.leafIdealKraus r.1 r.2 * (Boundary.exitKraus B r.1)ᴴ

/-- The ambient leaf-indexed Kraus family is complete on the entire boundary space.

Leaf completeness is combined with `Boundary.sum_exitKraus_mul_conjTranspose`, the resolution of
the classical public-history direct sum from arXiv:1210.4583, Section 2. -/
theorem ambientKraus_complete : ∑ r, (L.ambientKraus r)ᴴ * L.ambientKraus r = 1 := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ e : B.Exit, Boundary.exitKraus B e *
        (∑ r, (L.leafIdealKraus e r)ᴴ * L.leafIdealKraus e r) *
        (Boundary.exitKraus B e)ᴴ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      simp only [ambientKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Boundary.exitKraus B e)ᴴ
          (Boundary.exitKraus B e)
          (L.leafIdealKraus e r * (Boundary.exitKraus B e)ᴴ),
        Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul,
        ← Matrix.mul_assoc (L.leafIdealKraus e r)ᴴ (L.leafIdealKraus e r)
          (Boundary.exitKraus B e)ᴴ,
        ← Matrix.mul_assoc (Boundary.exitKraus B e)
          ((L.leafIdealKraus e r)ᴴ * L.leafIdealKraus e r)
          (Boundary.exitKraus B e)ᴴ]
    _ = ∑ e : B.Exit,
        Boundary.exitKraus B e * (Boundary.exitKraus B e)ᴴ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [L.leafIdealKraus_complete, Matrix.mul_one]
    _ = 1 := Boundary.sum_exitKraus_mul_conjTranspose B

/-- The boundary-derived ideal instrument.

Its observed outcome is `Unit`; the exit, fresh key, and discarded input keys are all hidden
Kraus data and cannot become program control flow. -/
noncomputable def idealInstrument : Instrument B.space B.space Unit where
  krausIndex _ := Σ e : B.Exit, (L.disposition e).Key × (L.disposition e).Key ×
    (L.disposition e).Key
  kraus _ := L.ambientKraus
  complete := by simpa using L.ambientKraus_complete

/-- The boundary-derived ideal channel.

Besides replacing accepted keys and acting identically on abort leaves, this canonical ambient
extension pinches between all distinct complete exits. It is therefore compared with
flag-only ideals only on exit-block-diagonal program outputs, or after explicit full-exit
pinching. -/
noncomputable def ideal : Op B.space →ₗ[ℂ] Op B.space := L.idealInstrument.channel

private theorem submatrix_sandwich {A C : Type} [Fintype A]
    [Fintype C] (e : C ≃ A) (K : Op A) (rho : Op C) :
    K.submatrix e e * rho * (K.submatrix e e)ᴴ =
      (K * rho.submatrix e.symm e.symm * Kᴴ).submatrix e e := by
  have hrho : rho = (rho.submatrix e.symm e.symm).submatrix e e := by
    ext i j
    simp
  have hmul : K.submatrix e e * rho =
      (K * rho.submatrix e.symm e.symm).submatrix e e := by
    conv_lhs => rw [hrho]
    exact Matrix.submatrix_mul_equiv K (rho.submatrix e.symm e.symm) e e e
  rw [hmul, Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv (K * rho.submatrix e.symm e.symm) Kᴴ e e e

/-- The ideal operation before inclusion into the ambient public-boundary direct sum. -/
noncomputable def leafIdeal (e : B.Exit) :
    Op (B.system e).total →ₗ[ℂ] Op (B.system e).total :=
  ∑ r, Matrix.conjLinearMap (L.leafIdealKraus e r)

/-- Complete coordinate characterization of the ideal operation on one leaf.

Only a single shared output key has support; its block is uniform with coefficient
`1 / card Key`, both input keys are summed out, and the residual operator is preserved. This is
the two-key retained form of the conventional QKD ideal preceding Definition 4 of
arXiv:2403.11851, lines 394-400. -/
theorem leafIdeal_coordinate_entry (e : B.Exit) (rho : Op (B.system e).total)
    (a b a' b' : (L.disposition e).Key) (u v : L.Residual e) :
    L.leafIdeal e rho
        ((L.coordinates e).symm (a, b, u)) ((L.coordinates e).symm (a', b', v)) =
      if a = b ∧ a' = b' ∧ a = a' then
        (((Fintype.card ((L.disposition e).Key) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ oldA, ∑ oldB,
            rho ((L.coordinates e).symm (oldA, oldB, u))
              ((L.coordinates e).symm (oldA, oldB, v))
      else 0 := by
  simp only [leafIdeal, LinearMap.sum_apply, Fintype.sum_prod_type, Matrix.conjLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, leafIdealKraus]
  simp_rw [submatrix_sandwich]
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]
  simp_rw [SharedKeyReplacement.kraus_sandwich_apply]
  by_cases h : a = b ∧ a' = b' ∧ a = a'
  · rcases h with ⟨rfl, rfl, rfl⟩
    rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
    simp only [and_self]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.submatrix_apply, Finset.mul_sum]
    · intro fresh _ hne
      have hne' : a ≠ fresh := fun h => hne h.symm
      simp [hne']
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro fresh _
    apply Finset.sum_eq_zero
    intro oldA _
    apply Finset.sum_eq_zero
    intro oldB _
    rw [ite_eq_right]
    intro hf
    exact h ⟨hf.1.trans hf.2.1.symm, hf.2.2.1.trans hf.2.2.2.symm,
      hf.1.trans hf.2.2.1.symm⟩

/-- On its own exit block, an ambient Kraus conjugation is exactly the leaf conjugation applied
to the extracted input block. -/
theorem ambientKraus_sameExit (e : B.Exit)
    (r : (L.disposition e).Key × (L.disposition e).Key × (L.disposition e).Key)
    (rho : Op B.space) (a b : (B.system e).total) :
    Matrix.conjLinearMap (L.ambientKraus ⟨e, r⟩) rho ⟨e, a⟩ ⟨e, b⟩ =
      Matrix.conjLinearMap (L.leafIdealKraus e r) ((LOCC.Boundary.exitBlock _) e rho) a b := by
  rw [← (LOCC.Boundary.exitBlock_apply _) e
    (Matrix.conjLinearMap (L.ambientKraus ⟨e, r⟩) rho) a b]
  simp only [LOCC.Boundary.exitBlock, Matrix.conjLinearMap, ambientKraus, LinearMap.coe_mk,
    AddHom.coe_mk,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Boundary.exitKraus B e)ᴴ (Boundary.exitKraus B e),
    Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul,
    Matrix.mul_one]

/-- An ambient Kraus matrix has no row support outside its indexed complete exit. -/
theorem ambientKraus_apply_eq_zero_of_exit_ne
    (q : Σ e : B.Exit, (L.disposition e).Key × (L.disposition e).Key ×
      (L.disposition e).Key) {e : B.Exit} (h : e ≠ q.1)
    (a : (B.system e).total) (x : B.space) :
    L.ambientKraus q ⟨e, a⟩ x = 0 := by
  simp only [ambientKraus, Matrix.mul_apply, Boundary.exitKraus_apply]
  apply Finset.sum_eq_zero
  intro y _
  have hleft :
      (∑ z, (if (⟨e, a⟩ : B.space) = ⟨q.1, z⟩ then 1 else 0) *
        L.leafIdealKraus q.1 q.2 z y) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    rw [ite_eq_right, zero_mul]
    intro heq
    exact h (congrArg Sigma.fst heq)
  rw [hleft, zero_mul]

/-- The ideal channel is the sum of conjugations by all ambient Kraus matrices. -/
theorem ideal_eq_krausSum :
    L.ideal = ∑ q, Matrix.conjLinearMap (L.ambientKraus q) := by
  simp only [ideal, idealInstrument, Instrument.channel_eq_sum, Instrument.operation,
    krausMap_eq_sum_conjLinearMap,
    Fintype.sum_unique]

/-- A diagonal complete-exit block of the ambient ideal is the leaf ideal applied to the
corresponding extracted input block. -/
theorem ideal_sameExit (rho : Op B.space) (e : B.Exit)
    (a b : (B.system e).total) :
    L.ideal rho ⟨e, a⟩ ⟨e, b⟩ = L.leafIdeal e ((LOCC.Boundary.exitBlock _) e rho) a b := by
  rw [L.ideal_eq_krausSum]
  simp only [LinearMap.sum_apply, Fintype.sum_sigma, Matrix.sum_apply]
  rw [Finset.sum_eq_single e]
  · simp only [leafIdeal, LinearMap.sum_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact L.ambientKraus_sameExit e r rho a b
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro r _
    simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hz : (∑ j, L.ambientKraus ⟨f, r⟩ ⟨e, a⟩ j * rho j x) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [L.ambientKraus_apply_eq_zero_of_exit_ne ⟨f, r⟩ (Ne.symm hfe) a j,
        zero_mul]
    rw [hz, zero_mul]
  · simp

/-- The ambient ideal deletes every matrix entry between distinct complete public histories.

This is full-exit pinching, which is strictly finer than accept/abort-flag pinching when
several histories have the same flag. -/
theorem ideal_crossExit_zero (rho : Op B.space) {e f : B.Exit} (hef : e ≠ f)
    (a : (B.system e).total) (b : (B.system f).total) :
    L.ideal rho ⟨e, a⟩ ⟨f, b⟩ = 0 := by
  rw [L.ideal_eq_krausSum]
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases he : e = q.1
  · have hf : f ≠ q.1 := fun h => hef (he.trans h.symm)
    simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [L.ambientKraus_apply_eq_zero_of_exit_ne q hf b x, star_zero, mul_zero]
  · simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hz : (∑ j, L.ambientKraus q ⟨e, a⟩ j * rho j x) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [L.ambientKraus_apply_eq_zero_of_exit_ne q he a j, zero_mul]
    rw [hz, zero_mul]

/-- Exact ambient same-exit coordinate formula: uniform shared key, discarded input keys, and
preserved retained operator. -/
theorem ideal_coordinate_entry (rho : Op B.space) (e : B.Exit)
    (a b a' b' : (L.disposition e).Key) (u v : L.Residual e) :
    L.ideal rho
        ⟨e, (L.coordinates e).symm (a, b, u)⟩
        ⟨e, (L.coordinates e).symm (a', b', v)⟩ =
      if a = b ∧ a' = b' ∧ a = a' then
        (((Fintype.card ((L.disposition e).Key) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ oldA, ∑ oldB,
            rho ⟨e, (L.coordinates e).symm (oldA, oldB, u)⟩
              ⟨e, (L.coordinates e).symm (oldA, oldB, v)⟩
      else 0 := by
  rw [L.ideal_sameExit rho e]
  rw [L.leafIdeal_coordinate_entry]
  congr 1
  simp only [(LOCC.Boundary.exitBlock_apply _)]

/-- On an abort leaf the derived leaf operation is literally the identity.

The proof uses the explicit equivalence from `Key abort` to `Unit`; it does not require the
concrete leaf registers themselves to be definitionally `Unit`. -/
theorem leafIdeal_abort (e : B.Exit) (h : L.disposition e = .abort)
    (rho : Op (B.system e).total) : L.leafIdeal e rho = rho := by
  have hKey : (L.disposition e).Key = Unit := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  let keyEquiv : (L.disposition e).Key ≃ Unit := Equiv.cast hKey
  let : Subsingleton (L.disposition e).Key :=
    ⟨fun x y => keyEquiv.injective (Subsingleton.elim _ _)⟩
  let : Unique (L.disposition e).Key :=
    { default := keyEquiv.symm ()
      uniq := fun x => Subsingleton.elim _ _ }
  ext a b
  let ca := L.coordinates e a
  let cb := L.coordinates e b
  have ha : a = (L.coordinates e).symm ca := by simp [ca]
  have hb : b = (L.coordinates e).symm cb := by simp [cb]
  rw [ha, hb]
  rcases ca with ⟨ka, kb, u⟩
  rcases cb with ⟨ka', kb', v⟩
  rw [L.leafIdeal_coordinate_entry]
  have hka : ka = default := Subsingleton.elim _ _
  have hkb : kb = default := Subsingleton.elim _ _
  have hka' : ka' = default := Subsingleton.elim _ _
  have hkb' : kb' = default := Subsingleton.elim _ _
  simp [hka, hkb, hka', hkb']

/-- The ambient ideal preserves every operator entry inside an abort exit block. -/
theorem ideal_coordinate_abort (rho : Op B.space) (e : B.Exit)
    (h : L.disposition e = .abort) (a b : (B.system e).total) :
    L.ideal rho ⟨e, a⟩ ⟨e, b⟩ = rho ⟨e, a⟩ ⟨e, b⟩ := by
  rw [L.ideal_sameExit rho e, L.leafIdeal_abort e h, (LOCC.Boundary.exitBlock_apply _)]

/-- On an accepted length-`ℓ` exit, both keys are replaced by one uniform shared
`2 ^ ℓ`-element key while the residual operator is preserved. -/
theorem ideal_coordinate_accept (rho : Op B.space) (e : B.Exit) {ℓ : ℕ}
    (h : L.disposition e = .accept ℓ)
    (a b a' b' : (L.disposition e).Key) (u v : L.Residual e) :
    L.ideal rho
        ⟨e, (L.coordinates e).symm (a, b, u)⟩
        ⟨e, (L.coordinates e).symm (a', b', v)⟩ =
      if a = b ∧ a' = b' ∧ a = a' then
        ((((2 ^ ℓ : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ oldA, ∑ oldB,
            rho ⟨e, (L.coordinates e).symm (oldA, oldB, u)⟩
              ⟨e, (L.coordinates e).symm (oldA, oldB, v)⟩
      else 0 := by
  have hKey : (L.disposition e).Key = (Fin ℓ → Fin 2) := by
    simpa [Disposition.Key] using congrArg Disposition.Key h
  have hcard : Fintype.card ((L.disposition e).Key) = 2 ^ ℓ := by
    exact (Fintype.card_congr (Equiv.cast hKey)).trans (by simp)
  simpa [hcard] using L.ideal_coordinate_entry rho e a b a' b' u v

/-- The ideal acts blockwise on complete public exits: its diagonal block at an exit is the leaf
ideal of the corresponding input block. -/
theorem exitBlock_ideal (rho : Op B.space) (e : B.Exit) :
    (LOCC.Boundary.exitBlock _) e (L.ideal rho) = L.leafIdeal e ((LOCC.Boundary.exitBlock _) e rho)
      := by
  ext a b
  rw [(LOCC.Boundary.exitBlock_apply _), L.ideal_sameExit]

/-- The boundary-derived ideal preserves the trace.

This is trace preservation of the complete ambient Kraus family `ambientKraus_complete`, the finite
operator-sum criterion of arXiv:1504.00233, lines 879-894. -/
theorem trace_ideal (rho : Op B.space) : (L.ideal rho).trace = rho.trace := by
  rw [L.ideal_eq_krausSum]
  simp only [LinearMap.sum_apply, Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.trace_sum]
  calc ∑ q, (L.ambientKraus q * rho * (L.ambientKraus q)ᴴ).trace
      = ∑ q, ((L.ambientKraus q)ᴴ * L.ambientKraus q * rho).trace :=
        Finset.sum_congr rfl fun q _ => Matrix.trace_mul_cycle _ _ _
    _ = ((∑ q, (L.ambientKraus q)ᴴ * L.ambientKraus q) * rho).trace := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = rho.trace := by rw [L.ambientKraus_complete, Matrix.one_mul]

/-- **The ideal fixes every operator carried by the diagonal blocks of aborting exits.**

Such an operator has no coherence between distinct complete exits and no entry on an accepting
exit, so pinching removes nothing and the abort leaves act as the identity. -/
theorem ideal_eq_self_of_abort (rho : Op B.space)
    (h : ∀ y z : B.space, rho y z ≠ 0 → y.1 = z.1 ∧ L.disposition y.1 = .abort) :
    L.ideal rho = rho := by
  have hzero : ∀ y z : B.space, ¬ (y.1 = z.1 ∧ L.disposition y.1 = .abort) → rho y z = 0 :=
    fun y z hyz => not_not.mp fun hne => hyz (h y z hne)
  ext ⟨e, a⟩ ⟨f, b⟩
  by_cases hef : e = f
  · subst hef
    by_cases he : L.disposition e = .abort
    · exact L.ideal_coordinate_abort rho e he a b
    · have hblock : (LOCC.Boundary.exitBlock _) e rho = 0 := by
        ext a' b'
        rw [(LOCC.Boundary.exitBlock_apply _)]
        exact hzero ⟨e, a'⟩ ⟨e, b'⟩ fun hyz => he hyz.2
      rw [L.ideal_sameExit, hblock, map_zero, hzero ⟨e, a⟩ ⟨e, b⟩ fun hyz => he hyz.2,
        Matrix.zero_apply]
  · rw [L.ideal_crossExit_zero rho hef, hzero ⟨e, a⟩ ⟨f, b⟩ fun hyz => hef hyz.1]

/-- A matrix unit inside the diagonal block of an aborting exit is fixed by the ideal. -/
theorem ideal_single_of_abort {y z : B.space} (hyz : y.1 = z.1)
    (h : L.disposition y.1 = .abort) (c : ℂ) :
    L.ideal (Matrix.single y z c) = Matrix.single y z c := by
  refine L.ideal_eq_self_of_abort _ fun y' z' hne => ?_
  rw [Matrix.single_apply] at hne
  split_ifs at hne with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact ⟨hyz, h⟩
  · exact absurd rfl hne


/-- The hidden shared-key Kraus index relabelled by a common bijection of the key alphabet. -/
private def keyIndexEquiv {L₁ L₂ : BoundaryKeyLayout B}
    (key : ∀ e, (L₁.disposition e).Key ≃ (L₂.disposition e).Key) :
    (Σ e : B.Exit, (L₁.disposition e).Key × (L₁.disposition e).Key × (L₁.disposition e).Key) ≃
      (Σ e : B.Exit,
        (L₂.disposition e).Key × (L₂.disposition e).Key × (L₂.disposition e).Key) :=
  Equiv.sigmaCongrRight fun e => Equiv.prodCongr (key e) (Equiv.prodCongr (key e) (key e))

/-- **One leaf key-replacement Kraus matrix is unchanged by the recoordinatization.** The
normalization only sees the key cardinality, which a bijection preserves, and every coordinate
condition is transported by injectivity of `key e` and `residual e`. -/
theorem leafIdealKraus_congr (L₁ L₂ : BoundaryKeyLayout B)
    (key : ∀ e, (L₁.disposition e).Key ≃ (L₂.disposition e).Key)
    (residual : ∀ e, L₁.Residual e ≃ L₂.Residual e)
    (hcoord : ∀ (e : B.Exit) (q : (B.system e).total),
      L₂.coordinates e q =
        (key e (L₁.coordinates e q).1, key e (L₁.coordinates e q).2.1,
          residual e (L₁.coordinates e q).2.2))
    (e : B.Exit)
    (r : (L₁.disposition e).Key × (L₁.disposition e).Key × (L₁.disposition e).Key) :
    L₂.leafIdealKraus e (key e r.1, key e r.2.1, key e r.2.2) = L₁.leafIdealKraus e r := by
  have hcard : Fintype.card ((L₂.disposition e).Key) =
      Fintype.card ((L₁.disposition e).Key) := (Fintype.card_congr (key e)).symm
  ext out input
  rw [leafIdealKraus_apply, leafIdealKraus_apply, hcoord e out, hcoord e input]
  simp [hcard]

/-- The ambient form of `leafIdealKraus_congr`: the two exit inclusions are the boundary's own and
do not depend on the layout. -/
theorem ambientKraus_congr (L₁ L₂ : BoundaryKeyLayout B)
    (key : ∀ e, (L₁.disposition e).Key ≃ (L₂.disposition e).Key)
    (residual : ∀ e, L₁.Residual e ≃ L₂.Residual e)
    (hcoord : ∀ (e : B.Exit) (q : (B.system e).total),
      L₂.coordinates e q =
        (key e (L₁.coordinates e q).1, key e (L₁.coordinates e q).2.1,
          residual e (L₁.coordinates e q).2.2))
    (e : B.Exit)
    (r : (L₁.disposition e).Key × (L₁.disposition e).Key × (L₁.disposition e).Key) :
    L₂.ambientKraus ⟨e, (key e r.1, key e r.2.1, key e r.2.2)⟩ = L₁.ambientKraus ⟨e, r⟩ := by
  simp only [ambientKraus]
  rw [leafIdealKraus_congr L₁ L₂ key residual hcoord e r]

/-- **The boundary-derived ideal key resource is an invariant of the ordered key coordinates and
the retained fibring.**

`key e` is one common relabelling of the key alphabet applied to *both* ordered key slots, so the
"one shared fresh key" condition and the uniform weight are preserved; `residual e` is an
arbitrary bijection of the retained coordinate. The two ambient Kraus families then coincide after
reindexing the hidden index, hence so do the two channels. -/
theorem ideal_congr (L₁ L₂ : BoundaryKeyLayout B)
    (key : ∀ e, (L₁.disposition e).Key ≃ (L₂.disposition e).Key)
    (residual : ∀ e, L₁.Residual e ≃ L₂.Residual e)
    (hcoord : ∀ (e : B.Exit) (q : (B.system e).total),
      L₂.coordinates e q =
        (key e (L₁.coordinates e q).1, key e (L₁.coordinates e q).2.1,
          residual e (L₁.coordinates e q).2.2)) :
    L₂.ideal = L₁.ideal := by
  rw [L₁.ideal_eq_krausSum, L₂.ideal_eq_krausSum]
  refine (Fintype.sum_equiv (keyIndexEquiv key) _ _ ?_).symm
  intro q
  obtain ⟨e, r⟩ := q
  exact congrArg Matrix.conjLinearMap (ambientKraus_congr L₁ L₂ key residual hcoord e r).symm

/-- **Invariance of the ideal resource under a change of retained coordinates that preserves the
exit disposition and both ordered key coordinates.**

The two key alphabets are only *propositionally* equal here — the dispositions agree pointwise, so
`Disposition.Key` agrees after transport — which is why the two key hypotheses are heterogeneous
equalities of the actual coordinate values. -/
theorem ideal_congr_of_disposition_eq (L₁ L₂ : BoundaryKeyLayout B)
    (hdisp : ∀ e, L₁.disposition e = L₂.disposition e)
    (residual : ∀ e, L₁.Residual e ≃ L₂.Residual e)
    (hAlice : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).1 ≍ (L₁.coordinates e q).1)
    (hBob : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).2.1 ≍ (L₁.coordinates e q).2.1)
    (hRes : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).2.2 = residual e (L₁.coordinates e q).2.2) :
    L₂.ideal = L₁.ideal := by
  refine ideal_congr L₁ L₂
    (fun e => Equiv.cast (congrArg Disposition.Key (hdisp e))) residual ?_
  intro e q
  refine Prod.ext ?_ (Prod.ext ?_ (hRes e q))
  · exact eq_of_heq ((hAlice e q).trans
      (cast_heq (congrArg Disposition.Key (hdisp e)) _).symm)
  · exact eq_of_heq ((hBob e q).trans
      (cast_heq (congrArg Disposition.Key (hdisp e)) _).symm)

/-- **The same recoordinatization names the same accepting output point.**

Both ordered keys are read at the common accepted length `ℓ`, and the retained coordinate is
carried by `residual e`, so the two layouts' accepted coordinates invert to one and the same joint
register value. This is what transports an accepted-key classicality statement between the two
presentations. -/
theorem acceptCoordinates_symm_congr (L₁ L₂ : BoundaryKeyLayout B)
    (residual : ∀ e, L₁.Residual e ≃ L₂.Residual e)
    (hAlice : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).1 ≍ (L₁.coordinates e q).1)
    (hBob : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).2.1 ≍ (L₁.coordinates e q).2.1)
    (hRes : ∀ (e : B.Exit) (q : (B.system e).total),
      (L₂.coordinates e q).2.2 = residual e (L₁.coordinates e q).2.2)
    {e : B.Exit} {ℓ : ℕ} (h₁ : L₁.disposition e = .accept ℓ)
    (h₂ : L₂.disposition e = .accept ℓ)
    (a b : (Fin ℓ → Fin 2)) (u : L₁.Residual e) :
    (L₂.acceptCoordinates h₂).symm (a, b, residual e u) =
      (L₁.acceptCoordinates h₁).symm (a, b, u) := by
  set q := (L₁.acceptCoordinates h₁).symm (a, b, u) with hq
  have hval : L₁.acceptCoordinates h₁ q = (a, b, u) := by
    rw [hq, Equiv.apply_symm_apply]
  have hq2 : L₂.acceptCoordinates h₂ q = (a, b, residual e u) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine eq_of_heq
        (((L₂.acceptCoordinates_fst_heq_coordinates_fst h₂ q).trans (hAlice e q)).trans ?_)
      exact ((L₁.acceptCoordinates_fst_heq_coordinates_fst h₁ q).symm).trans
        (heq_of_eq (congrArg (fun z => z.1) hval))
    · refine eq_of_heq
        (((L₂.acceptCoordinates_snd_fst_heq_coordinates_snd_fst h₂ q).trans
          (hBob e q)).trans ?_)
      exact ((L₁.acceptCoordinates_snd_fst_heq_coordinates_snd_fst h₁ q).symm).trans
        (heq_of_eq (congrArg (fun z => z.2.1) hval))
    · rw [L₂.acceptCoordinates_snd_snd h₂ q, hRes e q,
        ← L₁.acceptCoordinates_snd_snd h₁ q, hval]
  rw [← hq2, Equiv.symm_apply_apply]

/-- The boundary-derived ideal resource is a channel on the natural boundary register. -/
theorem isChannel_ideal : Quantum.Channels.IsChannel L.ideal :=
  L.idealInstrument.isChannel_channel

end BoundaryKeyLayout
end LOCC
