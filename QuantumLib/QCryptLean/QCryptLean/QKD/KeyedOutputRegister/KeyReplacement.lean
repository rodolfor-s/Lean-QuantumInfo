import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.QKD.KeyedOutputRegister.FlagBlocks
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic

/-!
# Shared-key replacement on a flagged output register

On acceptance, this channel discards both keys and writes one fresh uniform key
into both registers. On abort, it preserves every key and retained-register
coherence. The output domain remains the complete padded product register.
-/

open Quantum.Operators Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace QKD

variable (ℓ : ℕ) (D : Type*) [Fintype D] [DecidableEq D]

/-! ## 4. `keyReplace`: the ideal is a functor of the register layout, never of the program -/

/-- The Kraus operator of the accept branch of `keyReplace`, in the branch `(k, a, b)`: it reads
both key registers out (`⟨a|`, `⟨b|`) and writes the *same* fresh value `k` into both, inside the
accept block. The `√` is exactly what normalises the `2^ℓ` fresh-key branches. -/
def freshKeyKraus (k a b : Fin ℓ → Fin 2) : Op (KeyedOutput ℓ D) :=
  (((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℝ) : ℂ) •
    ((((Matrix.single k a (1 : ℂ)) ⊗ₖ (Matrix.single k b (1 : ℂ)))) ⊗ₖ (acceptFlagOp D))

/-- The accept part of `keyReplace`: discard both key registers and write one fresh uniform key into
both, inside the accept block. -/
def keyReplaceAccept :
    Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D) :=
  ∑ p : (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2),
    Matrix.conjLinearMap (freshKeyKraus ℓ D p.1 p.2.1 p.2.2)

/-- The accept event as a superoperator, `ρ ↦ P ρ P`. -/
def acceptSandwich :
    Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D) :=
  Matrix.conjLinearMap (acceptProjOp ℓ D)

/-- The abort event as a superoperator. -/
def abortSandwich :
    Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D) :=
  Matrix.conjLinearMap (abortProjOp ℓ D)

/-- **The key-replacement functor.** A fixed function of `(ℓ, D)` — the register layout — and
of **nothing else**: it never sees the program, so it cannot be tuned to make a particular protocol
look secure. On the accept block it discards both key registers and writes one fresh uniform key
into both; on the abort block it is the identity. Composing it after the real channel defines the
derived fixed-output ideal channel. -/
def keyReplace :
    Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D) :=
  keyReplaceAccept ℓ D + abortSandwich ℓ D

/-- Key replacement is the sum of the fresh-key and abort operations. -/
theorem keyReplace_eq_accept_add_abort :
    keyReplace ℓ D = keyReplaceAccept ℓ D + abortSandwich ℓ D := rfl

/-! ### The flag algebra of the two events -/

/-- Applying the acceptance event twice is the same as applying it once. -/
theorem acceptSandwich_acceptSandwich (ρ : Op (KeyedOutput ℓ D)) :
    acceptSandwich ℓ D (acceptSandwich ℓ D ρ) = acceptSandwich ℓ D ρ := by
  simp only [acceptSandwich, Matrix.conjLinearMap_apply]
  rw [← Matrix.conjLinearMap_apply, ← Matrix.conjLinearMap_apply,
    ← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul, Matrix.conjLinearMap_apply,
    acceptProjOp_mul_self]
  rfl

/-- The acceptance event is an idempotent linear map. -/
theorem acceptSandwich_idem :
    (acceptSandwich ℓ D).comp (acceptSandwich ℓ D) = acceptSandwich ℓ D :=
  LinearMap.ext fun ρ => acceptSandwich_acceptSandwich ℓ D ρ

/-- The acceptance event annihilates the abort block. -/
theorem acceptSandwich_abortSandwich (ρ : Op (KeyedOutput ℓ D)) :
    acceptSandwich ℓ D (abortSandwich ℓ D ρ) = 0 := by
  simp only [acceptSandwich, abortSandwich, Matrix.conjLinearMap_apply]
  rw [← Matrix.conjLinearMap_apply, ← Matrix.conjLinearMap_apply,
    ← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul, Matrix.conjLinearMap_apply,
    acceptProjOp_mul_abortProjOp,
    Matrix.zero_mul, Matrix.zero_mul]

/-- Composing acceptance after abort gives the zero operation. -/
theorem acceptSandwich_comp_abortSandwich :
    (acceptSandwich ℓ D).comp (abortSandwich ℓ D) = 0 :=
  LinearMap.ext fun ρ => acceptSandwich_abortSandwich ℓ D ρ

/-- **The accept projector on a diagonal matrix unit** keeps the unit when the flag is `true`
and kills it otherwise.  This is the whole content of "the accept block of a diagonally supported
channel is the sub-sum over its accepting branches", and it is a fact about the flagged register
alone: no program, no protocol and no index layout occurs. -/
theorem acceptSandwich_single (i : KeyedOutput ℓ D) (c : ℂ) :
    acceptSandwich ℓ D (Matrix.single i i c) =
      (if i.2.1 = true then (1 : ℂ) else 0) • Matrix.single i i c := by
  rw [acceptSandwich, Matrix.conjLinearMap_apply, acceptProjOp_conjTranspose,
    acceptProjOp_eq_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne p i with rfl | hp
  · rcases eq_or_ne q p with rfl | hq
    · by_cases h : q.2.1 = true <;> simp [h]
    · simp [Ne.symm hq]
  · simp [Ne.symm hp]

/-- The abort counterpart of `QKD.acceptSandwich_single`. -/
theorem abortSandwich_single (i : KeyedOutput ℓ D) (c : ℂ) :
    abortSandwich ℓ D (Matrix.single i i c) =
      (if i.2.1 = false then (1 : ℂ) else 0) • Matrix.single i i c := by
  rw [abortSandwich, Matrix.conjLinearMap_apply, abortProjOp_conjTranspose,
    abortProjOp_eq_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne p i with rfl | hp
  · rcases eq_or_ne q p with rfl | hq
    · by_cases h : q.2.1 = false <;> simp [h]
    · simp [Ne.symm hq]
  · simp [Ne.symm hp]

/-- Applying the abort event twice is the same as applying it once. -/
theorem abortSandwich_abortSandwich (ρ : Op (KeyedOutput ℓ D)) :
    abortSandwich ℓ D (abortSandwich ℓ D ρ) = abortSandwich ℓ D ρ := by
  simp only [abortSandwich, Matrix.conjLinearMap_apply]
  rw [← Matrix.conjLinearMap_apply, ← Matrix.conjLinearMap_apply,
    ← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul, Matrix.conjLinearMap_apply,
    abortProjOp_mul_self]
  rfl

/-! ### `keyReplace` against the flag blocks -/

/-- Fresh-key Kraus matrices have range in the acceptance sector. -/
theorem acceptProjOp_mul_freshKeyKraus (k a b : Fin ℓ → Fin 2) :
    acceptProjOp ℓ D * freshKeyKraus ℓ D k a b = freshKeyKraus ℓ D k a b := by
  rw [freshKeyKraus, acceptProjOp, Matrix.mul_smul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    acceptFlagOp_mul_self]

/-- Fresh-key Kraus matrices vanish on the abort sector. -/
theorem freshKeyKraus_mul_abortProjOp (k a b : Fin ℓ → Fin 2) :
    freshKeyKraus ℓ D k a b * abortProjOp ℓ D = 0 := by
  rw [freshKeyKraus, abortProjOp, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    acceptFlagOp_mul_abortFlagOp, Matrix.kronecker_zero, smul_zero]

/-- **The accept event fixes the fresh-key part of `keyReplace`.** -/
theorem acceptSandwich_keyReplaceAccept (ρ : Op (KeyedOutput ℓ D)) :
    acceptSandwich ℓ D (keyReplaceAccept ℓ D ρ) = keyReplaceAccept ℓ D ρ := by
  simp only [acceptSandwich, keyReplaceAccept, LinearMap.sum_apply, Matrix.conjLinearMap_apply]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Matrix.conjLinearMap_apply, ← Matrix.conjLinearMap_apply,
    ← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul, Matrix.conjLinearMap_apply,
    acceptProjOp_mul_freshKeyKraus]
  rfl

/-- The fresh-key operation has range in the acceptance sector. -/
theorem acceptSandwich_comp_keyReplaceAccept :
    (acceptSandwich ℓ D).comp (keyReplaceAccept ℓ D) = keyReplaceAccept ℓ D :=
  LinearMap.ext fun ρ => acceptSandwich_keyReplaceAccept ℓ D ρ

/-- **`keyReplace` is the identity on the abort block** — the half of the design that makes the
abort-agreement theorem work. -/
theorem keyReplace_abort (ρ : Op (KeyedOutput ℓ D)) :
    keyReplace ℓ D (abortSandwich ℓ D ρ) = abortSandwich ℓ D ρ := by
  rw [keyReplace, LinearMap.add_apply, abortSandwich_abortSandwich]
  rw [show keyReplaceAccept ℓ D (abortSandwich ℓ D ρ) = 0 from ?_, zero_add]
  simp only [keyReplaceAccept, abortSandwich, LinearMap.sum_apply, Matrix.conjLinearMap_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Matrix.conjLinearMap_apply, ← Matrix.conjLinearMap_apply,
    ← LinearMap.comp_apply, ← Matrix.conjLinearMap_mul, Matrix.conjLinearMap_apply,
    freshKeyKraus_mul_abortProjOp,
    Matrix.zero_mul, Matrix.zero_mul]

/-! ### `keyReplace` is a channel -/

/-- The Gram matrix of one fresh-key branch reads the two old keys. -/
theorem freshKeyKraus_conjTranspose_mul_self (k a b : Fin ℓ → Fin 2) :
    (freshKeyKraus ℓ D k a b)ᴴ * freshKeyKraus ℓ D k a b
      = ((((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : ℂ) •
          (Matrix.single a a (1 : ℂ) ⊗ₖ Matrix.single b b (1 : ℂ)) ⊗ₖ acceptFlagOp D := by
  rw [freshKeyKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  · rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity)]
  · rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul,
      acceptFlagOp_conjTranspose, acceptFlagOp_mul_self]

/-- The fresh-key completeness sum equals the acceptance projector. -/
theorem sum_freshKeyKraus_conjTranspose_mul_self :
    ∑ p : (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2),
        (freshKeyKraus ℓ D p.1 p.2.1 p.2.2)ᴴ * freshKeyKraus ℓ D p.1 p.2.1 p.2.2
      = acceptProjOp ℓ D := by
  have hab : ∑ a : (Fin ℓ → Fin 2), ∑ b : (Fin ℓ → Fin 2),
      (Matrix.single a a (1 : ℂ) ⊗ₖ Matrix.single b b (1 : ℂ)) ⊗ₖ acceptFlagOp D =
        acceptProjOp ℓ D := by
    ext i j
    simp [acceptProjOp, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.single_apply,
      Matrix.one_apply, Prod.ext_iff, ite_and]
    split_ifs <;> rfl
  simp_rw [freshKeyKraus_conjTranspose_mul_self]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, ← Finset.smul_sum]
  simp_rw [hab]
  have hscal : ∀ z : ℂ, z = 1 → z • acceptProjOp ℓ D = acceptProjOp ℓ D := by
    intro z hz; rw [hz, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  refine hscal _ ?_
  push_cast
  field_simp
  simp

/-- The Kraus family of `keyReplace`: one branch per fresh key and read-out pair, plus the abort
projector. -/
def keyReplaceKraus (o : Option ((Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2))) :
    Op (KeyedOutput ℓ D) :=
  match o with
  | none => abortProjOp ℓ D
  | some p => freshKeyKraus ℓ D p.1 p.2.1 p.2.2

omit [Fintype D] in
/-- The absent replacement branch preserves the full abort block. -/
@[simp] theorem keyReplaceKraus_none :
    keyReplaceKraus ℓ D none = abortProjOp ℓ D := rfl

omit [Fintype D] in
/-- A present replacement branch prepares its fresh shared key. -/
@[simp] theorem keyReplaceKraus_some (p : (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2)) :
    keyReplaceKraus ℓ D (some p) = freshKeyKraus ℓ D p.1 p.2.1 p.2.2 := rfl

/-- The fresh-key and abort branches form a Kraus presentation of replacement. -/
theorem keyReplace_eq_krausMap :
    keyReplace ℓ D = krausMap (keyReplaceKraus ℓ D) := by
  refine LinearMap.ext fun ρ => ?_
  change keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ
    = ∑ o : Option ((Fin ℓ → Fin 2) × (Fin ℓ → Fin 2) × (Fin ℓ → Fin 2)),
        keyReplaceKraus ℓ D o * ρ * (keyReplaceKraus ℓ D o)ᴴ
  rw [Fintype.sum_option]
  simp only [keyReplaceAccept, abortSandwich, LinearMap.sum_apply, Matrix.conjLinearMap_apply,
    keyReplaceKraus_none, keyReplaceKraus_some]
  exact add_comm _ _

/-- The key-replacement Kraus family is complete. -/
theorem keyReplaceKraus_complete :
    ∑ o, (keyReplaceKraus ℓ D o)ᴴ * keyReplaceKraus ℓ D o = 1 := by
  rw [Fintype.sum_option]
  simp only [keyReplaceKraus_none, keyReplaceKraus_some]
  rw [abortProjOp_conjTranspose, abortProjOp_mul_self, sum_freshKeyKraus_conjTranspose_mul_self,
    add_comm,
    acceptProjOp_add_abortProjOp]

/-- `keyReplace` is a channel for every finite retained register.
The `√` in `freshKeyKraus` makes the `2^ℓ`
fresh-key branches normalise: the completeness sum is `acceptProjOp`, and the abort branch supplies
`abortProjOp`. -/
theorem isChannel_keyReplace : IsChannel (keyReplace ℓ D) := by
  rw [keyReplace_eq_krausMap]
  exact ⟨isCompletelyPositive_krausMap _, fun ρ => by
    rw [trace_krausMap, keyReplaceKraus_complete, Matrix.one_mul]⟩

/-! ## 5. Accept and abort exhaust a denotation -/

/-- **Accept and abort exhaust a transcript-diagonal state.** -/
theorem acceptSandwich_add_abortSandwich_of_transcriptDiag (ρ : Op (KeyedOutput ℓ D))
    (h : TranscriptDiag ρ) :
    acceptSandwich ℓ D ρ + abortSandwich ℓ D ρ = ρ := by
  ext i j
  simp only [acceptSandwich, abortSandwich, Matrix.conjLinearMap_apply, Matrix.add_apply]
  rw [acceptProjOp_conjTranspose, abortProjOp_conjTranspose, acceptProjOp_eq_diagonal,
    abortProjOp_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_mul]
  by_cases hf : i.2.1 = j.2.1
  · cases hi : i.2.1 <;> cases hj : j.2.1 <;> simp_all
  · have hρ : ρ i j = 0 := h i j (fun hmod => hf (congrArg Prod.fst hmod))
    simp [hρ]

/-! ## 6. Abort agreement, for any transcript-diagonal channel

The two statements below are the abort half of the design, and they are about the **functor and
the output register only**: the hypothesis is that the channel's outputs are transcript-diagonal,
expressed directly as vanishing between distinct transcript blocks. Neither statement requires
a program or protocol syntax.

`keyReplace` is the identity on the whole abort block, so `Φ − keyReplace ∘ Φ` is supported in the
accept block: the real and ideal arms agree wherever the flag says abort. -/

/-- **The accept event fixes the key-replacement gap, pointwise.**  For any transcript-diagonal
output operator `ρ`, `ρ − keyReplace ρ` is its own accept block. -/
theorem acceptSandwich_sub_keyReplace_of_transcriptDiag (ρ : Op (KeyedOutput ℓ D))
    (h : TranscriptDiag ρ) :
    acceptSandwich ℓ D (ρ - keyReplace ℓ D ρ) = ρ - keyReplace ℓ D ρ := by
  have hpinch := acceptSandwich_add_abortSandwich_of_transcriptDiag ℓ D ρ h
  have hid : keyReplace ℓ D ρ = keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ := rfl
  rw [map_sub, hid, map_add, acceptSandwich_keyReplaceAccept, acceptSandwich_abortSandwich]
  calc acceptSandwich ℓ D ρ - (keyReplaceAccept ℓ D ρ + 0)
      = (acceptSandwich ℓ D ρ + abortSandwich ℓ D ρ)
          - (keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ) := by
        rw [add_zero]; abel
    _ = ρ - keyReplace ℓ D ρ := by rw [hpinch, hid]

/-- **The accept event fixes the key-replacement gap of a transcript-diagonal channel**, at the
level of maps. -/
theorem acceptSandwich_comp_sub_keyReplace_comp {S : Type*} (Φ : Op S →ₗ[ℂ] Op (KeyedOutput ℓ D))
    (h : ∀ ρ, TranscriptDiag (Φ ρ)) :
    (acceptSandwich ℓ D).comp (Φ - (keyReplace ℓ D).comp Φ) = Φ - (keyReplace ℓ D).comp Φ :=
  LinearMap.ext fun ρ => acceptSandwich_sub_keyReplace_of_transcriptDiag ℓ D (Φ ρ) (h ρ)

/-- 🚩 **Abort agreement, as a property of the output register.**  Outside the accept block a
transcript-diagonal channel and its key-replacement agree exactly.

In the protocol *schemes* the analogous statement is an assumed field
(`PMQKDProtocol.abortAgreement`).
Here it is a theorem with a hypothesis that every program discharges by construction. -/
theorem abortBranchAgreement_of_transcriptDiag {S : Type*} (Φ : Op S →ₗ[ℂ] Op (KeyedOutput ℓ D))
    (h : ∀ ρ, TranscriptDiag (Φ ρ)) :
    ((LinearMap.id : Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D)) -
        acceptSandwich ℓ D).comp (Φ - (keyReplace ℓ D).comp Φ) = 0 := by
  rw [LinearMap.sub_comp, LinearMap.id_comp, acceptSandwich_comp_sub_keyReplace_comp ℓ D Φ h,
    sub_self]

/-! ## Nonidentity -/

/-! For `[Nonempty D]` and `1 ≤ ℓ`, an accept-block off-diagonal operator witnesses nonidentity.
The following lemmas compute its image under key replacement. -/

/-- The abort projector is orthogonal to the acceptance projector. -/
theorem abortFlagOp_mul_acceptFlagOp : abortFlagOp D * acceptFlagOp D = 0 := by
  rw [acceptFlagOp, abortFlagOp, ← Matrix.mul_kronecker_mul]
  simp

/-- A fresh-key branch, applied to an accept-block operator, acts on the two key registers
independently: it reads them out and writes `k` into both. -/
theorem freshKeyKraus_conj (k a b : Fin ℓ → Fin 2) (XA XB : Op (Fin ℓ → Fin 2)) :
    freshKeyKraus ℓ D k a b * ((XA ⊗ₖ XB) ⊗ₖ acceptFlagOp D)
        * (freshKeyKraus ℓ D k a b)ᴴ
      = ((((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : ℂ) •
          ((Matrix.single k a (1 : ℂ) * XA * Matrix.single a k (1 : ℂ)) ⊗ₖ
            (Matrix.single k b (1 : ℂ) * XB * Matrix.single b k (1 : ℂ))) ⊗ₖ acceptFlagOp D := by
  rw [freshKeyKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  · rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity)]
  · rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, star_one, acceptFlagOp_conjTranspose,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul,
      acceptFlagOp_mul_self, acceptFlagOp_mul_self]

/-- For distinct key labels `u ≠ v`, key replacement annihilates the accept-block operator
with key-A factor `Matrix.single u v 1`. This holds for every retained register `D`. -/
theorem keyReplace_keyCoherence (u v : (Fin ℓ → Fin 2)) (huv : u ≠ v) :
    keyReplace ℓ D
        ((Matrix.single u v (1 : ℂ) ⊗ₖ Matrix.single u u (1 : ℂ)) ⊗ₖ acceptFlagOp D) = 0 := by
  rw [keyReplace, LinearMap.add_apply]
  have habort : abortSandwich ℓ D
      ((Matrix.single u v (1 : ℂ) ⊗ₖ Matrix.single u u (1 : ℂ)) ⊗ₖ acceptFlagOp D) = 0 := by
    simp only [abortSandwich, Matrix.conjLinearMap_apply, abortProjOp]
    rw [← Matrix.mul_kronecker_mul, abortFlagOp_mul_acceptFlagOp, Matrix.kronecker_zero,
      Matrix.zero_mul]
  have haccept : keyReplaceAccept ℓ D
      ((Matrix.single u v (1 : ℂ) ⊗ₖ Matrix.single u u (1 : ℂ)) ⊗ₖ acceptFlagOp D) = 0 := by
    simp only [keyReplaceAccept, LinearMap.sum_apply, Matrix.conjLinearMap_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [freshKeyKraus_conj,
      Matrix.single_mul_mul_single, Matrix.single_apply_of_ne (i := u) (j := v) (c := (1 : ℂ)) (i'
        := p.2.1) (j' := p.2.1)
        (fun h => huv (h.1.trans h.2.symm)),
      mul_zero, zero_mul, Matrix.single_zero,
      Matrix.zero_kronecker,
      Matrix.zero_kronecker, smul_zero]
  rw [habort, haccept, add_zero]

/-- If `[Nonempty D]` and `1 ≤ ℓ`, key replacement differs from the identity: it annihilates a
nonzero accept-block off-diagonal operator. This witness is not a density state. -/
theorem keyReplace_ne_id [Nonempty D] (hℓ : 1 ≤ ℓ) :
    keyReplace ℓ D ≠ (LinearMap.id : Op (KeyedOutput ℓ D) →ₗ[ℂ] Op (KeyedOutput ℓ D)) := by
  let u : Fin ℓ → Fin 2 := 0
  let v : Fin ℓ → Fin 2 := 1
  have huv : u ≠ v := by
    intro h
    have := congrFun h ⟨0, hℓ⟩
    norm_num [u, v] at this
  let ρ : Op (KeyedOutput ℓ D) :=
    ((((Matrix.single u v (1 : ℂ)) ⊗ₖ (Matrix.single u u (1 : ℂ)))) ⊗ₖ (acceptFlagOp D))
  have hzero : keyReplace ℓ D ρ = 0 := keyReplace_keyCoherence ℓ D u v huv
  have hne : ρ ≠ 0 := by
    intro hc
    obtain ⟨d⟩ := ‹Nonempty D›
    have hentry := congrFun (congrFun hc ((u, u), true, d)) ((v, u), true, d)
    simp [ρ, acceptFlagOp, Matrix.kroneckerMap_apply] at hentry
  intro hcon
  rw [hcon] at hzero
  exact hne hzero

end QKD

end
