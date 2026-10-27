import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Signal/reference blocks and the BB84 CKR dimension

Only the association of the retained Eve and reference registers remains as
register bookkeeping. No quantum register is enumerated.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Measurement Matrix

variable {E R : Type*}

/-- Select an outcome while associating Eve and the retained reference into one block. -/
def tauOutcomeEveRefEmbedding {n : ℕ} (ω : Signals n) :
    E × R → (Signals n × E) × R := fun er => ((ω, er.1), er.2)

/-- Both retained coordinates can be recovered from an outcome block. -/
lemma tauOutcomeEveRefEmbedding_injective {n : ℕ} (ω : Signals n) :
    Function.Injective (tauOutcomeEveRefEmbedding (E := E) (R := R) ω) := by
  intro a b h
  change ((ω, a.1), a.2) = ((ω, b.1), b.2) at h
  exact Prod.ext (congrArg (fun p : (Signals n × E) × R => p.1.2) h)
    (congrArg (fun p : (Signals n × E) × R => p.2) h)

variable [Fintype E] [Fintype R]

/-- Apply the pre-channel to the signal while preserving the actual reference type. -/
def tauOutputOp {n : ℕ} (E : Type*)
    (pre : Operation (Signals n) (Signals n × E)) (τ : DensityOp (Signals n × R)) :
    Op ((Signals n × E) × R) := mapTensorId pre R τ.toOp

/-- The amplified pre-channel sends normalized inputs to normalized outputs. -/
def tauOutputDensity {n : ℕ} (E : Type*) [Fintype E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (τ : DensityOp (Signals n × R)) : DensityOp ((Signals n × E) × R) :=
  (hpre.mapTensorId (Z := R)).applyDensity τ

/-- The conditioned Eve/reference blocks exhaust the ambient trace. -/
lemma tauOutcomeEveRefEmbedding_diag_sum_eq_one {n : ℕ}
    (ρ : DensityOp ((Signals n × E) × R)) :
    (∑ ω : Signals n, ∑ er : E × R,
      (ρ.toOp (tauOutcomeEveRefEmbedding ω er) (tauOutcomeEveRefEmbedding ω er)).re) = 1 := by
  have h := congrArg Complex.re ρ.trace_one
  simpa only [trace, diag, Complex.re_sum, Fintype.sum_prod_type,
    tauOutcomeEveRefEmbedding, Complex.one_re]
    using h

/-!
## The CKR polynomial dimension

`polyDim = C(n + signalDim² − 1, signalDim² − 1)` is the regularisation denominator used
throughout the CKR de Finetti reference constructions.
-/

/-- The polynomial-subspace dimension `C(n + d² − 1, d² − 1)` used as the
regularization denominator.  For `d = signalDim = 4` this equals `C(n + 15, 15)`. -/
noncomputable def ckrSymmetricDim (n : ℕ) : ℕ :=
  Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1)

/-- `ckrSymmetricDim n ≥ 1` for all `n`. -/
lemma ckrSymmetricDim_pos (n : ℕ) : 0 < ckrSymmetricDim n :=
  Nat.choose_pos (by simp [signalDim])

/-- `ckrSymmetricDim n ≥ 16` for every `n ≥ 1` (i.e. `[NeZero n]`).  Since
`ckrSymmetricDim n = C(n + 15, 15)` and `C(·, 15)` is monotone in its first argument,
`ckrSymmetricDim n ≥ C(1 + 15, 15) = C(16, 15) = 16`. -/
lemma sixteen_le_ckrSymmetricDim {n : ℕ} [NeZero n] : 16 ≤ ckrSymmetricDim n := by
  unfold ckrSymmetricDim
  have hb : signalDim ^ 2 - 1 = 15 := by decide
  rw [hb]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  calc (16 : ℕ) = Nat.choose (1 + 15) 15 := by decide
    _ ≤ Nat.choose (n + 15) 15 := Nat.choose_le_choose 15 (by omega)

end QKD.BB84.FiniteKey

end
