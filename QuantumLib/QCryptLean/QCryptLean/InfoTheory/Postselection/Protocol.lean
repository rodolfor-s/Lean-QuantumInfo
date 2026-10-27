import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Paired

/-! # Protocol -/


noncomputable section

universe u v w x y z r

namespace InfoTheory.Postselection

open Quantum.Operators Quantum.Channels Quantum.Metrics

/-- Real and ideal protocol families sharing output registers and an accept map. -/
structure PMQKDProtocol (A : Type u) (B : Type v) (K : Type w) (C : Type x)
    (CE : Type y) (CP : Type z) (Raw : Type r)
    [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP] (k : ℕ) where
  /-- The base privacy-amplification length in bits. -/
  l : ℕ
  /-- The real maps for the supported hash lengths. -/
  variantReal : ℕ → Operation ((Fin k → A) × (Fin k → B)) (K × ((C × CE) × CP))
  /-- The ideal maps on the same output register. -/
  variantIdeal : ℕ → Operation ((Fin k → A) × (Fin k → B)) (K × ((C × CE) × CP))
  /-- Every real variant is a channel. -/
  variantReal_isChannel : ∀ l', IsChannel (variantReal l')
  /-- Every ideal variant is a channel. -/
  variantIdeal_isChannel : ∀ l', IsChannel (variantIdeal l')
  /-- The accepted-output projection as a linear operation. -/
  acceptProj : Operation (K × ((C × CE) × CP)) (K × ((C × CE) × CP))
  /-- Repeated acceptance projection has no additional effect. -/
  acceptProj_idem : acceptProj.comp acceptProj = acceptProj
  /-- The real and ideal variants agree on the abort branch. -/
  abortAgreement : ∀ l', (LinearMap.id - acceptProj).comp (variantReal l' - variantIdeal l') = 0

variable {A : Type u} {B : Type v} {K : Type w} {C : Type x} {CE : Type y} {CP : Type z}
  {Raw : Type r} [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  {k : ℕ}

/-- The base real map at the stored hash length. -/
def PMQKDProtocol.realMap (P : PMQKDProtocol A B K C CE CP Raw k) := P.variantReal P.l

/-- The base ideal map at the stored hash length. -/
def PMQKDProtocol.idealMap (P : PMQKDProtocol A B K C CE CP Raw k) := P.variantIdeal P.l

/-- The real-minus-ideal operation at a specified hash length. -/
def PMQKDProtocol.differenceMap (P : PMQKDProtocol A B K C CE CP Raw k) (l' : ℕ) :=
  P.variantReal l' - P.variantIdeal l'

/-- The protocol difference with its input written as a function of paired rounds. -/
def PMQKDProtocol.roundDifferenceMap (P : PMQKDProtocol A B K C CE CP Raw k) (l' : ℕ) :
    Operation (Fin k → A × B) (K × ((C × CE) × CP)) :=
  (P.differenceMap l').comp
    (Matrix.reindexLinearEquiv ℂ ℂ (Quantum.Symmetry.pairFunctions A B k)
      (Quantum.Symmetry.pairFunctions A B k)).toLinearMap

/-- Single-round bipartite density states with a prescribed Alice marginal. -/
def fixedMarginalSet (σA : DensityOp A) : Set (DensityOp (A × B)) :=
  {σ | σ.partialTraceRight = σA}

/-- The difference is supported on the accepted branch. -/
theorem PMQKDProtocol.acceptProj_comp_differenceMap
    (P : PMQKDProtocol A B K C CE CP Raw k) (l' : ℕ) :
    P.acceptProj.comp (P.differenceMap l') = P.differenceMap l' := by
  have h := P.abortAgreement l'
  rw [LinearMap.sub_comp, LinearMap.id_comp] at h
  exact (sub_eq_zero.mp h).symm

/-- Fixed-marginal secrecy tests every finite nonempty Eve register and normalized input. -/
def IsFixedMarginalSecret.{s} {O : Type*} [Fintype O]
    (Δ : Operation ((Fin k → A) × (Fin k → B)) O) (σA : DensityOp A) (ε : ℝ) : Prop :=
  ∀ (E : Type s) [Fintype E] [Nonempty E]
    (ρ : DensityOp (((Fin k → A) × (Fin k → B)) × E)),
    Matrix.partialTraceRight (Matrix.partialTraceRight ρ.toOp) = (σA.tensorPow k).toOp →
      (1 / 2 : ℝ) * traceNorm (mapTensorId Δ E ρ.toOp) ≤ ε

/-- Fixed-marginal secrecy of a protocol's specified hash-length variant. -/
def PMQKDProtocol.IsSecretAt.{s} (P : PMQKDProtocol A B K C CE CP Raw k)
    (l' : ℕ) (σA : DensityOp A) (ε : ℝ) : Prop :=
  IsFixedMarginalSecret.{_, _, s} (P.differenceMap l') σA ε

universe s

/-- Enlarging a secrecy budget preserves the fixed-marginal guarantee. -/
theorem IsFixedMarginalSecret.mono {O : Type*} [Fintype O]
    {Δ : Operation ((Fin k → A) × (Fin k → B)) O} {σA : DensityOp A} {ε δ : ℝ}
    (h : IsFixedMarginalSecret.{_, _, s} Δ σA ε) (hεδ : ε ≤ δ) :
    IsFixedMarginalSecret.{_, _, s} Δ σA δ :=
  fun E _ _ ρ hρ => (h E ρ hρ).trans hεδ

/-- A zero difference is secret with zero error, for every allowed marginal. -/
theorem isFixedMarginalSecret_zero {O : Type*} [Fintype O] (σA : DensityOp A) :
    IsFixedMarginalSecret.{_, _, s}
      (0 : Operation ((Fin k → A) × (Fin k → B)) O) σA 0 := by
  intro E _ _ ρ _
  change (1 / 2 : ℝ) * traceNorm (0 : Op (O × E)) ≤ 0
  rw [traceNorm_zero, mul_zero]

end InfoTheory.Postselection
