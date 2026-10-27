import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReference
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CKRConsequences
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.RankPurificationBounds
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # A small purifier for the joint Bell reference

The auxiliary register is a finite type bounded by the number of Bell occupation
types. Reassociating the joint extension exposes the whole signal-word reference
and this small register, with no dimension casts or reference numbering.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open QKD.BB84.Measurement Math.Combinatorics Matrix

/-- A pure extension of a prescribed joint marginal with a Bell-sized auxiliary register. -/
structure BellPurifierOfMarginal (n : ℕ) (ρ₀ : DensityOp (Signals n × Signals n)) where
  /-- The finite auxiliary register. -/
  reg : Type
  /-- The auxiliary register's finite basis. -/
  [fintypeReg : Fintype reg]
  /-- The pure extension of the joint marginal. -/
  purifier : DensityOp ((Signals n × Signals n) × reg)
  /-- Purity of the extension. -/
  purifier_isPure : purifier.IsPure
  /-- Discarding only the auxiliary register returns the joint marginal. -/
  purifier_partialTraceRight : purifier.partialTraceRight = ρ₀
  /-- The auxiliary register costs at most the Bell symmetric dimension. -/
  card_reg_le_bellSymmetricDim : Fintype.card reg ≤ bellSymmetricDim n

attribute [instance] BellPurifierOfMarginal.fintypeReg

/-- The small purifier at the type-coherent Bell de Finetti joint state. -/
abbrev BellSymmetricPurifier (n : ℕ) : Type 1 :=
  let e := Equiv.piCongrRight fun _ : Fin n => finTwoEquiv.symm.prodCongr finTwoEquiv.symm
  BellPurifierOfMarginal n ((bellPairedDeFinettiState n).reindex (e.prodCongr e))

/-- Expose the reference as the signal-word register paired with the small auxiliary type. -/
def enVBellPurification {n : ℕ} {ρ₀ : DensityOp (Signals n × Signals n)}
    (V : BellPurifierOfMarginal n ρ₀) : DensityOp (Signals n × (Signals n × V.reg)) :=
  V.purifier.reindex (Equiv.prodAssoc _ _ _)

/-- Structural reassociation preserves the Bell extension's purity. -/
theorem isPure_enVBellPurification {n : ℕ} {ρ₀ : DensityOp (Signals n × Signals n)}
    (V : BellPurifierOfMarginal n ρ₀) : (enVBellPurification V).IsPure :=
  V.purifier_isPure.reindex _

/-- Discarding the combined reference equals the iterated marginal. -/
theorem enVBellPurification_partialTraceRight {n : ℕ}
    {ρ₀ : DensityOp (Signals n × Signals n)} (V : BellPurifierOfMarginal n ρ₀) :
    (enVBellPurification V).partialTraceRight = ρ₀.partialTraceRight := by
  apply DensityOp.ext
  change partialTraceRight (Matrix.reindex (Equiv.prodAssoc _ _ _)
    (Equiv.prodAssoc _ _ _) V.purifier.toOp) = _
  rw [← partialTraceRight_partialTraceRight]
  change partialTraceRight V.purifier.partialTraceRight.toOp = _
  rw [V.purifier_partialTraceRight]
  rfl

/-- The small-reference extension purifies the same Bell marginal as the canonical one. -/
theorem isPurification_enVBellPurification {n : ℕ} (V : BellSymmetricPurifier n) :
    IsBellCKRDeFinettiPurification (enVBellPurification V) := by
  refine ⟨isPure_enVBellPurification V, ?_⟩
  rw [enVBellPurification_partialTraceRight]
  apply DensityOp.ext
  change partialTraceRight (Matrix.reindex _ _ (bellPairedDeFinettiState n).toOp) = _
  rw [partialTraceRight_reindex]
  change Matrix.reindex _ _ (bellPairedDeFinettiState n).partialTraceRight.toOp = _
  rw [bellPairedDeFinettiState_partialTraceRight]
  rfl

/-- Bell occupation types supply a reference of exactly the allowed polynomial size. -/
theorem nonempty_bellSymmetricPurifier (n : ℕ) : Nonempty (BellSymmetricPurifier n) := by
  classical
  let R := Sym (Fin 4) n
  let e := Equiv.piCongrRight fun _ : Fin n => finTwoEquiv.symm.prodCongr finTwoEquiv.symm
  let ρ := (bellPairedDeFinettiState n).reindex (e.prodCongr e)
  have hc : Fintype.card R = bellSymmetricDim n := by
    rw [Sym.card_sym_eq_choose, Fintype.card_fin,
      show 4 + n - 1 = n + 3 from by omega]
    have h := Nat.choose_symm (by omega : 3 ≤ n + 3)
    simpa [bellSymmetricDim] using h
  have hr : ρ.toOp.rank ≤ Fintype.card R := by
    change (Matrix.reindex (e.prodCongr e) (e.prodCongr e)
      (bellPairedDeFinettiState n).toOp).rank ≤ _
    rw [Matrix.rank_reindex, hc]
    exact rank_bellPairedDeFinettiState_le n
  obtain ⟨ψ, hψ, hm⟩ := ρ.exists_isPure_partialTraceRight_eq_of_rank_le hr
  exact ⟨{
    reg := R
    fintypeReg := inferInstance
    purifier := ψ
    purifier_isPure := hψ
    purifier_partialTraceRight := hm
    card_reg_le_bellSymmetricDim := hc.le }⟩

/-- The amplified trace norm depends only on the shared Bell marginal, not its purifier. -/
theorem Bell.ckrTraceNorm_canonical_eq_enV {n : ℕ} {Y : Type*} [Fintype Y]
    (V : BellSymmetricPurifier n) (Δ : Operation (Signals n) Y) :
    ckrTraceNorm Δ (bellCKRDeFinettiPurification n) =
      ckrTraceNorm Δ (enVBellPurification V) :=
  tensorTraceNorm_eq_of_shared_marginal Δ _ _ _
    (isPurification_bellCKRDeFinettiPurification n).isPure
    (isPurification_enVBellPurification V).isPure
    (isPurification_bellCKRDeFinettiPurification n).marginal
    (isPurification_enVBellPurification V).marginal

end QKD.BB84.FiniteKey
