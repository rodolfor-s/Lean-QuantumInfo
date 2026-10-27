import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement
import QCryptLean.InfoTheory.SmoothMinEntropy.AnnouncementBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Penalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-!
# BB84 syndrome and verification announcements

The protocol announcement kernel combines the error-correction syndrome with a uniformly
seeded verification tag. Its domination bound charges the announced bit lengths to smooth
min-entropy. Generic uniformly seeded kernels are in
`InfoTheory/SmoothMinEntropy/Announcement/UniformSeed.lean`.
-/

open Quantum.Operators InfoTheory.SmoothMinEntropy Matrix
open QKD.BB84.Measurement
open scoped ComplexOrder Kronecker

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The public syndrome, uniform verification seed and its tag, on their actual value types. -/
def announceKernel {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    SubDensityOp (Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) :=
  (uniformSeededAnnounce (fun t : KeyHashSeed n ℓEV peSel =>
    (ec.syndrome x, verificationTag n ℓEV peSel t x))).reindex ((Equiv.prodAssoc _ _ _).symm.trans
      (((Equiv.prodComm _ _).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)))

/-- Every secret value gives a normalized public announcement. -/
lemma announceKernel_trace {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    (announceKernel ℓEV peSel ec x).trace = 1 := by
  unfold announceKernel SubDensityOp.trace SubDensityOp.reindex
  rw [reindex_trace]
  exact uniformSeededAnnounce_trace _

/-- The public seed costs no entropy; only the syndrome and tag cardinalities are charged. -/
lemma opLe_announceKernel_smul_maxMixed {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    OpLe (announceKernel ℓEV peSel ec x).toOp
      (Complex.ofReal ((2 : ℝ) ^ (leakEC + ℓEV)) •
        (DensityOp.maxMixed (X := Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV))).toOp) := by
  let g := fun t : KeyHashSeed n ℓEV peSel =>
    (ec.syndrome x, verificationTag n ℓEV peSel t x)
  have h := (opLe_reindex_iff ((Equiv.prodAssoc _ _ _).symm.trans
    (((Equiv.prodComm _ _).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))) _ _).mpr
      (opLe_uniformSeededAnnounce_smul_maxMixed g)
  have hc : (Fintype.card (Bits leakEC × Bits ℓEV) : ℂ) =
      Complex.ofReal ((2 : ℝ) ^ (leakEC + ℓEV)) := by
    simp [Bits, Fintype.card_prod, pow_add]
  rw [hc] at h
  convert h using 1
  · rfl
  · simp only [DensityOp.maxMixed, reindex_apply, submatrix_smul, Pi.smul_apply,
      submatrix_one_equiv, Fintype.card_prod, mul_left_comm]

/-- The exact classical announcement charge at the original smoothing radius. -/
theorem smoothMinEntropy_le_announce_add_leak
    {n leakEC : ℕ} {E : Type*} [Fintype E]
    (ℓEV : ℕ) (peSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (ε : ℝ)
    (ρ : CQState (KeyBitString n peSel) E) (σ : SubDensityOp E) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.tensorLeftKernel (announceKernel ℓEV peSel ec))
        (((DensityOp.maxMixed (X :=
          Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV))).toSubDensityOp).kronecker σ) +
        ENNReal.ofReal ((leakEC : ℝ) + (ℓEV : ℝ)) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hcharge : Real.log ((2 : ℝ) ^ (leakEC + ℓEV)) / Real.log 2 =
      (leakEC : ℝ) + (ℓEV : ℝ) := by
    rw [Real.log_pow]
    push_cast
    field_simp
  have hc : (1 : ℝ) ≤ (2 : ℝ) ^ (leakEC + ℓEV) := one_le_pow₀ one_le_two
  have h := smoothMinEntropy_le_tensorLeftKernel_add ε ρ σ
    (announceKernel ℓEV peSel ec) hc (announceKernel_trace ℓEV peSel ec)
    (opLe_announceKernel_smul_maxMixed ℓEV peSel ec)
  rwa [hcharge] at h

end QKD.BB84.FiniteKey
