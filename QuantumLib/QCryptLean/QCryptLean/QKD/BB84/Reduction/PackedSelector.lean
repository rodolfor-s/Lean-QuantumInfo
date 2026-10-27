import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRotationFactorization
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SelectionData

/-! # Packed Selector -/


noncomputable section

namespace QKD.BB84.Reduction

open QKD.BB84.FiniteKey

/-- The packed Z-key/Z-test/X-test mask has exactly the required parametric key count.

This is the finite threshold count for the explicit packed selector; no equality between the Z
and X test quotas is assumed. -/
theorem packedPESel_keyCount (nK mZ mX : ℕ) :
    QKD.BB84.FiniteKey.KeyCount
      (nK + mZ + mX) (mZ + mX)
      (@Sampling.packedPESel nK mZ mX) := by
  change Fintype.card {i : Fin (nK + mZ + mX) // Sampling.packedPESel i = false} = _
  rw [Sampling.card_packedPESel_eq_false]
  simp only [keyRounds]
  omega

/-- On the configured key/Z-test/X-test layout, the test position is the key-prefix offset. -/
theorem peRoundIdx_packed (nK mZ mX : ℕ)
    (j : Fin (min (nK + mZ + mX) (mZ + mX))) :
    peRoundIdx (@Sampling.packedPESel nK mZ mX) j =
      ⟨nK + j, by have := j.isLt; omega⟩ := by
  have hmono : Monotone (@Sampling.packedPESel nK mZ mX) := by
    intro i k hik
    by_cases hi : nK ≤ i.val
    · have hk : nK ≤ k.val := hi.trans hik
      simp [Sampling.packedPESel, hi, hk]
    · simp [Sampling.packedPESel, hi]
  rw [peRoundIdx_of_monotone _ hmono]
  apply Fin.ext
  simp only [keyRounds]
  omega

/-- The Z-test block of the packed selector has cardinality `mZ`. -/
theorem siftedZTestSampleSize_packed (nK mZ mX : ℕ) :
    siftedZTestSampleSize
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) = mZ := by
  classical
  let e : Fin mZ ≃
      {i : Fin (nK + mZ + mX) //
        Sampling.packedPESel i = true ∧ Sampling.packedXSel i = false} := {
    toFun z := ⟨⟨nK + z.val, by omega⟩, by
      simp [Sampling.packedPESel, Sampling.packedXSel]
      ⟩
    invFun i := ⟨i.1.val - nK, by
      have hlo : nK ≤ i.1.val := by
        simpa [Sampling.packedPESel] using i.2.1
      have hhi : ¬nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      omega⟩
    left_inv z := by
      apply Fin.ext
      simp
    right_inv i := by
      apply Subtype.ext
      apply Fin.ext
      have hlo : nK ≤ i.1.val := by
        simpa [Sampling.packedPESel] using i.2.1
      simp
      omega }
  unfold siftedZTestSampleSize
  rw [← Fintype.card_subtype]
  calc
    _ = Fintype.card (Fin mZ) := Fintype.card_congr e.symm
    _ = mZ := Fintype.card_fin mZ

/-- The X-test block of the packed selector has cardinality `mX`. -/
theorem siftedXTestSampleSize_packed (nK mZ mX : ℕ) :
    siftedXTestSampleSize
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) = mX := by
  classical
  let e : Fin mX ≃
      {i : Fin (nK + mZ + mX) //
        Sampling.packedPESel i = true ∧ Sampling.packedXSel i = true} := {
    toFun x := ⟨⟨nK + mZ + x.val, by omega⟩, by
      simp [Sampling.packedPESel, Sampling.packedXSel]
      omega⟩
    invFun i := ⟨i.1.val - (nK + mZ), by
      have hlo : nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      omega⟩
    left_inv x := by
      apply Fin.ext
      simp
    right_inv i := by
      apply Subtype.ext
      apply Fin.ext
      have hlo : nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      simp
      omega }
  unfold siftedXTestSampleSize
  rw [← Fintype.card_subtype]
  calc
    _ = Fintype.card (Fin mX) := Fintype.card_congr e.symm
    _ = mX := Fintype.card_fin mX

end QKD.BB84.Reduction
