import QuantumLib.LOCC.Instrument.Classical
import QuantumLib.LOCC.Instrument.UniformChoice
import QuantumLib.LOCC.MultipartiteSystem
import QuantumLib.LOCC.Program.Classical
import QuantumLib.LOCC.Program.Denotation
import QuantumLib.LOCC.TwoParty
import QuantumLib.QKD.BB84.ClassicalData
import QuantumLib.QKD.BB84.ErrorCorrection
import QuantumLib.QKD.BB84.KeyHash
import QuantumLib.QKD.BB84.Program
import QuantumLib.QKD.BB84.Registers
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic

/-! # Seed Tag Syndrome -/


open Quantum.Operators (Op)

open scoped BigOperators

noncomputable section

namespace QKD.BB84
open LOCC LOCC.TwoParty FiniteKey Measurement

/-- Each announced seed, tag, and syndrome contributes its exact uniform sampling weight. -/
theorem announceSeedTagSyndrome_operation_diag
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (r : KeyHashSeedPairEV n ℓ ℓEV peSel)
    (tagSyn : Bits ℓEV × Bits leakEC)
    (rho : Op (system (Bits n) (Bits n)).total) (a b : Bits n) :
    (announceSeedTagSyndrome (B := Bits n) ℓ ℓEV ec).successorOperation (r, tagSyn) rho
        ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) =
      if tagAndSyndrome n ℓ ℓEV peSel leakEC ec r a = tagSyn then
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ *
          rho ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a, b)) else 0 := by
  refine (AnnouncedAction.successorOperation_alice_apply
    (Instrument.uniformChoice fun r =>
      Instrument.nondemolitionReadout (tagAndSyndrome n ℓ ℓEV peSel leakEC ec r))
        id (r, tagSyn) rho a a b b).trans ?_
  rw [Instrument.uniformChoice_operation]
  simp only [LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Instrument.nondemolitionReadout_operation_apply, and_self, Matrix.submatrix_apply]
  rw [mul_ite, mul_zero]

end QKD.BB84
