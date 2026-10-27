import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.QuantumLHL.HashOperation
import QCryptLean.InfoTheory.SmoothMinEntropy.Instrument
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.DensityExt
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Native instrument factorization of the protocol difference -/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open scoped Kronecker
variable {A B K C CE CP Raw E Public Seed Key R : Type*}
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] [Fintype Public] [Fintype Seed] [Fintype Key] [Fintype R]
  [Nonempty Seed] [Nonempty Key] [DecidableEq Seed] [DecidableEq Key] [DecidableEq Public]
  {k l' : ℕ} {M : RawKeyMeasurement A B K C CE CP Raw E k}

/-- The linear protocol difference is the isometrically encoded instrument hash difference. -/
theorem MeasureThenHash.roundDifferenceMap_eq_hashDifference_conj
    (H : MeasureThenHash M Public Seed Key l') :
    M.toProtocol.roundDifferenceMap l' =
      (krausMap (fun _ : Unit => H.encode)).comp
        (SeedKey.hashDifferenceOperation H.hash H.instrument) := by
  apply linearMap_eq_of_densityOp
  intro ρ
  let f := Quantum.Symmetry.pairFunctions A B k
  have hacc := congrArg (fun F => F (Matrix.reindex f f ρ.toOp))
    (M.toProtocol.acceptProj_comp_differenceMap l')
  change M.toProtocol.acceptProj (M.toProtocol.roundDifferenceMap l' ρ.toOp) =
    M.toProtocol.roundDifferenceMap l' ρ.toOp at hacc
  rw [← hacc]
  change M.toProtocol.acceptProj (M.toProtocol.variantReal l' _ -
    M.toProtocol.variantIdeal l' _) = _
  simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv]
  rw [map_sub, H.acceptProj_variantReal, H.acceptProj_variantIdeal]
  simp only [LinearMap.comp_apply, krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_unique]
  rw [SeedKey.hashDifferenceOperation_apply H.hash H.instrument ρ.toOp
    (CQState.ofInstrument H.instrument H.instrument_isCompletelyPositive
      H.instrument_weight_le_one ρ) (fun _ => rfl), Matrix.mul_sub, Matrix.sub_mul]

/-- Any reference extension of the protocol difference has the hash difference's trace norm. -/
theorem MeasureThenHash.traceNorm_mapTensorId_eq_hashDifference
    (H : MeasureThenHash M Public Seed Key l')
    (D : Op ((Fin k → A × B) × R)) :
    traceNorm (mapTensorId (M.toProtocol.roundDifferenceMap l') R D) =
      traceNorm (mapTensorId (SeedKey.hashDifferenceOperation H.hash H.instrument) R D) := by
  classical
  rw [H.roundDifferenceMap_eq_hashDifference_conj, mapTensorId_comp, LinearMap.comp_apply,
    mapTensorId_krausMap]
  simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_unique]
  apply traceNorm_isometry_conj
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    H.encode_isometry, Matrix.one_mul, one_kronecker_one]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end InfoTheory.Postselection
