import QCryptLean.InfoTheory.Postselection.InstrumentMixture
import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.HashingError
import QCryptLean.InfoTheory.SmoothMinEntropy.AcceptedMixture
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.RegisterExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Exact key-length compensation for an accepted correlated mixture -/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti Quantum.Metrics
  InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL MeasureTheory
variable {A B K C CE CP Raw E Public Seed Key R : Type*}
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] [Fintype Public] [Fintype Seed] [Fintype Key] [Fintype R]
  [Nonempty Raw] [Nonempty E] [Nonempty Seed] [Nonempty Key] [Nonempty R]
  [DecidableEq Raw] [DecidableEq Seed] [DecidableEq Key] [DecidableEq Public]
  {k l' : ℕ} {M : RawKeyMeasurement A B K C CE CP Raw E k}

/-- IID component hashing budgets survive accepted mixing and the correlated-register penalty. -/
theorem MeasureThenHash.extended_hashing_bound (H : MeasureThenHash M Public Seed Key l')
    (μ : DensityMeasure (A × B)) (S P : Set (DensityOp (A × B)))
    (hS : IsClosed S) (hP : IsClosed P) (hμ : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (εAT εPA εbar : ℝ) (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (hbad : ∑ x, (Matrix.of fun i j => ∫ σ in Sᶜ,
      ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure).trace.re ≤ εAT)
    (hcomp : ∀ σ ∈ S ∩ P,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (ρ : CQState Raw (E × R)) (hρ : ρ.partialTraceRight = H.acceptMixture μ)
    (hl : (l' : ℝ) ≤ (M.toProtocol.l : ℝ) - 2 * Real.logb 2 (Fintype.card R : ℝ)) :
    traceDistanceGen (InfoTheory.QuantumLHL.SeedKey.output H.hash ρ).toJointDensity.toOp
      (uniformCQState (C := Seed × Key) ρ.quantumMarginal).toJointDensity.toOp ≤
        εPA + 2 * (εbar + Real.sqrt (2 * εAT)) := by
  classical
  let F (σ : (S ∩ P : Set (DensityOp (A × B)))) := smoothMinEntropy εbar (M.rawKeyCQ σ.1) M.sigmaE
  let V := ⨅ σ, F σ
  have hfloor : V ≤ smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) (H.acceptMixture μ)
      M.sigmaE := by
    apply smoothMinEntropy_acceptedMixture_floor μ (H.acceptMixture μ) M.rawKeyCQ M.sigmaE
      (fun x i j => congrArg (fun D : Op E => D i j) (H.acceptMixture_block_integral μ x))
      H.continuous_rawKeyCQ S P hS hP hμ hεbar hbad
    intro σ hσS hσP
    exact iInf_le F ⟨σ, hσS, hσP⟩
  let σref := M.sigmaE.kronecker (DensityOp.maxMixed (X := R)).toSubDensityOp
  have hp : V ≤ smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) ρ σref +
      ENNReal.ofReal (2 * Real.logb 2 (Fintype.card R : ℝ)) := by
    rw [← hρ] at hfloor
    exact hfloor.trans (smoothMinEntropy_le_extension_add ρ M.sigmaE _)
  have he : hashingError l' (smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) ρ σref) ≤ εPA := by
    apply (hashingError_le_of_le_add M.toProtocol.l l'
      (2 * Real.logb 2 (Fintype.card R : ℝ)) V _
      (mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num)
        (by exact_mod_cast Fintype.card_pos))) hp hl).trans
    exact hashingError_iInf_le _ F hεPA (fun σ => hcomp σ.1 σ.2)
  exact (InfoTheory.QuantumLHL.SeedKey.traceDistanceGen_output_le_hashingError_add
    H.hash H.isTwoUniversal_hash ρ σref _
    (add_nonneg hεbar (Real.sqrt_nonneg _)) l' H.card_key).trans (add_le_add he le_rfl)

end InfoTheory.Postselection
