import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialKLChernoff
import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.Concentration.SelectedBinomialPassSum
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PEConcentration
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic

/-!
# Split-test bad-branch concentration: the per-round sift Born weight and accept mass

The local `H ⊗ H` sift on X-designated parameter-estimation rounds turns the announced two-basis
test into a fail-closed **split test**: the Z-subsample (size `m_Z`) carries the bit statistic
and the disjoint X-subsample (size `m_X`) carries the phase statistic, each earning its own
accept-mass concentration bound at the subsample rate `exp(−2·m·δ²)`.

## Main definitions

- `siftedBorn`: the per-round sift Born weight.  Every round is read in the computational
  basis; an X-designated PE round is read *after* the local `H ⊗ H`, so its weight is the
  computational diagonal of `xBasisConjugate σ`, while Z-designated PE rounds and key rounds
  carry the unrotated diagonal of `σ`.
- `componentAcceptProbability`: the accept mass of a de Finetti component `σ` —
  the total Born weight of the outcome strings that pass `siftedLocalPETestPassed`.

## Main results

- `componentAcceptProbability_le_binomialPassSum`: dropping the Z-subsample conjunct and
  marginalising
  every round the X-test does not read, the accept mass is bounded by the binomial PE-pass mass
  of `σ`'s phase marginal over the `m_X` X-test rounds.

Each arm drops the other conjunct of the two-basis test
(`Math.Concentration.SelectedBinomialPassSum.passSum_mono_of_imp`) and then marginalises the
unselected rounds
(`Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`
).
The per-round form of the marginalisation is needed because on the Z arm the unselected rounds are
of two kinds — X-PE rounds carrying the `H⊗H`-rotated Born vector and key rounds carrying the
unrotated one — so a single unselected weight vector cannot express them.

References: Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan
(2024), `arXiv:2403.11851`, Lemma 9 Eq.44; Shor–Preskill (2000) for the `Z ↔ X` duality carried by
`xBasisConjugate_bitRate_eq_phaseRate`.
-/

open Quantum.Operators Matrix Quantum.Channels
open QKD.BB84.Measurement
open Quantum.DeFinetti MeasureTheory
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## 1. The per-round V2 Born weight -/

/-- The computational diagonal of a density operator is nonnegative. -/
private lemma densityOp_diag_re_nonneg (ρ : DensityOp Signal) (k : Signal) :
    0 ≤ (ρ.toOp k k).re := by
  have h : (0 : ℂ) ≤ ρ.toOp k k :=
    ρ.posSemidef.diag_nonneg
  exact (Complex.le_def.mp h).1

/-- The computational diagonal of a density operator sums to one (`Tr ρ = 1`). -/
private lemma densityOp_diag_re_sum (ρ : DensityOp Signal) :
    (∑ k : Signal, (ρ.toOp k k).re) = 1 := by
  rw [← Complex.re_sum,
    show (∑ k : Signal, ρ.toOp k k) = (1 : ℂ) from ρ.trace_one, Complex.one_re]

/-- **The per-round sift Born weight.**

Every round is measured in the computational basis; the only rotation is the local `H ⊗ H`
applied on rounds that are both PE-designated and X-designated (`xTestPairOp`).  So
the round weight is the computational diagonal of the `H⊗H`-conjugate `xBasisConjugate σ` on
an X-test round and the computational diagonal of `σ` itself on a Z-test round or a key round.
Explicit; no `Classical.choose`. -/
def siftedBorn (peSel xSel : Bool) (σ : DensityOp Signal) (k : Signal) :
    ℝ :=
  if peSel && xSel then ((xBasisConjugate σ).toOp k k).re else (σ.toOp k k).re

/-- Each per-round sift Born weight is nonnegative. -/
theorem siftedBorn_nonneg (peSel xSel : Bool) (σ : DensityOp Signal)
    (k : Signal) : 0 ≤ siftedBorn peSel xSel σ k := by
  unfold siftedBorn
  split_ifs
  · exact densityOp_diag_re_nonneg _ k
  · exact densityOp_diag_re_nonneg _ k

/-- The per-round sift Born weights sum to one (`Tr σ = Tr (H⊗H · σ · H⊗H) = 1`). -/
theorem siftedBorn_sum (peSel xSel : Bool) (σ : DensityOp Signal) :
    (∑ k : Signal, siftedBorn peSel xSel σ k) = 1 := by
  unfold siftedBorn
  split_ifs
  · exact densityOp_diag_re_sum _
  · exact densityOp_diag_re_sum _

/-- The per-round sift Born weight is continuous in the component `σ`. -/
theorem continuous_siftedBorn (peSel xSel : Bool) (k : Signal) :
    Continuous (fun σ : DensityOp Signal => siftedBorn peSel xSel σ k) := by
  unfold siftedBorn
  have hbase : Continuous (fun ρ : DensityOp Signal => (ρ.toOp k k).re) :=
    Complex.continuous_re.comp
      ((continuous_apply k).comp ((continuous_apply k).comp continuous_induced_dom))
  split_ifs
  · exact hbase.comp continuous_xBasisConjugate
  · exact hbase

/-! ## 2. The accept mass of a de Finetti component -/

/-- **The split-test accept mass of a de Finetti component.**

`∑_{ω accepted} ∏_i siftedBorn (peSel i) (xSel i) σ (ω i)`: the per-component mass of the
outcome strings that pass the fail-closed LOCC two-basis test `siftedLocalPETestPassed`, with
each round contributing its computational Born weight after the local sift. Explicit finite sum;
no `Classical.choose`. -/
def componentAcceptProbability
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) : ℝ :=
  ∑ ω : Fin n → Signal,
    if siftedLocalPETestPassed peSel xSel δ Q ω then
      ∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i) else 0

/-- The accept mass is nonnegative. -/
theorem componentAcceptProbability_nonneg
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) :
    0 ≤ componentAcceptProbability n peSel xSel Q δ σ := by
  unfold componentAcceptProbability
  refine Finset.sum_nonneg (fun ω _ => ?_)
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => siftedBorn_nonneg (peSel i) (xSel i) σ (ω i))
  · exact le_refl 0

/-- The accept mass is at most one: dropping the accept filter, the full sum factorises over
the rounds to `∏_i (∑_k siftedBorn (peSel i) (xSel i) σ k) = ∏_i 1 = 1`. -/
theorem componentAcceptProbability_le_one
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) :
    componentAcceptProbability n peSel xSel Q δ σ ≤ 1 := by
  unfold componentAcceptProbability
  have hfull :
      (∑ ω : Fin n → Signal,
        ∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i)) = 1 := by
    rw [← Fintype.prod_sum
      (f := fun (i : Fin n) (k : Signal) => siftedBorn (peSel i) (xSel i) σ k)]
    simp_rw [siftedBorn_sum]
    simp
  calc
    (∑ ω : Fin n → Signal,
        if siftedLocalPETestPassed peSel xSel δ Q ω then
          ∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i) else 0)
        ≤ ∑ ω : Fin n → Signal,
            ∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i) := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          split_ifs
          · exact le_refl _
          · exact Finset.prod_nonneg
              (fun i _ => siftedBorn_nonneg (peSel i) (xSel i) σ (ω i))
    _ = 1 := hfull

/-- The accept mass is continuous in the component `σ`. -/
theorem continuous_componentAcceptProbability
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    Continuous (componentAcceptProbability n peSel xSel Q δ) := by
  unfold componentAcceptProbability
  refine continuous_finsetSum _ (fun ω _ => ?_)
  split_ifs
  · exact continuous_finsetProd _
      (fun i _ => continuous_siftedBorn (peSel i) (xSel i) (ω i))
  · exact continuous_const

/-! ## 3. The phase-arm accept-mass reduction

The accept mass is reduced by dropping the Z-subsample conjunct (`passSum_mono_of_imp`) and
marginalising out the rounds the X-test does not read
(`selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`). No non-degeneracy hypothesis is
needed: the test is fail-closed, so a degenerate subsample gives accept mass `0`.
-/

/-- The `{1,2}` computational-diagonal mass of `σ` is its bit-flip error rate:
`bitFlipProjector = diag(0,1,1,0)` (`bitFlipProjector_eq_matrix`), so
`Tr(Π_bit · σ) = σ₁₁ + σ₂₂`. -/
private lemma sum_diag_errorFlag_eq_bitFlipErrorRate (σ : DensityOp Signal) :
    (∑ j ∈ Finset.univ.filter (fun j : Signal => j.1 ≠ j.2), (σ.toOp j j).re) =
      QKD.BB84.Model.bitFlipErrorRate σ := by
  change (∑ j ∈ Finset.univ.filter (fun j : Signal => j.1 ≠ j.2), (σ.toOp j j).re) =
    (∑ i : Signal, ∑ j : Signal, bitFlipProjector i j * σ.toOp j i).re
  rw [bitFlipProjector_eq_matrix]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_filter]

open QKD.BB84.FiniteKey in
/-- **X-subsample domination of the accept mass.**

Dropping the Z-subsample condition and marginalising every round the X-test does not read, the
accept mass is bounded by the binomial PE-pass mass of `σ`'s **phase** marginal over the `m_X`
X-test rounds.

The phase identification is exactly the X-test soundness of the sift: an X-designated PE round is
read in the computational basis *after* the local `H ⊗ H`, so its `{1,2}` disagreement rate is
`bitFlipErrorRate (xBasisConjugate σ)`, which is `phaseFlipErrorRate σ` by
`xBasisConjugate_bitRate_eq_phaseRate`.

No `m_X ≠ 0` hypothesis: at `m_X = 0` the test is fail-closed. -/
theorem componentAcceptProbability_le_binomialPassSum {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp Signal) :
    componentAcceptProbability n peSel xSel Q δ σ ≤
      Math.Concentration.BinomialPassSum.binomialPassSum
        (siftedXTestSampleSize peSel xSel) Q δ (phaseFlipErrorRate σ) := by
  classical
  set sel : Fin n → Bool := fun i => peSel i && xSel i with hsel
  have hcard : Fintype.card {i // sel i = true} = siftedXTestSampleSize peSel xSel := by
    rw [Fintype.card_subtype]
    unfold siftedXTestSampleSize
    congr 1
    ext i
    simp [hsel]
  have hcount : ∀ ω : Fin n → Signal,
      (Finset.univ.filter
        (fun i => sel i = true ∧ (fun j : Signal => j.1 ≠ j.2) (ω i))).card =
          siftedXTestErrorCount peSel xSel ω := by
    intro ω
    unfold siftedXTestErrorCount
    congr 1
    ext i
    simp [hsel, and_assoc]
  -- On an X-test round the V2 Born weight is the computational diagonal of the `H⊗H`-conjugate.
  have hprodeq : ∀ ω : Fin n → Signal,
      (∏ i : Fin n, siftedBorn (peSel i) (xSel i) σ (ω i)) =
        ∏ i : Fin n, (if sel i then ((xBasisConjugate σ).toOp (ω i) (ω i)).re
          else siftedBorn (peSel i) (xSel i) σ (ω i)) := by
    intro ω
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : sel i = true
    · rw [ite_eq_left hi]
      have hx : (peSel i && xSel i) = true := by simpa [hsel] using hi
      simp [siftedBorn, hx]
    · rw [ite_eq_right hi]
  calc componentAcceptProbability n peSel xSel Q δ σ
         = ∑ ω : Fin n → Signal,
          if siftedLocalPETestPassed peSel xSel δ Q ω then
            ∏ i : Fin n, (if sel i then ((xBasisConjugate σ).toOp (ω i) (ω i)).re
              else siftedBorn (peSel i) (xSel i) σ (ω i)) else 0 := by
        unfold componentAcceptProbability
        exact Finset.sum_congr rfl (fun ω _ => by split_ifs with h; exacts [hprodeq ω, rfl])
    _ ≤ ∑ ω : Fin n → Signal,
          if |((Finset.univ.filter (fun i => sel i = true ∧
                  (fun j : Signal => j.1 ≠ j.2) (ω i))).card : ℝ) /
                Fintype.card {i // sel i = true} - Q| ≤ δ then
            ∏ i : Fin n, (if sel i then ((xBasisConjugate σ).toOp (ω i) (ω i)).re
              else siftedBorn (peSel i) (xSel i) σ (ω i)) else 0 := by
        refine Math.Concentration.SelectedBinomialPassSum.passSum_mono_of_imp _ _ _ ?_ ?_
        · intro ω
          refine Finset.prod_nonneg (fun i _ => ?_)
          by_cases hi : sel i = true
          · rw [ite_eq_left hi]; exact densityOp_diag_re_nonneg _ (ω i)
          · rw [ite_eq_right hi]; exact siftedBorn_nonneg (peSel i) (xSel i) σ (ω i)
        · intro ω hω
          rw [hcount ω, hcard]
          simp only [siftedLocalPETestPassed, Bool.and_eq_true, decide_eq_true_eq] at hω
          exact hω.2.2
    _ = Math.Concentration.BinomialPassSum.binomialPassSum
          (Fintype.card {i // sel i = true}) Q δ
          (∑ j ∈ Finset.univ.filter (fun j : Signal => j.1 ≠ j.2),
            ((xBasisConjugate σ).toOp j j).re) :=
   Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum_perRound
          (sel := sel) (flag := fun j : Signal => j.1 ≠ j.2)
          (g := fun k => ((xBasisConjugate σ).toOp k k).re)
          (h := fun i k => siftedBorn (peSel i) (xSel i) σ k)
          (densityOp_diag_re_sum _) (fun i => siftedBorn_sum (peSel i) (xSel i) σ) Q δ
    _ = Math.Concentration.BinomialPassSum.binomialPassSum
          (siftedXTestSampleSize peSel xSel) Q δ (phaseFlipErrorRate σ) := by
        rw [hcard, sum_diag_errorFlag_eq_bitFlipErrorRate (xBasisConjugate σ),
          xBasisConjugate_bitRate_eq_phaseRate σ]

end QKD.BB84.FiniteKey

end
