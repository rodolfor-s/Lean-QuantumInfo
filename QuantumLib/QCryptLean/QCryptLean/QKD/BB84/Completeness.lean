import QCryptLean.Math.Analysis.ComplexSqrtTwo
import QCryptLean.Math.Combinatorics.CoordinateCounts
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BernoulliTails
import QCryptLean.Math.Concentration.BinarySymmetricTail
import QCryptLean.Math.Concentration.BinomialKLChernoff
import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.Concentration.BinomialPassSumBand
import QCryptLean.Math.Concentration.BinomialPassSumCompleteness
import QCryptLean.Math.Concentration.SelectedBinomialPassSum
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRotationFactorization
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.ABRegister
import QCryptLean.QKD.BB84.Model.BellMeasurement
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.Bell
import QCryptLean.Quantum.Symmetry.BellMixture

/-!
# BB84 completeness (honest channel at QBER `Q`, no attack)

The completeness endpoint of the BB84 statement surface: without it, every security theorem is
vacuously satisfiable by the always-abort protocol. On `n` EPR pairs with Bob's half sent through
the **honest channel at QBER `Q`** with **no attack**, the full accept test — the LOCC two-basis
parameter-estimation test AND the error-verification tag match — passes and the error-correction
decode succeeds with probability at least `1 − ε_c`.

**The honest run is noisy.** The source is `honestTensorSource n Q`: the i.i.d. Pauli channel
`ρ ↦ (1 − 2Q)·ρ + Q·(X_B ρ X_B) + Q·(Z_B ρ Z_B)` on Bob's half of each EPR pair, whose bit error
rate and phase error rate are both exactly `Q`. The completeness statement is a genuine
two-subsample Hoeffding statement, valid for every `Q ∈ [0, 1/2]` and every `δ > 0`.

## Main definitions
- `honestPauliChannel`, `honestSourceSingle`: the honest QBER-`Q` channel on Bob's half and
  its action on one EPR pair.
- `honestTensorSource`: the `n`-fold i.i.d. honest source.
- `honestOutcomeWeight`: the computational-basis Born weight of a round-outcome string `ω`
  under the honest source (apply the `H ⊗ H` sift on X-test rounds, then measure both halves in
  the computational basis).
- `honestKeyErrWeight`: the honest-run conditional probability that Bob's key string is `b`
  given Alice's is `a`, read off `honestOutcomeWeight`. This is the reference error model that
  the reconciliation guarantee `ECScheme.DecodesWhp` is charged against.
- `hoeffdingTestAbortBound`: the completeness error
  `ε_c = 2·exp(−2·m_Z·δ²) + 2·exp(−2·m_X·δ²) + εEC` — the two two-sided Hoeffding tails of the
  split-subsample test at the actual subsample sizes, plus the reconciliation-failure mass.
- `testAbortBound`: the completeness error at the relative-entropy (Chernoff) rate,
  `ε_c^KL = Σ_{±} exp(−m_Z·klBer (Q±δ) q) + Σ_{±} exp(−m_X·klBer (Q±δ) q) + εEC` — the four
  one-sided KL tails of the split-subsample test; no margin `η` is needed.

## Main statements
- `honestOutcomeWeight_eq_prod`: the honest outcome weight is the i.i.d. product
  `∏_r (if ω r ∈ {0,3} then (1−Q)/2 else Q/2)` — each round independently disagrees with
  probability exactly `Q`, in BOTH bases (the honest state is `H ⊗ H`-invariant because its bit and
  phase error rates coincide).
- `one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band`: on the honest source at a QBER `q` within
margin `η` of the
  accept centre `Q` (`|q − Q| ≤ δ − η`), the total honest Born mass of the joint event "the full
  accept condition passes AND Bob's syndrome-decode reproduces Alice's key string" is at least
  `1 − ε_c(m_Z, m_X, η, εEC)`. Valid for every `Q ∈ [0, 1/2]` and every `δ, η > 0`.
- `one_sub_testAbortBound_le_sum_of_strict_band`: the same completeness statement with the PE tails
priced
  at the Bernoulli relative-entropy rate `klBer` (Chernoff bound; Cover–Thomas, *Elements of
  Information Theory*, §11.1): for `Q − δ < q < Q + δ` no margin is needed, and the budget is
  `ε_c^KL(m_Z, m_X, Q, δ, q, εEC)`, far sharper than the Hoeffding budget at small error rates.
- `two_le_hoeffdingTestAbortBound_of_empty`: an empty PE subsample forces the budget
  to at least `2`.

References: Bennett–Brassard 1984; Renner 2005 (arXiv:quant-ph/0512258v2) §6.5; Nahar, Tupkary,
Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V (robustness); CKR 2009 (arXiv:0809.3019)
main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma
`\label{lem:extractpart}` :319–:328). -/

open Quantum.Operators Quantum.Symmetry Matrix
open scoped Kronecker Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84

open QKD.BB84.FiniteKey QKD.BB84.Model QKD.BB84.Measurement

/-! ## The honest channel at QBER `Q`

Alice's qubit is the high index of the `4`-dimensional round register and Bob's the low one, so the
channel Alice → Bob acts on the second tensor factor. -/

/-- Flip Bob's bit while keeping Alice's bit register unchanged. -/
def bobPauliX : Op Signal :=
  (1 : Op Bit) ⊗ₖ Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm pauliX

/-- Apply the phase Pauli to Bob's half of the pair. -/
def bobPauliZ : Op Signal :=
  (1 : Op Bit) ⊗ₖ Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm pauliZ

/-- Bob's bit flip exchanges his two computational basis values. -/
lemma bobPauliX_eq_matrix :
    bobPauliX = fun i j : Signal => if i.1 = j.1 ∧ i.2 ≠ j.2 then (1 : ℂ) else 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bobPauliX, pauliX, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, finTwoEquiv]

/-- Bob's phase flip is negative precisely when his computational bit is one. -/
lemma bobPauliZ_eq_matrix :
    bobPauliZ = fun i j : Signal => if i = j then (if i.2 = 0 then (1 : ℂ) else -1) else 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bobPauliZ, pauliZ, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.diagonal_apply, finTwoEquiv]

/-- The Y-free honest Pauli channel: mutually exclusive bit and phase flips of probability `Q`. -/
def honestPauliChannel (Q : ℝ) (ρ : Op Signal) : Op Signal :=
  ((1 - 2 * Q : ℝ) : ℂ) • ρ + (Q : ℂ) • (bobPauliX * ρ * bobPauliX) +
    (Q : ℂ) • (bobPauliZ * ρ * bobPauliZ)

/-- One EPR pair with Bob's half passed through the honest Pauli channel. -/
def honestSourceSingle (Q : ℝ) : Op Signal := honestPauliChannel Q eprSingle.toOp

/-- The honest source is the Bell mixture with weights `1 - 2Q, Q, Q, 0`. -/
private lemma honestSourceSingle_eq_bellDiagonal (Q : ℝ) :
    honestSourceSingle Q = (1 - 2 * Q : ℂ) • bellPOVM 0 +
      (Q : ℂ) • bellPOVM 1 + (Q : ℂ) • bellPOVM 2 := by
  have hX : bobPauliX * bellState 0 = bellState 1 := by
    apply Ket.ext
    funext ⟨i, j⟩
    change (∑ k : Signal, bobPauliX (i, j) k * (bellState 0).vec k) = _
    rw [bobPauliX_eq_matrix]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, bellState,
        Ket.reindex, bellLabelKet, bellKet, finTwoEquiv]
  have hZ : bobPauliZ * bellState 0 = bellState 2 := by
    apply Ket.ext
    funext ⟨i, j⟩
    change (∑ k : Signal, bobPauliZ (i, j) k * (bellState 0).vec k) = _
    rw [bobPauliZ_eq_matrix]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, bellState,
        Ket.reindex, bellLabelKet, bellKet, finTwoEquiv]
  have hXh : bobPauliXᴴ = bobPauliX := by
    ext i j
    change star (bobPauliX j i) = bobPauliX i j
    rw [bobPauliX_eq_matrix]
    simp [eq_comm]
  have hZh : bobPauliZᴴ = bobPauliZ := by
    ext i j
    change star (bobPauliZ j i) = bobPauliZ i j
    rw [bobPauliZ_eq_matrix]
    by_cases h : i = j
    · subst i
      by_cases hbit : j.2 = 0 <;> simp [hbit]
    · simp [h, eq_comm]
  have he : eprSingle.toOp = (bellState 0).projector := rfl
  have hXP := Ket.projector_mul bobPauliX (bellState 0)
  have hZP := Ket.projector_mul bobPauliZ (bellState 0)
  rw [hXh, hX] at hXP
  rw [hZh, hZ] at hZP
  rw [honestSourceSingle, honestPauliChannel, he, ← hXP, ← hZP]
  push_cast
  rfl

/-- The honest pair's entries, including agreement and disagreement coherences. -/
lemma honestSourceSingle_eq_matrix (Q : ℝ) :
    honestSourceSingle Q = fun i j : Signal =>
      if i = j then (if i.1 = i.2 then ((1 - Q : ℝ) : ℂ) / 2 else (Q : ℂ) / 2)
      else if i.1 = i.2 ∧ j.1 = j.2 then ((1 - 3 * Q : ℝ) : ℂ) / 2
      else if i.1 ≠ i.2 ∧ j.1 ≠ j.2 then (Q : ℂ) / 2 else 0 := by
  rw [honestSourceSingle_eq_bellDiagonal]
  ext ⟨i, j⟩ ⟨k, l⟩
  change ((1 - 2 * Q : ℂ) * ((bellState 0).vec (i, j) * star ((bellState 0).vec (k, l))) +
    (Q : ℂ) * ((bellState 1).vec (i, j) * star ((bellState 1).vec (k, l))) +
    (Q : ℂ) * ((bellState 2).vec (i, j) * star ((bellState 2).vec (k, l)))) = _
  have hs : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = 1 / 2 := by
    simpa only [pow_two] using Complex.inv_sqrt_two_mul_self
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bellState, Ket.reindex, bellLabelKet, bellKet, finTwoEquiv] <;>
    ring_nf <;> simp only [hs] <;> ring

/-- The honest pair is unchanged by switching both local bases to X. -/
lemma hadamardPair_honestSourceSingle_conj (Q : ℝ) :
    hadamardPair * honestSourceSingle Q * hadamardPair = honestSourceSingle Q := by
  ext ⟨i, j⟩ ⟨k, l⟩
  change (∑ t : Signal, (∑ u : Signal, hadamardPair (i, j) u *
    honestSourceSingle Q u t) * hadamardPair t (k, l)) = honestSourceSingle Q (i, j) (k, l)
  simp only [honestSourceSingle_eq_matrix, hadamardPair_eq_matrix]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring

/-- The honest single-pair source has trace one, for every real parameter. -/
lemma trace_honestSourceSingle (Q : ℝ) : (honestSourceSingle Q).trace = 1 := by
  rw [honestSourceSingle_eq_matrix]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The honest single-pair source is positive semidefinite on the probability simplex. -/
theorem posSemidef_honestSourceSingle (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (honestSourceSingle q).PosSemidef := by
  rw [honestSourceSingle_eq_bellDiagonal]
  exact (((bellState 0).posSemidef_projector.smul
    (show (0 : ℂ) ≤ 1 - 2 * q by exact_mod_cast (show (0 : ℝ) ≤ 1 - 2 * q by linarith))).add
      ((bellState 1).posSemidef_projector.smul (RCLike.ofReal_nonneg.mpr hq0))).add
        ((bellState 2).posSemidef_projector.smul (RCLike.ofReal_nonneg.mpr hq0))

/-- Independent honest pairs on the natural function type of round registers. -/
def honestTensorSource (n : ℕ) (Q : ℝ) : Op (Signals n) :=
  Matrix.piTensorProduct fun _ : Fin n => honestSourceSingle Q

/-! ## The honest error rates

The two statistics the PE test reads are exactly `Q`. -/

/-! ## The honest outcome weight -/

/-- The **honest computational-basis Born weight** of the round-outcome string `ω` under the
attack-free run at QBER `Q`: the honest source `honestTensorSource n Q` conjugated by the `H ⊗ H`
sift `siftedRotation` (identity off the X-test rounds), read on its computational-basis
diagonal. This is the honest outcome probability `⟨ω| (V ρ_Q^{⊗n} V†) |ω⟩` — an explicit real
diagonal entry, no `Classical.choose`. -/
def honestOutcomeWeight (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Signals n) : ℝ :=
  (((siftedRotation n peSel xSel) * honestTensorSource n Q *
      (siftedRotation n peSel xSel)ᴴ)
    ω ω).re

/-- The conditional honest law of Bob's key given Alice's key, obtained by dividing the
joint outcome mass by Alice's marginal. The marginal is positive for every Alice word, and
`honestKeyErrWeight_eq_bscWeight` identifies this law with the binary-symmetric product law.
A decoding guarantee for this law is a completeness assumption on the supplied scheme. -/
def honestKeyErrWeight (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (a b : KeyBitString n peSel) : ℝ :=
  (∑ ω : Signals n,
      if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
      then honestOutcomeWeight n Q peSel xSel ω else 0) /
  (∑ ω : Signals n,
      if aliceKeyString peSel ω = a
      then honestOutcomeWeight n Q peSel xSel ω else 0)

/-- The **completeness error** `ε_c = 2·exp(−2·m_Z·δ²) + 2·exp(−2·m_X·δ²) + εEC`: the two-sided
Hoeffding tails of the two PE subsamples, at the actual subsample sizes `m_Z`, `m_X`, plus the
reconciliation-failure budget `εEC`. The honest channel sits at the centre of the accept ball, so
each subsample contributes the two-sided tail `2·exp(−2·m·δ²)`; a smaller subsample gives a larger
tail, so a biased PE split that shrinks one subsample costs completeness. -/
def hoeffdingTestAbortBound (mZ mX : ℕ) (δ εEC : ℝ) : ℝ :=
  Math.Concentration.hoeffdingTwoSidedTail mZ δ +
    Math.Concentration.hoeffdingTwoSidedTail mX δ + εEC

/-- **The KL-rate completeness budget** `ε_c^KL = exp(−m_Z·klBer (Q+δ) q) + exp(−m_Z·klBer (Q−δ) q)
+ exp(−m_X·klBer (Q+δ) q) + exp(−m_X·klBer (Q−δ) q) + εEC`: the four one-sided relative-entropy
tails of the split-subsample PE test at the actual subsample sizes — no margin `η` is needed,
because the honest QBER only has to lie strictly inside the accept window — plus the
reconciliation-failure mass `εEC`. By the Chernoff bound the binomial tail decays at the Bernoulli
relative-entropy rate `klBer` (Cover–Thomas, *Elements of Information Theory*, §11.1), which at
small error rates is far sharper than the Hoeffding rate `2·δ²` priced by
`hoeffdingTestAbortBound`. -/
def testAbortBound (mZ mX : ℕ) (Q δ q εEC : ℝ) : ℝ :=
  Math.Concentration.bernoulliWindowTail mZ Q δ q +
    Math.Concentration.bernoulliWindowTail mX Q δ q + εEC

/-! ## Honest-run outcome weight: closed form at QBER `Q`

The honest single-pair state `ρ_Q` is `H ⊗ H`-invariant (its bit and phase error rates are both
`Q`), so every round of the honest run — X-tested or not — reads an agreement outcome `{0, 3}` with
weight `(1−Q)/2` and a mismatch outcome `{1, 2}` with weight `Q/2`. The honest outcome weight
therefore factors round-wise into `∏_r ((1−Q)/2 if ω r ∈ {0, 3} else Q/2)`: an i.i.d. sequence of
rounds, each disagreeing with probability exactly `Q`. -/

/-- **Single-round honest diagonal weight.** For either sift setting (`H ⊗ H` on an X-test round or
the identity otherwise), the computational-basis diagonal of the conjugated single-pair honest state
`rot · ρ_Q · rotᴴ` is `(1−Q)/2` on the agreement outcomes `{0, 3}` and `Q/2` on the mismatch
outcomes `{1, 2}`. On the X-test branch this uses that `H ⊗ H` fixes `ρ_Q`. -/
private lemma honest_singleRound_diag (Q : ℝ) (pe x : Bool) (k : Signal) :
    (xTestPairOp pe x * honestSourceSingle Q *
        (xTestPairOp pe x)ᴴ) k k
      = (if k.1 = k.2 then ((1 - Q : ℝ) : ℂ) / 2 else ((Q : ℝ) : ℂ) / 2) := by
  have hdiag : honestSourceSingle Q k k
      = (if k.1 = k.2 then ((1 - Q : ℝ) : ℂ) / 2 else ((Q : ℝ) : ℂ) / 2) := by
    simp only [honestSourceSingle_eq_matrix, ite_true]
  unfold xTestPairOp
  by_cases h : (pe && x) = true
  · rw [ite_eq_left h, conjTranspose_hadamardPair,
      show hadamardPair * honestSourceSingle Q * hadamardPair
          = honestSourceSingle Q from hadamardPair_honestSourceSingle_conj Q]
    exact hdiag
  · rw [ite_eq_right h, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    exact hdiag

/-- **Round factorization of the honest diagonal weight.** The computational-basis diagonal entry
of the honest conjugated `n`-fold source `V ρ_Q^{⊗n} Vᴴ` at the round-outcome string `ω` factors
round-wise into the single-round diagonal entries `rot_r · ρ_Q · rot_rᴴ`: all three operators are
tensor products over rounds, so their product is the tensor product of the single-round
products. -/
private lemma honest_diag_prod (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Signals n) :
    ((siftedRotation n peSel xSel * honestTensorSource n Q *
        (siftedRotation n peSel xSel)ᴴ)
        ω ω)
      = ∏ r : Fin n, ((xTestPairOp (peSel r) (xSel r) * honestSourceSingle Q *
          (xTestPairOp (peSel r) (xSel r))ᴴ) (ω r) (ω r)) := by
  rw [siftedRotation, honestTensorSource, Matrix.conjTranspose_piTensorProduct,
    Matrix.piTensorProduct_mul, Matrix.piTensorProduct_mul]
  rfl

/-- **Closed form of the honest outcome weight.** On the honest channel at QBER `Q` the honest
computational-basis Born weight factors round-wise into
`∏_r ((1−Q)/2 if ω r ∈ {0, 3} else Q/2)`: each round independently reads an agreement outcome
`{0, 3}` with weight `(1−Q)/2` and a mismatch outcome `{1, 2}` with weight `Q/2`, INDEPENDENT of
the sift — the honest state is `H ⊗ H`-invariant, so the X-test rounds see the same rate. The two
PE subsamples are therefore two independent `Binomial(m, Q)` samples. -/
theorem honestOutcomeWeight_eq_prod (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Signals n) :
    honestOutcomeWeight n Q peSel xSel ω
      = ∏ r : Fin n, (if (ω r).1 = (ω r).2 then (1 - Q) / 2 else Q / 2) := by
  unfold honestOutcomeWeight
  rw [honest_diag_prod]
  simp only [honest_singleRound_diag]
  have hcast : (∏ r : Fin n, (if (ω r).1 = (ω r).2 then ((1 - Q : ℝ) : ℂ) / 2
        else ((Q : ℝ) : ℂ) / 2))
      = (((∏ r : Fin n, (if (ω r).1 = (ω r).2 then (1 - Q) / 2 else Q / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [hcast, Complex.ofReal_re]

/-- The honest outcome weight is nonnegative (a product of nonnegative single-round weights). -/
private lemma honestOutcomeWeight_nonneg (n : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (peSel xSel : Fin n → Bool) (ω : Signals n) :
    0 ≤ honestOutcomeWeight n Q peSel xSel ω := by
  rw [honestOutcomeWeight_eq_prod]
  refine Finset.prod_nonneg fun _ _ => ?_
  split_ifs <;> linarith

/-- The single-round honest weight vector `k ↦ ((1−Q)/2 if k ∈ {0,3} else Q/2)` sums to `1`. -/
private lemma honest_singleRound_sum_one (Q : ℝ) :
    (∑ k : Signal, if k.1 = k.2 then (1 - Q) / 2 else Q / 2) = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [Fin.ext_iff]
  ring

/-- Alice's single-round bit is uniform in the honest outcome law. -/
private lemma honest_singleRound_aliceBit_sum (q : ℝ) (a : Fin 2) :
    (∑ k : Signal, if k.1 = a then
      (if k.1 = k.2 then (1 - q) / 2 else q / 2) else 0) = 1 / 2 := by
  fin_cases a <;> simp only [Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    norm_num [Fin.ext_iff] <;> ring

/-- The joint single-round bit mass is half the binary-symmetric transition weight. -/
private lemma honest_singleRound_bitPair_sum (q : ℝ) (a b : Fin 2) :
    (∑ k : Signal, if k.1 = a ∧ k.2 = b then
      (if k.1 = k.2 then (1 - q) / 2 else q / 2) else 0) =
      (if a = b then 1 - q else q) / 2 := by
  fin_cases a <;> fin_cases b <;> simp only [Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    norm_num [Fin.ext_iff]

/-- Every Alice key has the same strictly positive honest marginal mass. -/
private lemma honest_aliceKey_sum (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool)
    (a : KeyBitString n peSel) :
    (∑ ω, if aliceKeyString peSel ω = a then
      honestOutcomeWeight n q peSel xSel ω else 0) =
        (1 / 2 : ℝ) ^ Fintype.card {i : Fin n // peSel i = false} := by
  classical
  simp only [honestOutcomeWeight_eq_prod, funext_iff, aliceKeyString]
  rw [Fintype.sum_ite_forall_subtype_prod (fun i => peSel i = false)
    (fun _ (k : Signal) => if k.1 = k.2 then (1 - q) / 2 else q / 2)
    (fun _ => honest_singleRound_sum_one q) (fun i (k : Signal) => k.1 = a i)]
  simp only [honest_singleRound_aliceBit_sum, Finset.prod_const, Finset.card_univ]

/-- The honest joint key mass factors as the uniform Alice mass times the BSC transition law. -/
private lemma honest_keyPair_sum (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool)
    (a b : KeyBitString n peSel) :
    (∑ ω, if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b then
      honestOutcomeWeight n q peSel xSel ω else 0) =
        Math.Concentration.BinarySymmetricTail.bscWeight q a b /
          (2 : ℝ) ^ Fintype.card {i : Fin n // peSel i = false} := by
  classical
  simp only [honestOutcomeWeight_eq_prod, funext_iff, aliceKeyString, bobKeyString,
    ← forall_and]
  rw [Fintype.sum_ite_forall_subtype_prod (fun i => peSel i = false)
    (fun _ (k : Signal) => if k.1 = k.2 then (1 - q) / 2 else q / 2)
    (fun _ => honest_singleRound_sum_one q) (fun i (k : Signal) => k.1 = a i ∧ k.2 = b i)]
  simp only [honest_singleRound_bitPair_sum, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Math.Concentration.BinarySymmetricTail.bscWeight]

/-- Conditioned on Alice's word, Bob's honest key has the binary-symmetric product law. -/
theorem honestKeyErrWeight_eq_bscWeight (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool) :
    honestKeyErrWeight n q peSel xSel =
      Math.Concentration.BinarySymmetricTail.bscWeight q := by
  funext a b
  rw [honestKeyErrWeight, honest_keyPair_sum,
    honest_aliceKey_sum, _root_.one_div_pow,
    div_div_div_cancel_right₀ (by positivity), div_one]

/-- **Normalization of the honest outcome weight.** The honest Born weights sum to `1`: each round's
single-round weights sum to `(1−Q)/2 + Q/2 + Q/2 + (1−Q)/2 = 1`, and the product over rounds
is `1`. -/
private lemma sum_honestOutcomeWeight (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool) :
    ∑ ω : Signals n, honestOutcomeWeight n Q peSel xSel ω = 1 := by
  simp only [honestOutcomeWeight_eq_prod]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (k : Signal) =>
    if k.1 = k.2 then (1 - Q) / 2 else Q / 2)]
  exact Finset.prod_eq_one fun _ _ => honest_singleRound_sum_one Q

/-! ## The PE test on the honest channel: two independent binomial subsamples -/

/-- **The selected-subsample band mass is the binomial pass mass.** For any round selector `sel`,
the honest mass at QBER `q` of the round-outcome strings whose disagreement fraction on the
`sel`-subsample lies within `δ` of `Q` equals `binomialPassSum m Q δ q` at the subsample size
`m = #{i | sel i}`: the honest rounds are i.i.d. with mismatch probability `q`, and the unselected
rounds sum out freely.

This is the honest-run instance of the sifted PE reduction
`Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum`; unlike
the attacked case, the selected and unselected Born vectors coincide (the honest state is
`H ⊗ H`-invariant), so the constant-family form suffices. -/
private lemma honest_selectedBand_pass (n : ℕ) (q Q δ : ℝ) (peSel xSel sel : Fin n → Bool) :
    (∑ ω : Signals n,
        if |((Finset.univ.filter (fun i => sel i = true ∧ ((ω i).1 ≠ (ω i).2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then honestOutcomeWeight n q peSel xSel ω else 0)
      = Math.Concentration.BinomialPassSum.binomialPassSum
          (Finset.univ.filter (fun i => sel i = true)).card Q δ q := by
  classical
  set g : Signal → ℝ := fun k => if k.1 = k.2 then (1 - q) / 2 else q / 2 with hg_def
  have hg : (∑ j, g j) = 1 := honest_singleRound_sum_one q
  have hcard : Fintype.card {i // sel i = true}
      = (Finset.univ.filter (fun i => sel i = true)).card := Fintype.card_subtype _
  have hflag : (∑ j ∈ Finset.univ.filter (fun j : Signal => j.1 ≠ j.2), g j) = q := by
    rw [Finset.sum_filter]
    simp only [hg_def, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [Fin.ext_iff]
  have key :=
      Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum
      (n := n) sel (fun k => k.1 ≠ k.2) g g hg hg Q δ
  rw [hflag, hcard] at key
  rw [← key]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hprod : (∏ i : Fin n, (if sel i then g (ω i) else g (ω i)))
      = honestOutcomeWeight n q peSel xSel ω := by
    simp only [ite_self, hg_def]
    exact (honestOutcomeWeight_eq_prod n q peSel xSel ω).symm
  rw [hprod]

/-- The Z-test disagreement count is the flag count on the selector `peSel && !xSel`. -/
private lemma zTest_count_eq (n : ℕ) (peSel xSel : Fin n → Bool)
    (ω : Signals n) :
    (Finset.univ.filter (fun i => (peSel i && !xSel i) = true ∧ ((ω i).1 ≠ (ω i).2))).card
      = siftedZTestErrorCount peSel xSel ω := by
  rw [siftedZTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true',
    and_assoc]

/-- The Z-test subsample size is the size of the selector `peSel && !xSel`. -/
private lemma zTest_size_eq (n : ℕ) (peSel xSel : Fin n → Bool) :
    (Finset.univ.filter (fun i => (peSel i && !xSel i) = true)).card
      = siftedZTestSampleSize peSel xSel := by
  rw [siftedZTestSampleSize]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true']

/-- The X-test disagreement count is the flag count on the selector `peSel && xSel`. -/
private lemma xTest_count_eq (n : ℕ) (peSel xSel : Fin n → Bool)
    (ω : Signals n) :
    (Finset.univ.filter (fun i => (peSel i && xSel i) = true ∧ ((ω i).1 ≠ (ω i).2))).card
      = siftedXTestErrorCount peSel xSel ω := by
  rw [siftedXTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, and_assoc]

/-- The X-test subsample size is the size of the selector `peSel && xSel`. -/
private lemma xTest_size_eq (n : ℕ) (peSel xSel : Fin n → Bool) :
    (Finset.univ.filter (fun i => (peSel i && xSel i) = true)).card
      = siftedXTestSampleSize peSel xSel := by
  rw [siftedXTestSampleSize]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]

/-- **The honest mass failing one PE band is exactly `1 − binomialPassSum m Q δ q`.** The honest
band mass equals the binomial pass mass (`honest_selectedBand_pass`), and the band mass and
its complement add up to the total honest mass `1`, so the failure mass is the exact binomial band
failure — at every subsample size, including the empty one (both sides read the same `0/0 = 0`
junk convention). This is the exact-mass input for both the Hoeffding-priced and the KL-rate
completeness budgets. -/
private lemma sum_honestOutcomeWeight_bandFail_eq_one_sub_binomialPassSum (n : ℕ) (q Q δ : ℝ)
    (peSel xSel sel : Fin n → Bool) :
    (∑ ω : Signals n,
        if |((Finset.univ.filter (fun i => sel i = true ∧ ((ω i).1 ≠ (ω i).2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then 0 else honestOutcomeWeight n q peSel xSel ω)
      = 1 - Math.Concentration.BinomialPassSum.binomialPassSum
          (Finset.univ.filter (fun i => sel i = true)).card Q δ q := by
  classical
  -- The band mass and its complement add up to the total honest mass `1`.
  have hsplit : (∑ ω : Signals n,
        if |((Finset.univ.filter (fun i => sel i = true ∧ ((ω i).1 ≠ (ω i).2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then honestOutcomeWeight n q peSel xSel ω else 0)
      + (∑ ω : Signals n,
        if |((Finset.univ.filter (fun i => sel i = true ∧ ((ω i).1 ≠ (ω i).2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then 0 else honestOutcomeWeight n q peSel xSel ω) = 1 := by
    rw [← Finset.sum_add_distrib, ← sum_honestOutcomeWeight n q peSel xSel]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  have hpass := honest_selectedBand_pass n q Q δ peSel xSel sel
  linarith [hsplit, hpass]

/-- **Honest decode-failure bound.** The total honest Born mass of round-outcome strings whose
syndrome-decode fails is at most `εEC`. Regrouping by `(Alice key, Bob key)` and using
`num = errWeight · marg` (with `marg = Alice-marginal`, `∑ marg = 1`), the reconciliation guarantee
`ec.DecodesWhp (honestKeyErrWeight …) εEC` charges each Alice-conditional failure mass
to `εEC`. -/
private lemma honest_decode_bound (n leakEC : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (peSel xSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (εEC : ℝ)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n Q peSel xSel) εEC) :
    (∑ ω : Signals n,
        if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else honestOutcomeWeight n Q peSel xSel ω) ≤ εEC := by
  classical
  set num : KeyBitString n peSel → KeyBitString n peSel → ℝ :=
    fun a b => ∑ ω : Signals n,
      if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
      then honestOutcomeWeight n Q peSel xSel ω else 0 with hnum
  set den : KeyBitString n peSel → ℝ :=
    fun a => ∑ ω : Signals n,
      if aliceKeyString peSel ω = a
      then honestOutcomeWeight n Q peSel xSel ω else 0 with hden
  have hden_nonneg : ∀ a, 0 ≤ den a := by
    intro a; simp only [hden]; refine Finset.sum_nonneg fun ω _ => ?_
    split_ifs
    · exact honestOutcomeWeight_nonneg n Q hQ0 hQ1 peSel xSel ω
    · exact le_refl 0
  have hnum_nonneg : ∀ a b, 0 ≤ num a b := by
    intro a b; simp only [hnum]; refine Finset.sum_nonneg fun ω _ => ?_
    split_ifs
    · exact honestOutcomeWeight_nonneg n Q hQ0 hQ1 peSel xSel ω
    · exact le_refl 0
  have hnum_le : ∀ a b, num a b ≤ den a := by
    intro a b; simp only [hnum, hden]; refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h : aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
    · rw [ite_eq_left h, ite_eq_left h.1]
    · rw [ite_eq_right h]; split_ifs
      · exact honestOutcomeWeight_nonneg n Q hQ0 hQ1 peSel xSel ω
      · exact le_refl 0
  have herrW : ∀ a b, num a b = honestKeyErrWeight n Q peSel xSel a b * den a := by
    intro a b
    by_cases hm : den a = 0
    · have hj : num a b = 0 := le_antisymm (hm ▸ hnum_le a b) (hnum_nonneg a b)
      rw [hj, hm, mul_zero]
    · have heq : honestKeyErrWeight n Q peSel xSel a b = num a b / den a := by
        simp only [hnum, hden, honestKeyErrWeight]
      rw [heq, div_mul_cancel₀ _ hm]
  have hden_sum : (∑ a, den a) = 1 := by
    simp only [hden]
    rw [Finset.sum_comm]
    have hcollapse : ∀ ω, (∑ a, if aliceKeyString peSel ω = a
        then honestOutcomeWeight n Q peSel xSel ω else 0)
        = honestOutcomeWeight n Q peSel xSel ω := fun ω => by simp [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl (fun ω _ => hcollapse ω)]
    exact sum_honestOutcomeWeight n Q peSel xSel
  have hregroup : (∑ ω : Signals n,
        if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else honestOutcomeWeight n Q peSel xSel ω)
      = ∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b := by
    have hpt : ∀ ω, (if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else honestOutcomeWeight n Q peSel xSel ω)
        = ∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0
            else if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
              then honestOutcomeWeight n Q peSel xSel ω else 0 := by
      intro ω
      rw [Finset.sum_eq_single (aliceKeyString peSel ω)]
      · rw [Finset.sum_eq_single (bobKeyString peSel ω)]
        · simp
        · intro b _ hb
          have hb' : bobKeyString peSel ω ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        have ha' : aliceKeyString peSel ω ≠ a := fun h => ha h.symm
        simp [ha']
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hnum]
    split_ifs with hC
    · simp
    · rfl
  rw [hregroup]
  have hpera : ∀ a, (∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
      ≤ den a * εEC := by
    intro a
    have hstep : (∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
        = den a * ∑ b, (if ec.decode b (ec.syndrome a) = a then 0
            else honestKeyErrWeight n Q peSel xSel a b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [herrW a b]
      split_ifs <;> ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (hDecode a) (hden_nonneg a)
  calc (∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
         ≤ ∑ a, den a * εEC := Finset.sum_le_sum fun a _ => hpera a
    _ = (∑ a, den a) * εEC := by rw [← Finset.sum_mul]
    _ = 1 * εEC := by rw [hden_sum]
    _ = εEC := one_mul εEC

/-- **A reconciliation guarantee against the honest error model has a nonnegative budget.**  The
honest conditional key-error weights are nonnegative for `0 ≤ Q ≤ 1`, so the decode-failure mass
of any Alice key string, which `hDecode` bounds by `εEC`, is nonnegative. -/
theorem nonneg_of_decodesWhp_honestKeyErrWeight {n leakEC : ℕ} {peSel xSel : Fin n → Bool}
    {ec : ECScheme n peSel leakEC} {Q εEC : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n Q peSel xSel) εEC) : 0 ≤ εEC := by
  classical
  refine le_trans (Finset.sum_nonneg fun b _ => ?_) (hDecode fun _ => 0)
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg fun ω _ => by
        split_ifs
        · exact honestOutcomeWeight_nonneg n Q hQ0 hQ1 peSel xSel ω
        · exact le_rfl)
      (Finset.sum_nonneg fun ω _ => by
        split_ifs
        · exact honestOutcomeWeight_nonneg n Q hQ0 hQ1 peSel xSel ω
        · exact le_rfl)

/-- **An empty subsample makes the completeness budget at least two.**  It contributes the term
`2·exp(0) = 2`; the other terms are nonnegative once `εEC` is. -/
theorem two_le_hoeffdingTestAbortBound_of_empty (mZ mX : ℕ) (δ εEC : ℝ) (hεEC : 0 ≤ εEC)
    (h : mZ = 0 ∨ mX = 0) : 2 ≤ hoeffdingTestAbortBound mZ mX δ εEC := by
  simp only [hoeffdingTestAbortBound,
    Math.Concentration.hoeffdingTwoSidedTail]
  rcases h with rfl | rfl
  · have := Real.exp_pos (-2 * (mX : ℝ) * δ ^ 2)
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    linarith
  · have := Real.exp_pos (-2 * (mZ : ℝ) * δ ^ 2)
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    linarith

/-- **An empty subsample makes the KL-rate completeness budget at least two.**  It contributes the
two terms `exp(0) + exp(0) = 2`; the other terms are nonnegative once `εEC` is. -/
theorem two_le_testAbortBound_of_empty (mZ mX : ℕ) (Q δ q εEC : ℝ) (hεEC : 0 ≤ εEC)
    (h : mZ = 0 ∨ mX = 0) : 2 ≤ testAbortBound mZ mX Q δ q εEC := by
  simp only [testAbortBound,
    Math.Concentration.bernoulliWindowTail,
    Math.Concentration.bernoulliChernoffTail]
  rcases h with rfl | rfl
  · have h1 := Real.exp_pos (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q)
    have h2 := Real.exp_pos (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)
    simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero] at h1 h2 ⊢
    linarith
  · have h1 := Real.exp_pos (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q)
    have h2 := Real.exp_pos (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)
    simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero] at h1 h2 ⊢
    linarith

/-- **BB84 completeness core: exact PE-band failure tails.**

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept test — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − (eZ + eX + εEC)`, where `eZ` and `eX` are any upper
bounds on the exact binomial band-failure masses `1 − binomialPassSum m Q δ q` of the Z- and
X-test subsamples (`sum_honestOutcomeWeight_bandFail_eq_one_sub_binomialPassSum`). The
reconciliation hypothesis is charged against
the honest error model at the actual QBER `q`. Both the Hoeffding-priced
(`one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band`) and the KL-rate Chernoff-priced
(`one_sub_testAbortBound_le_sum_of_strict_band`) completeness statements are instances, differing
only in
how `eZ`, `eX` are priced. -/
private lemma one_sub_add_le_sum_honestOutcomeWeight_of_bandFail_le (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ εEC eZ eX : ℝ)
    (hZnonempty : 0 < siftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < siftedXTestSampleSize peSel xSel)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hZ : 1 - Math.Concentration.BinomialPassSum.binomialPassSum
        (siftedZTestSampleSize peSel xSel) Q δ q ≤ eZ)
    (hX : 1 - Math.Concentration.BinomialPassSum.binomialPassSum
        (siftedXTestSampleSize peSel xSel) Q δ q ≤ eX)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n q peSel xSel) εEC) :
    1 - (eZ + eX + εEC) ≤
      ∑ ω : Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then honestOutcomeWeight n q peSel xSel ω else 0) := by
  classical
  set w : (Signals n) → ℝ := honestOutcomeWeight n q peSel xSel with hw
  have hw_nonneg : ∀ ω, 0 ≤ w ω := fun ω => honestOutcomeWeight_nonneg n q hq0 hq1 peSel xSel ω
  -- Split the accept∧decode mass off the total: `∑ [P] w = (∑ w) − ∑ [¬P] w`.
  have hsplit : (∑ ω : Signals n,
        if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then w ω else 0)
      = (∑ ω : Signals n, w ω)
        - ∑ ω : Signals n,
            (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
                 ec.decode (bobKeyString peSel ω)
                     (ec.syndrome (aliceKeyString peSel ω)) =
                   aliceKeyString peSel ω
              then 0 else w ω) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [hsplit, sum_honestOutcomeWeight]
  -- The test-or-decode failure mass is at most the PE-failure mass plus the decode-failure mass:
  -- wherever the decode succeeds the two error-verification tags are the same value, so the only
  -- way the full test can reject is the PE test.
  have hfail_le : (∑ ω : Signals n,
        if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else w ω)
      ≤ (∑ ω : Signals n,
          if siftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
        + ∑ ω : Signals n,
          if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
            then 0 else w ω := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hPEi : (0 : ℝ) ≤
        if siftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω := by
      split_ifs
      · exact le_refl 0
      · exact hw_nonneg ω
    have hDi : (0 : ℝ) ≤
        if ec.decode (bobKeyString peSel ω)
            (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else w ω := by
      split_ifs
      · exact le_refl 0
      · exact hw_nonneg ω
    by_cases hd : ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
    · -- The decode succeeds, so the EV tags coincide and only the PE test can reject.
      have hEV : evVerified ℓEV peSel ec t ω = true := by
        simp [evVerified, hd]
      rw [ite_eq_left hd, add_zero]
      by_cases hp : siftedLocalPETestPassed peSel xSel δ Q ω = true
      · have ha : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true := by
          simp [siftedLocalPEAndEVPassed, hp, hEV]
        rw [ite_eq_left ⟨ha, hd⟩, ite_eq_left hp]
      · rw [ite_eq_right hp]
        split_ifs
        · exact hw_nonneg ω
        · exact le_refl _
    · rw [ite_eq_right (fun h : _ ∧ _ => hd h.2), ite_eq_right hd]
      linarith
  -- The PE-failure mass is at most the sum of the two exact band-failure masses, hence at most
  -- `eZ + eX` by the tail hypotheses.
  have hpe : (∑ ω : Signals n,
        if siftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
      ≤ eZ + eX := by
    have hZsize := zTest_size_eq n peSel xSel
    have hXsize := xTest_size_eq n peSel xSel
    have hZexact := sum_honestOutcomeWeight_bandFail_eq_one_sub_binomialPassSum n q Q δ peSel xSel
      (fun i => peSel i && !xSel i)
    have hXexact := sum_honestOutcomeWeight_bandFail_eq_one_sub_binomialPassSum n q Q δ peSel xSel
      (fun i => peSel i && xSel i)
    simp only [zTest_count_eq, hZsize, xTest_count_eq, hXsize] at hZexact hXexact
    calc (∑ ω : Signals n,
          if siftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
        ≤ (∑ ω : Signals n,
            if |(siftedZTestErrorCount peSel xSel ω : ℝ) /
                  (siftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω)
          + ∑ ω : Signals n,
            if |(siftedXTestErrorCount peSel xSel ω : ℝ) /
                  (siftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun ω _ => ?_
          by_cases hp : siftedLocalPETestPassed peSel xSel δ Q ω = true
          · have hband := hp
            rw [siftedLocalPETestPassed] at hband
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hband
            rw [ite_eq_left hp, ite_eq_left hband.1.2, ite_eq_left hband.2.2]
            norm_num
          · rw [ite_eq_right hp]
            have hZi : (0 : ℝ) ≤ if |(siftedZTestErrorCount peSel xSel ω : ℝ) /
                  (siftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
              split_ifs
              · exact le_refl 0
              · exact hw_nonneg ω
            have hXi : (0 : ℝ) ≤ if |(siftedXTestErrorCount peSel xSel ω : ℝ) /
                  (siftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
              split_ifs
              · exact le_refl 0
              · exact hw_nonneg ω
            -- Failing the conjunctive test means failing at least one band.
            have hone : ¬ (|(siftedZTestErrorCount peSel xSel ω : ℝ) /
                  (siftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ ∧
              |(siftedXTestErrorCount peSel xSel ω : ℝ) /
                (siftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ) := by
              intro ⟨h1, h2⟩
              exact hp (by
                rw [siftedLocalPETestPassed]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨hZnonempty, h1⟩, ⟨hXnonempty, h2⟩⟩)
            rcases not_and_or.mp hone with h | h
            · rw [ite_eq_right h]; linarith
            · rw [ite_eq_right h]; linarith
      _ = (1 - Math.Concentration.BinomialPassSum.binomialPassSum
              (siftedZTestSampleSize peSel xSel) Q δ q)
          + (1 - Math.Concentration.BinomialPassSum.binomialPassSum
              (siftedXTestSampleSize peSel xSel) Q δ q) := by
          rw [hZexact, hXexact]
      _ ≤ eZ + eX := add_le_add hZ hX
  have hdec := honest_decode_bound n leakEC q hq0 hq1 peSel xSel ec εEC hDecode
  linarith [hfail_le, hpe, hdec]

/-- **BB84 completeness at a shifted honest QBER, priced at the relative-entropy (Chernoff) rate.**

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept test — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − ε_c^KL(m_Z, m_X, Q, δ, q, εEC)`, whenever the honest
QBER lies strictly inside the accept window, `Q − δ < q < Q + δ`. No margin is needed: each
subsample's PE-failure mass is the exact binomial band failure
(`sum_honestOutcomeWeight_bandFail_eq_one_sub_binomialPassSum`),
dominated by the two one-sided KL-rate Chernoff exponents
(`one_sub_binomialPassSum_le_exp_add_exp`; Chernoff bound, Cover–Thomas, *Elements of
Information
Theory*, §11.1). The reconciliation hypothesis is charged against the honest error model at the
actual QBER `q`. -/
theorem one_sub_testAbortBound_le_sum_of_strict_band (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ εEC : ℝ)
    (hZnonempty : 0 < siftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < siftedXTestSampleSize peSel xSel)
    (hq0 : 0 < q) (hq1 : q < 1) (hlo : Q - δ < q) (hhi : q < Q + δ)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n q peSel xSel) εEC) :
    1 - testAbortBound (siftedZTestSampleSize peSel xSel)
          (siftedXTestSampleSize peSel xSel) Q δ q εEC ≤
      ∑ ω : Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then honestOutcomeWeight n q peSel xSel ω else 0) := by
  refine one_sub_add_le_sum_honestOutcomeWeight_of_bandFail_le n ℓEV leakEC peSel xSel ec t q Q δ
    εEC
    (Real.exp (-(siftedZTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(siftedZTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q - δ) q))
    (Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q - δ) q))
    hZnonempty hXnonempty hq0.le hq1.le ?_ ?_ hDecode
  · exact Math.Concentration.BinomialKLChernoff.one_sub_binomialPassSum_le_exp_add_exp _ _ _ _
      hq0 hq1 hlo hhi
  · exact Math.Concentration.BinomialKLChernoff.one_sub_binomialPassSum_le_exp_add_exp _ _ _ _
      hq0 hq1 hlo hhi

/-- **BB84 completeness at a shifted honest QBER** (Hoeffding-priced statement, unchanged).

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept test — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − ε_c(m_Z, m_X, η, εEC)`, whenever `q` lies in the
window shrunk by a margin `η > 0`, i.e. `|q − Q| ≤ δ − η`. The centred case `q = Q`, `η = δ` is the
completeness guarantee at the accept centre itself.

Corollary of the exact-band core `one_sub_add_le_sum_honestOutcomeWeight_of_bandFail_le` with the
two subsample tails
priced at the two-sided Hoeffding rate `2·exp(−2·m·η²)` (which is what needs the margin `η`); the
KL-rate Chernoff corollary `one_sub_testAbortBound_le_sum_of_strict_band` prices the same core
without a
margin. -/
theorem one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ η εEC : ℝ)
    (hZnonempty : 0 < siftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < siftedXTestSampleSize peSel xSel)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη : 0 < η) (hband : |q - Q| ≤ δ - η)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight n q peSel xSel) εEC) :
    1 - hoeffdingTestAbortBound (siftedZTestSampleSize peSel xSel)
          (siftedXTestSampleSize peSel xSel) η εEC ≤
      ∑ ω : Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then honestOutcomeWeight n q peSel xSel ω else 0) := by
  refine one_sub_add_le_sum_honestOutcomeWeight_of_bandFail_le n ℓEV leakEC peSel xSel ec t q Q δ
    εEC
    (2 * Real.exp (-2 * (siftedZTestSampleSize peSel xSel : ℝ) * η ^ 2))
    (2 * Real.exp (-2 * (siftedXTestSampleSize peSel xSel : ℝ) * η ^ 2))
    hZnonempty hXnonempty hq0 hq1 ?_ ?_ hDecode
  · exact Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding_of_mem_band
      _ (ne_of_gt hZnonempty) Q δ η q hq0 hq1 hη hband
  · exact Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding_of_mem_band
      _ (ne_of_gt hXnonempty) Q δ η q hq0 hq1 hη hband

end QKD.BB84

end -- noncomputable section
