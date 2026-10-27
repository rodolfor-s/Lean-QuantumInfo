import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.BellPostMeasurement
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Bell

/-!
# The genuine-LOCC two-basis sift: H⊗H on X-test rounds, fail-closed local PE

The genuine-LOCC sifting layer of BB84: a **local product** `H ⊗ H` on X-designated test rounds
(EB-honest, licensed by the source-replacement identity that an `X`-basis measurement on Alice's
half of an EPR pair is equivalent to preparing and sending an `X`-basis state), contrasted with the
Bell-rotation sift `siftedPairOp`, which is not LOCC-implementable (it requires
four-Bell-state discrimination). The parameter-estimation test built on the local sift is the LOCC
two-basis test on announced local outcomes, **fail-closed** on empty subsamples (an empty Z- or
X-subsample rejects, rather than silently passing).

## Main definitions

* `siftedPairOp` — the per-round Bell-rotation sift `V` on PE rounds, identity on
  key rounds; not LOCC-implementable.
* `xTestPairOp`, `siftedRotation` — the per-round / `n`-round LOCC sift: `H ⊗ H` on
  `peSel ∧ xSel` rounds, identity elsewhere.
* `siftedLocalPETestPassed` — the fail-closed LOCC two-basis test (Z- and X-subsample
  disagreement fractions each within `δ` of `Q`, both subsamples required non-empty).
* `siftedLocalPEAndEVPassed` — the full accept predicate: the PE test above **and** the
  error-verification tag matches (`evVerified`).
* `siftedRotatedPreOutput`, `siftedEveConditioned`, `siftedPostMeasurementCQState` —
  the sifted pre-channel output and its outcome-conditioned CQ state.
* `postMeasurementCQSiftedLocalPEPassFilter`,
  `siftedLocalPEAcceptedPostMeasurementCQState` — the fail-closed local-PE pass filter and the
  physical accept CQ state at `siftedLocalPETestPassed`.

## Main results

* `conjTranspose_mul_siftedRotation`, `conjTranspose_mul_siftedRotation_tensor_one` — the sift is
unitary.
* `siftedPostMeasurementCQState_weight_eq_one` — the post-measurement CQ blocks have total
  weight one.
* `hadamardPair_conj_bellTwirl` — `(H⊗H) G_k (H⊗H) = G_{σ k}` with `σ = ![0,3,2,1]`: the X-test sift
  relabels the bilateral Bell twirl group by `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`, with no sign.

Bell-twirl invariance of the accept test defined here
(`siftedLocalPEAndEVPassed_bellTwirl_invariant`, `evVerified_shift_invariant`,
`key_strings_shift`, `siftedLocalPETestPassed_bellTwirl_invariant`) is analysis built on the
FiniteKey's twirl-permutation machinery (`bellKeyOutcomePerm`, `RoundKernel.lean`) and lives in
`QKD.BB84.FiniteKey.Postselection.SiftedAcceptTwirlInvariant`, not here.

## References

Renner 2005 §5, §6.5; Nahar et al. 2024 (`arXiv:2403.11851`) §B; Shor–Preskill 2000 (the Z↔X basis
duality).
-/

open Quantum.Operators Matrix Quantum.Channels
open QKD.BB84.Measurement Quantum.Symmetry
open InfoTheory.SmoothMinEntropy
open Quantum.DeFinetti MeasureTheory
open QKD.BB84.FiniteKey
open scoped Kronecker Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## The Bell-rotation sift: `V` on PE rounds, identity on key rounds

The sifting rotation `siftedPairOp` is `V` on PE rounds, `1` on key rounds.
Reading the `V`-rotated PE rounds in the computational basis is reading them in the **Bell** basis
(Renner 2005 `arXiv:quant-ph/0512258v2`, §6.5); the key rounds are read in the genuine
computational `Z` basis. It requires four-Bell-state discrimination and so is not
LOCC-implementable; the genuine-LOCC replacement below (`xTestPairOp`/
`siftedRotation`, `H ⊗ H`) uses only local single-qubit gates. -/

/-- The per-round sifting operator: the single-pair Bell rotation `V` on a PE round, the
identity on a key round.  Both are unitary, so the per-round operator is unitary. -/
def siftedPairOp (peSel : Bool) : Op Signal :=
  if peSel then bellBasisRotation else (1 : Op Signal)

/-- The per-round sifting operator is unitary: `Vᴴ V = 1` on PE rounds (Bell orthonormality),
`1ᴴ 1 = 1` on key rounds. -/
theorem conjTranspose_mul_siftedPairOp (peSel : Bool) :
    (siftedPairOp peSel)ᴴ * siftedPairOp peSel =
        (1 : Op Signal) := by
  cases peSel <;> simp [siftedPairOp, conjTranspose_mul_bellBasisRotation]

/-! ## The H⊗H sift on X-test rounds -/

/-- The per-round LOCC sift operator: the local product `H ⊗ H` (`hadamardPair`) on a round that
is both PE-designated and X-designated, the identity otherwise. Both are unitary and, crucially,
both are **local products of single-qubit gates** — LOCC-implementable (unlike the Bell-basis Bell
rotation `V`). -/
def xTestPairOp (peSel xSel : Bool) : Op Signal :=
  if peSel && xSel then hadamardPair else (1 : Op Signal)

/-- The per-round LOCC sift operator is unitary: `(H⊗H)ᴴ (H⊗H) = 1` on X-test rounds (Hermitian
involution), `1ᴴ 1 = 1` elsewhere. -/
theorem conjTranspose_mul_xTestPairOp (peSel xSel : Bool) :
    (xTestPairOp peSel xSel)ᴴ * xTestPairOp peSel xSel =
      (1 : Op Signal) := by
  unfold xTestPairOp
  by_cases h : (peSel && xSel) = true
  · rw [ite_eq_left h, conjTranspose_hadamardPair, hadamardPair_mul_self]
  · rw [ite_eq_right h, Matrix.conjTranspose_one, Matrix.one_mul]

/-- The `n`-round LOCC sift unitary: the tensor product over rounds of
`xTestPairOp (peSel a) (xSel a)`, entry `(i, j) = ∏ a, (H⊗H or 1)_{i_a, j_a}` under
the mixed-radix tensor index. On X-test rounds it is the LOCAL `H ⊗ H`; on Z-test and key rounds
it is the identity. A product of local unitaries, LOCC-implementable. Explicit; no
`Classical.choose`. -/
def siftedRotation (n : ℕ) (peSel xSel : Fin n → Bool) : Op (Signals n) :=
  piTensorProduct fun a => xTestPairOp (peSel a) (xSel a)

/-- **`siftedRotation` is unitary**: every round factor is unitary
(`conjTranspose_mul_xTestPairOp`), and a tensor product of isometries is an isometry
(`conjTranspose_tensorFamily_mul_self`). -/
theorem conjTranspose_mul_siftedRotation (n : ℕ) (peSel xSel : Fin n → Bool) :
    (siftedRotation n peSel xSel)ᴴ * siftedRotation n peSel xSel = 1 := by
  rw [siftedRotation, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [conjTranspose_mul_xTestPairOp, piTensorProduct_one]

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- `siftedRotation peSel xSel ⊗ 1_E` is unitary, from `conjTranspose_mul_siftedRotation`. -/
theorem conjTranspose_mul_siftedRotation_tensor_one (n : ℕ) (peSel xSel : Fin n → Bool) :
    (siftedRotation n peSel xSel ⊗ₖ (1 : Op E))ᴴ *
      (siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_mul_siftedRotation,
    conjTranspose_one, one_mul, one_kronecker_one]

/-! ## The fail-closed LOCC two-basis parameter-estimation test -/

/-- Disagreement count on the Z-test subsample: PE rounds that are NOT X-designated with a
bit-mismatch outcome (`ω i ∈ {1, 2}`). -/
def siftedZTestErrorCount {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Signals n) : ℕ :=
  (Finset.univ.filter (fun i =>
    peSel i = true ∧ xSel i = false ∧ (ω i).1 ≠ (ω i).2)).card

/-- Disagreement count on the X-test subsample: PE rounds that ARE X-designated with a
(rotated-frame) bit-mismatch outcome (`ω i ∈ {1, 2}`). -/
def siftedXTestErrorCount {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Signals n) : ℕ :=
  (Finset.univ.filter (fun i =>
    peSel i = true ∧ xSel i = true ∧ (ω i).1 ≠ (ω i).2)).card

/-- **The fail-closed LOCC two-basis PE test.** Both subsamples must be non-empty and both
disagreement fractions must lie within `δ` of `Q`. Computed entirely from announced local
outcomes — no joint (trans-laboratory) measurement anywhere, so the test uses only classical public
  data.
**Fail-closed:** an empty Z-subsample OR an empty X-subsample rejects
(`decide (0 < mZ) && decide (0 < mX) && …`), so a degenerate selector cannot silently disable a
basis's test. -/
def siftedLocalPETestPassed {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ω : Signals n) : Bool :=
  let mZ : ℕ := siftedZTestSampleSize peSel xSel
  let mX : ℕ := siftedXTestSampleSize peSel xSel
  (decide (0 < mZ) &&
    decide (|(siftedZTestErrorCount peSel xSel ω : ℝ) / mZ - Q| ≤ δ)) &&
  (decide (0 < mX) &&
    decide (|(siftedXTestErrorCount peSel xSel ω : ℝ) / mX - Q| ≤ δ))

/-- **The full accept predicate: parameter estimation AND error verification.**

The protocol accepts a round-outcome string `ω` under the error-verification seed `t` iff the
fail-closed LOCC two-basis PE test passes *and* Alice's announced `ℓEV`-bit tag matches the tag of
Bob's syndrome-decoded string (`evVerified`). This is the predicate the real and ideal pass
Kraus operators are gated on.

The PE-only test `siftedLocalPETestPassed` is deliberately left as its own declaration: it is
the predicate the accept-weight functional `siftedEveVisiblePEPassWeight`, the
accept-weight dichotomy, and `one_sub_hoeffdingTestAbortBound_le_sum_of_mem_band` read. Since
accepting here implies
accepting there, the EV conjunct only shrinks the accept set relative to the PE-only test.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C "Classical part"
(main.tex:906–919): error correction followed by error verification comparing hash values of
length `log(1/ε_EV)` (main.tex:917). -/
def siftedLocalPEAndEVPassed {n : ℕ} (ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Signals n) : Bool :=
  siftedLocalPETestPassed peSel xSel δ Q ω && evVerified ℓEV peSel ec t ω

/-- Accepting the full test implies accepting the PE-only test: the EV conjunct can only shrink
the accept set. Consumed wherever a bound stated at the PE-only accept event must cover the
channels' actual (PE ∧ EV) accept event. -/
theorem siftedLocalPETestPassed_of_siftedLocalPEAndEVPassed {n : ℕ} (ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Signals n)
    (h : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true) :
    siftedLocalPETestPassed peSel xSel δ Q ω = true :=
  (Bool.and_eq_true _ _ |>.mp h).1

/-! ## The `H ⊗ H` relabel of the bilateral Bell twirl group

On an X-designated PE round the LOCC sift conjugates the round by `H ⊗ H`, so a bilateral Pauli
`G_k` of the twirl group `bilateralPauli = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]` is seen in the
rotated frame as `G_{σ k}`.  The relabel `σ` is the involution `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`, and it
is **sign-free**: the single-qubit `H Y H = −Y` sign is real, but it appears twice in `Y ⊗ Y` and
squares away.

The relabel is why a twirl argument may be run round-wise across the two PE bases at once: the twirl
group is closed under it (`hadamardPair_conj_bellTwirl`), and every element's key-round action is
already covered by `siftedLocalPETestPassed_bellTwirl_invariant`.  Under `σ` the off-diagonal
(bit-flipping) set `{X⊗X, Y⊗Y}` is carried to `{Y⊗Y, Z⊗Z}`, so on X-designated PE rounds the
flipping elements are `{Y, Z}`, not `{X, Y}`.
-/

/-- **The `H ⊗ H` relabel `σ` of the bilateral Bell twirl group**: `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`,
i.e. `![0, 3, 2, 1]`.  An involution, with no sign. -/
def bellHadSwap : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- **`(H⊗H) G_k (H⊗H) = G_{σ k}`** with `σ = bellHadSwap = ![0,3,2,1]`: the X-test sift carries the
bilateral Bell twirl group to itself, relabelling `I⊗I ↦ I⊗I`, `X⊗X ↦ Z⊗Z`, `Y⊗Y ↦ Y⊗Y`,
`Z⊗Z ↦ X⊗X`, with **coefficient `+1` in every case** — the `H Y H = −Y` sign appears on both tensor
factors of `Y ⊗ Y` and cancels. -/
theorem hadamardPair_conj_bellTwirl (k : Fin 4) :
    hadamardPair *
        reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
          (finTwoEquiv.symm.prodCongr finTwoEquiv.symm) (bilateralPauli k) * hadamardPair =
      reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
        (finTwoEquiv.symm.prodCongr finTwoEquiv.symm) (bilateralPauli (bellHadSwap k)) := by
  let e : Bool × Bool ≃ Signal := finTwoEquiv.symm.prodCongr finTwoEquiv.symm
  have hH : hadamardPair = reindex e e
      (Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard) := rfl
  rw [hH]
  change reindex e e _ * reindex e e _ * reindex e e _ = reindex e e _
  rw [← reindex_mul, ← reindex_mul]
  congr 1
  unfold bilateralPauli bellHadSwap
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Quantum.Gates.hadamard_conj_pauli]
  split_ifs <;> ext i j <;> simp [kroneckerMap_apply]

/-! ## The post-measurement CQ stack: sifted blocks, local-PE filter, accept state

The channel's accept event is read from the sifted state: the difference of the real and ideal
channels is supported on `siftedLocalPETestPassed` evaluated after the local `H ⊗ H` sift, so
the accept-weight functional that bounds it must read that test on a
`siftedRotation`-conjugated state. -/

/-- Rotate the pre-channel output into the local measurement frame. -/
def siftedRotatedPreOutput {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) : DensityOp (Signals n × E) :=
  UnitaryOp.evolve (⟨siftedRotation n peSel xSel ⊗ₖ (1 : Op E), mem_unitaryGroup_iff'.mpr
    (conjTranspose_mul_siftedRotation_tensor_one E n peSel xSel)⟩ :
      UnitaryOp (Signals n × E)) (hpre.applyDensity ρ)

/-- The retained Eve block conditioned on a complete signal outcome string. -/
def siftedEveConditioned {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) (ω : Signals n) : SubDensityOp E :=
  (siftedRotatedPreOutput E pre hpre peSel xSel ρ).toSubDensityOp.submatrix
    (fun a => (ω, a)) (fun _ _ h => congrArg Prod.snd h)

/-- The complete outcome family has total weight one. -/
theorem siftedPostMeasurementCQState_weight_eq_one {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) :
    ∑ ω, (siftedEveConditioned E pre hpre peSel xSel ρ ω).trace = 1 := by
  have h := congrArg Complex.re (siftedRotatedPreOutput E pre hpre peSel xSel ρ).trace_one
  simpa only [siftedEveConditioned, SubDensityOp.submatrix, SubDensityOp.trace,
    DensityOp.toSubDensityOp, Matrix.trace, Matrix.diag, Matrix.submatrix_apply,
    Complex.re_sum, Fintype.sum_prod_type, Complex.one_re] using h

/-- The measured signal string and its conditional retained quantum state. -/
def siftedPostMeasurementCQState {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (Signals n)) : CQState (Signals n) E where
  stateMap := siftedEveConditioned E pre hpre peSel xSel ρ
  weight_le_one := (siftedPostMeasurementCQState_weight_eq_one E pre hpre peSel xSel ρ).le

/-- Keep exactly the outcomes passing both nonempty, basis-specific parameter tests. -/
def postMeasurementCQSiftedLocalPEPassFilter {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ρ : CQState (Signals n) E) : CQState (Signals n) E :=
  ρ.filterKeep (siftedLocalPETestPassed peSel xSel δ Q)

/-- The accepted CQ state of the intrinsic tensor-power mixture. -/
def siftedLocalPEAcceptedPostMeasurementCQState {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (μ : DensityMeasure Signal) (Q δ : ℝ) : CQState (Signals n) E :=
  postMeasurementCQSiftedLocalPEPassFilter E peSel xSel Q δ
    (siftedPostMeasurementCQState E pre hpre peSel xSel (integralTensorPowerDensity n μ))

end QKD.BB84.Model

end
