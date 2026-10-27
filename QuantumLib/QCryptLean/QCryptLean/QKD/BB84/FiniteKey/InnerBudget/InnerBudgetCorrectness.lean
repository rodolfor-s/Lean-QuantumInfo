import QCryptLean.Math.Combinatorics.TripleSum
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AnnouncedChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-!
# The exact pass-block split and error-verification correctness

The real and ideal abort branches coincide. Their pass channels split exactly into agree and
differ outcomes according to the reconciled strings, including the ideal channel's fresh-key
outputs. The differ blocks have total trace norm at most `2 * 2^(-ℓEV)` on every input and
reference. This bound uses the universal verification hash and holds for every decoder.

The pass-channel positivity and trace estimates support the channel-level decomposition in
`PassBlocks.lean`; correctness is bounded before applying postselection to the agree block.

Reference: Nahar et al. 2024, arXiv:2403.11851, Section V.C and Appendix B.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open scoped Kronecker Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

variable (E : Type*) [Fintype E] [DecidableEq E]

/-!
## The general-`m` differ pass Kraus families

Restrictions of the general-`m` pass Kraus families
`Announced.retainedSiftedPEAnnounce{PassBranch,IdealPass}Kraus` (`SiftedPEAnnounce.lean`) to the
branch
where Alice's and Bob's key strings differ.  Their agree complements
`realPassAgreeKraus` / `idealPassAgreeKraus` live in `AgreeChannels.lean`.
-/

open scoped Classical in
/-- **Differ-restricted general-`m` real pass Kraus family**: the general-`m` pass Kraus, zeroed
on the outcomes where Alice's and Bob's key strings agree. -/
def realPassDifferKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun k =>
    if siftedKeyStringsDiffer peSel ec k.2 then
      Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k
    else 0

open scoped Classical in
/-- **Differ-restricted general-`m` ideal pass Kraus family.** -/
def idealPassDifferKraus (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Signals n × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E)
        (Signals n × E) ℂ :=
  fun k =>
    if siftedKeyStringsDiffer peSel ec k.1 then
      Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k
    else 0

/-- Adjoint product of a differ-restricted general-`m` real pass Kraus operator: the input-outcome
projector on the branch where the strings differ AND the full `PE ∧ EV` test accepts.  The differ
conjunct passes straight through
`Announced.passKraus_conjTranspose_mul_self`. -/
lemma realPassDifferKraus_conjTranspose_mul_self (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n) :
    (realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)ᴴ *
        realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k =
      if siftedKeyStringsDiffer peSel ec k.2 &&
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
        Matrix.single k.2 k.2 1 ⊗ₖ (1 : Op E)
      else 0 := by
  classical
  by_cases h : siftedKeyStringsDiffer peSel ec k.2 = true
  · simp only [realPassDifferKraus, h, ite_true, Bool.true_and]
    convert Announced.passKraus_conjTranspose_mul_self E n m ℓ ℓEV peSel xSel
      leakEC ec δ Q k.1 k.2 using 1
    split_ifs <;> ext i j <;> simp [Matrix.one_apply]
  · simp [realPassDifferKraus, h]

/-- Adjoint product of a differ-restricted general-`m` ideal pass Kraus operator. -/
lemma idealPassDifferKraus_conjTranspose_mul_self (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (k : Signals n × Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)ᴴ *
        idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k =
      if siftedKeyStringsDiffer peSel ec k.1 &&
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        Matrix.single k.1 k.1 1 ⊗ₖ (1 : Op E)
      else 0 := by
  classical
  by_cases h : siftedKeyStringsDiffer peSel ec k.1 = true
  · simp only [idealPassDifferKraus, h, ite_true, Bool.true_and]
    convert Announced.idealPassKraus_conjTranspose_mul_self E n m ℓ ℓEV peSel xSel
      leakEC ec δ Q k.1 k.2.1 k.2.2 using 1
    split_ifs <;> ext i j <;> simp [Matrix.one_apply]
  · simp [idealPassDifferKraus, h]

/-!
## The general-`m` base-scheme pass channels

The general-`m` mirrors of `bb84SiftedPEAnnounceEveVisible{Real,Ideal}PassChannel`
(`AnnouncedChannels.lean`) restricted to the differ branch, with the binder shape of the
general-`m` agree channels (`InnerBudgetAgreeBlock.lean`).
-/

open scoped Classical in
/-- **General-`m` base-scheme real DIFFER pass channel**: the accept branch of the general-`m`
real PA/abort map restricted to the outcomes where Alice's and Bob's key strings differ. -/
noncomputable def announcedEveRealDiffer
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMap (realPassDifferKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

open scoped Classical in
/-- **General-`m` base-scheme ideal DIFFER pass channel.** -/
noncomputable def announcedEveIdealDiffer
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMap (idealPassDifferKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

open scoped Classical in
/-- **General-`m` base-scheme real pass channel**: the accept branch of the general-`m` real
PA/abort map (uniform seed-pair average) after the computational measurement and the LOCC attack
channel. -/
noncomputable def announcedEveRealPass
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMap (Announced.passKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

open scoped Classical in
/-- **General-`m` base-scheme ideal pass channel**: the fresh-uniform-key accept branch of the
general-`m` ideal key/abort map. -/
noncomputable def announcedEveIdealPass
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Operation (Signals n)
      (KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMap (Announced.idealPassKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)).comp
    ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
      (siftedConjAfterPre E pre peSel xSel))

open scoped Classical in
/-- General-`m` base-scheme real pass output at the CKR reference state `τ`. -/
noncomputable def siftedPEAnnounceEveVisibleRealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    Op ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :=
  mapTensorId (announcedEveRealPass E (m := m) ℓ ℓEV pre
    peSel xSel leakEC ec Q δ) R τ.toOp

open scoped Classical in
/-- General-`m` base-scheme ideal pass output at the CKR reference state `τ`. -/
noncomputable def siftedPEAnnounceEveVisibleIdealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    Op ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :=
  mapTensorId (announcedEveIdealPass E (m := m) ℓ ℓEV pre
    peSel xSel leakEC ec Q δ) R τ.toOp

omit [DecidableEq E] in
/-- **The general-`m` base channels differ only by their pass branches** (the shared-fail-branch
cancellation, D5).  The general-`m` fail Kraus family is literally the same object in the real and
in the ideal map, at the same seed-pair scale, so it cancels in the difference. -/
theorem _root_.QKD.BB84.Model.Announced.WithEve.real_sub_ideal_eq_pass_sub
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
        (E := E) -
      (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).idealProtocolMap
        (E := E)).comp
      (siftedConjAfterPre E pre peSel xSel)) =
      announcedEveRealPass E (m := m) ℓ ℓEV pre peSel xSel leakEC
          ec Q δ -
        announcedEveIdealPass E (m := m) ℓ ℓEV pre peSel xSel
            leakEC ec Q δ := by
  classical
  simp only [siftedPEAnnounceEveVisibleProtocol,
    Announced.real_eq_krausMap, Announced.ideal_eq_krausMap,
    announcedEveRealPass, announcedEveIdealPass, one_div]
  ext M i j
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Matrix.sub_apply]
  change ((_ : ℂ) + _) - (_ + _) = _ - _
  abel

omit [DecidableEq E] in
/-- The general-`m` real pass channel is completely positive. -/
theorem isCompletelyPositive_announcedEveRealPass
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveRealPass E (m := m) ℓ ℓEV pre peSel xSel
          leakEC ec Q δ)) := by
  classical
  unfold announcedEveRealPass
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

omit [DecidableEq E] in
/-- The general-`m` ideal pass channel is completely positive. -/
theorem isCompletelyPositive_announcedEveIdealPass
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveIdealPass E (m := m) ℓ ℓEV pre peSel xSel
          leakEC ec Q δ)) := by
  classical
  unfold announcedEveIdealPass
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

omit [DecidableEq E] in
/-- The general-`m` real pass output is positive semidefinite. -/
theorem posSemidef_siftedPEAnnounceEveVisibleRealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (siftedPEAnnounceEveVisibleRealPassOutput E (m := m) ℓ ℓEV pre peSel xSel leakEC
      ec Q δ τ).PosSemidef := by
  classical
  exact (isCompletelyPositive_announcedEveRealPass E (m := m) ℓ ℓEV pre hpre
    peSel xSel leakEC ec Q δ).mapTensorId.posSemidef τ.posSemidef

omit [DecidableEq E] in
/-- The general-`m` ideal pass output is positive semidefinite. -/
theorem posSemidef_siftedPEAnnounceEveVisibleIdealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (siftedPEAnnounceEveVisibleIdealPassOutput E (m := m) ℓ ℓEV pre peSel xSel leakEC
      ec Q δ τ).PosSemidef := by
  classical
  exact (isCompletelyPositive_announcedEveIdealPass E (m := m) ℓ ℓEV pre hpre
    peSel xSel leakEC ec Q δ).mapTensorId.posSemidef τ.posSemidef

/-- **The general-`m` real pass-output trace is at most the τ-side accept weight.**  The pass
channel's accept test is `PE ∧ EV`, the weight functional's is `PE` alone, so the seed-pair average
of the accept-gated block sum is dominated termwise by the PE-gated one; the uniform seed-pair scale
then cancels exactly.  The right-hand side is the UNCHANGED, `m`-free
`siftedEveVisiblePEPassWeight`. -/
theorem realPassOutput_trace_re_le_tauLocalPEAcceptedWeight
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (siftedPEAnnounceEveVisibleRealPassOutput E (m := m) ℓ ℓEV pre peSel xSel leakEC
        ec Q δ τ).trace.re ≤
      siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ := by
  classical
  set W : ℝ := siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ with
      hW
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by
    rw [hcard]; exact_mod_cast Fintype.card_pos
  have htrace :=
    trace_passOutput_eq_sum_ite E pre hpre peSel xSel
      (K := Announced.passKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)
      (c := 1 / (card : ℂ))
      (gate := fun k => siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2)
      (ωof := fun k => k.2)
      (fun k => by
        convert Announced.passKraus_conjTranspose_mul_self E n m ℓ ℓEV
          peSel xSel leakEC ec δ Q k.1 k.2 using 1
        split_ifs <;> ext i j <;> simp [Matrix.one_apply])
      τ
  rw [siftedPEAnnounceEveVisibleRealPassOutput,
    announcedEveRealPass, ← hcard, htrace]
  rw [show (∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          (((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / (card : ℂ)) = (((1 : ℝ) / (card : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum_eq : ∑ ω : Signals n,
      (if siftedLocalPETestPassed peSel xSel δ Q ω then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace : ℝ) else 0)
            = W := by
    rw [hW, siftedEveVisiblePEPassWeight_eq_sum_marginal]
  have hstep : ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
      (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ)
        else 0) ≤ (card : ℝ) * W := by
    calc ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
          (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
            ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ)
                else 0)
           ≤ ∑ _k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
            (if siftedLocalPETestPassed peSel xSel δ Q _k.2 then
              ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight _k.2).trace : ℝ)
              else 0) :=
          Finset.sum_le_sum (fun k _ =>
            ite_peAndEVPassed_le_ite_pePassed E pre hpre ℓEV peSel xSel ec Q δ τ.partialTraceRight
                k.1.2 k.2)
      _ = ∑ _st : KeyHashSeedPairEV n ℓ ℓEV peSel, ∑ ω : Signals n,
            (if siftedLocalPETestPassed peSel xSel δ Q ω then
              ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace : ℝ)
                  else 0) :=
          Fintype.sum_prod_type _
      _ = (card : ℝ) * W := by
          rw [hsum_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcard]
  calc (1 : ℝ) / (card : ℝ) *
        ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
          (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
            ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ)
                else 0)
         ≤ (1 : ℝ) / (card : ℝ) * ((card : ℝ) * W) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = W := by field_simp

/-- **The general-`m` ideal pass-output trace is at most the τ-side accept weight.**  Same
argument as the real arm: the ideal pass Kraus family carries the same `PE ∧ EV` test and the same
input-outcome projectors, and its fresh-key/seed-pair scale `1/(2^ℓ·|ST|)` cancels the `2^ℓ·|ST|`
multiplicity of the test-indicator sum exactly. -/
theorem idealPassOutput_trace_re_le_tauLocalPEAcceptedWeight
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (siftedPEAnnounceEveVisibleIdealPassOutput E (m := m) ℓ ℓEV pre peSel xSel leakEC
        ec Q δ τ).trace.re ≤
      siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ := by
  classical
  set W : ℝ := siftedEveVisiblePEPassWeight E pre hpre peSel xSel Q δ τ with
      hW
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by
    rw [hcard]; exact_mod_cast Fintype.card_pos
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have htrace :=
    trace_passOutput_eq_sum_ite E pre hpre peSel xSel
      (K := Announced.idealPassKraus E n m ℓ ℓEV
        peSel xSel leakEC ec δ Q)
      (c := 1 / ((2 ^ ℓ : ℂ) * (card : ℂ)))
      (gate := fun k => siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1)
      (ωof := fun k => k.1)
      (fun k => by
        convert Announced.idealPassKraus_conjTranspose_mul_self E n m ℓ ℓEV
          peSel xSel leakEC ec δ Q k.1 k.2.1 k.2.2 using 1
        split_ifs <;> ext i j <;> simp [Matrix.one_apply])
      τ
  rw [siftedPEAnnounceEveVisibleIdealPassOutput,
    announcedEveIdealPass, ← hcard, htrace]
  rw [show (∑ k : Signals n × Bits ℓ ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          (((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : Signals n × Bits ℓ ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / ((2 ^ ℓ : ℂ) * (card : ℂ))) =
      (((1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum_eq : ∑ ω : Signals n,
      (if siftedLocalPETestPassed peSel xSel δ Q ω then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace : ℝ) else 0)
            = W := by
    rw [hW, siftedEveVisiblePEPassWeight_eq_sum_marginal]
  have hstep : ∑ k : Signals n × Bits ℓ ×
        KeyHashSeedPairEV n ℓ ℓEV peSel,
      (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ)
        else 0) ≤ ((2 : ℝ) ^ ℓ * (card : ℝ)) * W := by
    calc ∑ k : Signals n × Bits ℓ ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
          (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
            ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ)
                else 0)
           ≤ ∑ _k : Signals n × Bits ℓ ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
            (if siftedLocalPETestPassed peSel xSel δ Q _k.1 then
              ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight _k.1).trace : ℝ)
              else 0) :=
          Finset.sum_le_sum (fun k _ =>
            ite_peAndEVPassed_le_ite_pePassed E pre hpre ℓEV peSel xSel ec Q δ τ.partialTraceRight
                k.2.2.2 k.1)
      _ = ∑ ω : Signals n,
            ∑ _y : Bits ℓ × KeyHashSeedPairEV n ℓ ℓEV peSel,
            (if siftedLocalPETestPassed peSel xSel δ Q ω then
              ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace : ℝ)
                  else 0) :=
          Fintype.sum_prod_type _
      _ = ((2 : ℝ) ^ ℓ * (card : ℝ)) * W := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Bits,
            Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hcard]
          rw [hsum_eq]
          push_cast
          ring
  calc (1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) *
        ∑ k : Signals n × Bits ℓ ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
          (if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
            ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ)
                else 0)
         ≤ (1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) * (((2 : ℝ) ^ ℓ * (card : ℝ)) * W) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = W := by field_simp

omit [DecidableEq E] in
/-- **The general-`m` base difference is the real-minus-ideal pass output.**  The general-`m` fail
Kraus family is the same object at the same scale in both maps (D5), so it cancels after tensoring
with the CKR reference. -/
theorem _root_.QKD.BB84.Model.Announced.WithEve.mapTensorId_sub_eq_pass_sub
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    mapTensorId
        (((siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).realProtocolMap
        (E := E) -
          (siftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
              Q δ).idealProtocolMap
        (E := E)).comp
          (siftedConjAfterPre E pre peSel xSel)) R τ.toOp =
      siftedPEAnnounceEveVisibleRealPassOutput E (m := m) ℓ ℓEV pre peSel xSel leakEC
          ec Q δ τ -
        siftedPEAnnounceEveVisibleIdealPassOutput E (m := m) ℓ ℓEV pre peSel xSel
            leakEC ec Q δ τ := by
  classical
  rw [QKD.BB84.Model.Announced.WithEve.real_sub_ideal_eq_pass_sub]
  exact LinearMap.congr_fun (mapTensorId_sub _ _) τ.toOp

/-! ## The general-`m` agree/differ split and the differ-block correctness charge -/

omit [DecidableEq E] in
private lemma realPassKraus_split {n : ℕ} (m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMap (Announced.passKraus E n m ℓ ℓEV peSel xSel
        leakEC ec δ Q) =
      krausMap (realPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) +
        krausMap (realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) := by
  classical
  refine krausMap_eq_add_of_sandwich_eq_add _ _ _ (fun k A => ?_)
  by_cases h : siftedKeyStringsDiffer peSel ec k.2 = true <;>
    simp [realPassAgreeKraus, realPassDifferKraus, h]

omit [DecidableEq E] in
private lemma idealPassKraus_split {n : ℕ} (m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMap (Announced.idealPassKraus E n m ℓ ℓEV peSel xSel
        leakEC ec δ Q) =
      krausMap (idealPassAgreeKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) +
        krausMap (idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q) := by
  classical
  refine krausMap_eq_add_of_sandwich_eq_add _ _ _ (fun k A => ?_)
  by_cases h : siftedKeyStringsDiffer peSel ec k.1 = true <;>
    simp [idealPassAgreeKraus, idealPassDifferKraus, h]

omit [DecidableEq E] in
/-- **The general-`m` real pass channel is the sum of its agree and differ blocks.** -/
theorem announcedEveRealPass_eq_agree_add_differ
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    announcedEveRealPass E (m := m) ℓ ℓEV pre peSel xSel leakEC
        ec Q δ =
      announcedEveRealAgree E (m := m) ℓ ℓEV pre peSel xSel
          leakEC ec Q δ +
        announcedEveRealDiffer E (m := m) ℓ ℓEV pre peSel
            xSel leakEC
          ec Q δ := by
  classical
  rw [announcedEveRealPass,
    announcedEveRealAgree,
    announcedEveRealDiffer,
    realPassKraus_split, smul_add, LinearMap.add_comp]

omit [DecidableEq E] in
/-- **The general-`m` ideal pass channel is the sum of its agree and differ blocks.** -/
theorem announcedEveIdealPass_eq_agree_add_differ
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    announcedEveIdealPass E (m := m) ℓ ℓEV pre peSel xSel leakEC
        ec Q δ =
      announcedEveIdealAgree E (m := m) ℓ ℓEV pre peSel xSel
          leakEC ec Q δ +
        announcedEveIdealDiffer E (m := m) ℓ ℓEV pre peSel
            xSel leakEC
          ec Q δ := by
  classical
  rw [announcedEveIdealPass,
    announcedEveIdealAgree,
    announcedEveIdealDiffer,
    idealPassKraus_split, smul_add, LinearMap.add_comp]

/-- **The general-`m` real differ-block pass-output TRACE IDENTITY**: the trace of the differ block
of the real pass output on the CKR reference `τ` is EXACTLY the differ-and-accept weight of the
attacked marginal `τ.partialTraceRight`.

Equality, not an inequality: the accept-gated trace formula collapses the single-entry Kraus family
onto the test-indicated outcome projectors, and the uniform seed-pair scale `1/|ST|` cancels the
`|ST|`-fold multiplicity exactly.  The right-hand side is the UNCHANGED, `m`-free
`siftedEveVisibleDifferAcceptWeight`. -/
theorem realDifferPassOutput_trace_re_eq_differAndAcceptWeight
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (mapTensorId
      (announcedEveRealDiffer E (m := m) ℓ ℓEV pre peSel xSel
          leakEC ec Q δ)
      R τ.toOp).trace.re =
      siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceRight := by
  classical
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by rw [hcard]; exact_mod_cast Fintype.card_pos
  have htrace :=
    trace_passOutput_eq_sum_ite E pre hpre peSel xSel
      (K := realPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (c := 1 / (card : ℂ))
      (gate := fun k => siftedKeyStringsDiffer peSel ec k.2 &&
        siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2)
      (ωof := fun k => k.2)
      (fun k => realPassDifferKraus_conjTranspose_mul_self E n m ℓ ℓEV peSel xSel
        leakEC ec δ Q k)
      τ
  rw [announcedEveRealDiffer, ← hcard, htrace]
  rw [show (∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
        (if siftedKeyStringsDiffer peSel ec k.2 &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          (((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × Signals n,
        (if siftedKeyStringsDiffer peSel ec k.2 &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.2).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / (card : ℂ)) = (((1 : ℝ) / (card : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    sum_sum_ite_differAndAccept_eq E ℓ ℓEV pre hpre peSel xSel ec Q δ τ.partialTraceRight, ← hcard]
  field_simp

/-- **The general-`m` ideal differ-block pass-output TRACE IDENTITY.**  Same computation as the
real arm: the ideal pass Kraus family carries the same test and the same input-outcome projectors,
and its fresh-key/seed-pair scale `1/(2^ℓ·|ST|)` cancels the `2^ℓ·|ST|`-fold multiplicity exactly.
-/
theorem idealDifferPassOutput_trace_re_eq_differAndAcceptWeight
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    (mapTensorId
      (announcedEveIdealDiffer E (m := m) ℓ ℓEV pre peSel
          xSel leakEC ec Q δ)
      R τ.toOp).trace.re =
      siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceRight := by
  classical
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by rw [hcard]; exact_mod_cast Fintype.card_pos
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have htrace :=
    trace_passOutput_eq_sum_ite E pre hpre peSel xSel
      (K := idealPassDifferKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q)
      (c := 1 / ((2 ^ ℓ : ℂ) * (card : ℂ)))
      (gate := fun k => siftedKeyStringsDiffer peSel ec k.1 &&
        siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1)
      (ωof := fun k => k.1)
      (fun k => idealPassDifferKraus_conjTranspose_mul_self E n m ℓ ℓEV peSel xSel
        leakEC ec δ Q k)
      τ
  rw [announcedEveIdealDiffer, ← hcard, htrace]
  rw [show (∑ k : Signals n × Bits ℓ ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if siftedKeyStringsDiffer peSel ec k.1 &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          (((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : Signals n × Bits ℓ ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if siftedKeyStringsDiffer peSel ec k.1 &&
            siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / ((2 ^ ℓ : ℂ) * (card : ℂ))) =
      (((1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum : ∑ k : Signals n × Bits ℓ ×
        KeyHashSeedPairEV n ℓ ℓEV peSel,
      (if siftedKeyStringsDiffer peSel ec k.1 &&
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight k.1).trace : ℝ) else
            0) =
      ((2 : ℝ) ^ ℓ * (card : ℝ)) *
        siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceRight := by
    rw [Fintype.sum_prod_prod_eq_card_mul_sum_sum (Ω := Signals n) (A := Bits ℓ)
      (B := KeyHashSeedPairEV n ℓ ℓEV peSel)
      (fun st ω => if siftedKeyStringsDiffer peSel ec ω &&
          siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ((siftedEveConditioned E pre hpre peSel xSel τ.partialTraceRight ω).trace : ℝ) else 0)]
    rw [Fintype.sum_prod_type,
      sum_sum_ite_differAndAccept_eq E ℓ ℓEV pre hpre peSel xSel ec Q δ τ.partialTraceRight, ←
        hcard]
    simp only [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hsum]
  field_simp

omit [DecidableEq E] in
/-- The general-`m` real differ pass channel is completely positive (a nonnegatively-scaled Kraus
map after a CP map — zeroing part of a Kraus family leaves a Kraus family). -/
theorem isCompletelyPositive_announcedEveRealDiffer
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveRealDiffer E (m := m) ℓ ℓEV pre peSel
          xSel leakEC
        ec Q δ)) := by
  classical
  unfold announcedEveRealDiffer
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

omit [DecidableEq E] in
/-- The general-`m` ideal differ pass channel is completely positive. -/
theorem isCompletelyPositive_announcedEveIdealDiffer
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      ((announcedEveIdealDiffer E (m := m) ℓ ℓEV pre peSel
          xSel leakEC
        ec Q δ)) := by
  classical
  unfold announcedEveIdealDiffer
  apply IsCompletelyPositive.comp
  · exact (isCompletelyPositive_krausMap _).smul (by positivity)
  · exact isCompletelyPositive_measurement_comp_siftedConjAfterPre E pre hpre peSel xSel

omit [DecidableEq E] in
/-- **The operator form of the correctness leg at a general test-set size `m`.**  The
differ-and-accept block of `real − ideal` — the sub-block of the general-`m` base-scheme difference
supported on "the two key strings differ AND the protocol accepts" — has CKR tensor trace norm at
most `2·2^(−ℓEV)`, for EVERY attack-free `pre` slot, EVERY reference state `τ`, EVERY
error-correction scheme `ec` and EVERY test-set size `m`.

The scalar input `siftedEveVisibleDifferAcceptWeight_le_two_rpow_neg` (`AnnouncedChannels.lean`) is
`m`-free — it bounds a Born mass of outcome strings and names no output register — so it is reused
at the attacked CKR marginal `τ.partialTraceRight`. The test-set size changes only the output
register; the trace identities above account for that change.

**Stated JOINTLY.**  `InfoTheory.Postselection.ErrorVerification.conditional_correctness_fails`
PROVES that the conditional form `Pr[differ | accept]` is not bounded by `2^(−ℓEV)`, which is why
the charge is additive.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) §V.C, error verification "by comparing hash values
of length log(1/ε_EV)". -/
theorem ckrTraceNorm_announcedEveDiffer_sub_le_two_mul_pow_neg
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    ckrTraceNorm
        (announcedEveRealDiffer E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ -
          announcedEveIdealDiffer E (m := m) ℓ ℓEV pre peSel
              xSel leakEC
            ec Q δ) τ ≤
      2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  classical
  have hRealPSD := (isCompletelyPositive_announcedEveRealDiffer E (m := m) ℓ ℓEV
    pre hpre peSel xSel leakEC ec Q δ).mapTensorId (Z := R) |>.posSemidef τ.posSemidef
  have hIdealPSD := (isCompletelyPositive_announcedEveIdealDiffer E (m := m) ℓ ℓEV
    pre hpre peSel xSel leakEC ec Q δ).mapTensorId (Z := R) |>.posSemidef τ.posSemidef
  have hScalar := siftedEveVisibleDifferAcceptWeight_le_two_rpow_neg E pre hpre ℓEV
    peSel xSel ec Q δ τ.partialTraceRight
  unfold ckrTraceNorm
  rw [mapTensorId_sub, LinearMap.sub_apply]
  calc _ ≤ _ := traceNorm_sub_posSemidef_le _ _ hRealPSD hIdealPSD
       _ = 2 * siftedEveVisibleDifferAcceptWeight E pre hpre ℓEV peSel xSel ec Q δ
           τ.partialTraceRight := by
         rw [Complex.add_re, realDifferPassOutput_trace_re_eq_differAndAcceptWeight (hpre := hpre),
           idealDifferPassOutput_trace_re_eq_differAndAcceptWeight (hpre := hpre)]
         ring
       _ ≤ 2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by linarith

end QKD.BB84.FiniteKey

end
