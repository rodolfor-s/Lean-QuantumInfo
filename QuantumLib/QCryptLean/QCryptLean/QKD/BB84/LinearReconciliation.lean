import QCryptLean.InfoTheory.QuantumLHL.BinaryInnerProductHash
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.HammingBall
import QCryptLean.Math.CodingTheory.SyndromeDecoding
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinarySymmetricTail
import QCryptLean.QKD.BB84.Completeness
import QCryptLean.QKD.BB84.ErrorCorrection

/-!
# Linear reconciliation for the honest BB84 error law

`ECScheme.exists_decode_eq_of_hammingDist_le` corrects an entire Hamming ball using a separating
syndrome. `ECScheme.exists_decodesWhp_linearSyndrome` instead fixes a binary linear hash by
averaging its weighted collisions; `ECScheme.exists_decodesWhp_linearSyndrome_of_entropy`
expresses the collision budget through binary entropy. Translation invariance makes the
probabilistic guarantee uniform over Alice's words. The fixed seed can depend on the error rate;
it is not sampled anew on each execution.

Reference: Renner, quant-ph/0512258, `lem:errcorrsmooth` (main.tex:7765–7775).
-/

open scoped BigOperators

noncomputable section

namespace QKD.BB84.ECScheme

open InfoTheory.QuantumLHL Math.CodingTheory Math.Concentration.BinarySymmetricTail

/-- The decoding failure mass of a coset scheme is independent of Alice's word. -/
lemma coset_failure_mass {n m : ℕ} {peSel : Fin n → Bool}
    (syn : KeyBitString n peSel →+ (Fin m → Fin 2)) (rep : (Fin m → Fin 2) → KeyBitString n peSel)
    (q : ℝ) (a : KeyBitString n peSel) :
    (∑ b, if (coset syn rep).decode b ((coset syn rep).syndrome a) = a then 0
      else Math.Concentration.BinarySymmetricTail.bscWeight q a b) =
    ∑ e, if rep (syn e) = e then 0
      else Math.Concentration.BinarySymmetricTail.bscWeight q 0 e := by
  classical
  rw [← (Equiv.subLeft a).sum_comp]
  simp only [Equiv.subLeft_apply, coset_decode_eq_iff, sub_sub_cancel,
    bscWeight_self_sub_right]

/-- A syndrome alphabet larger than the radius-`2t` ball admits a translation-equivariant
scheme correcting every pair of words at Hamming distance at most `t`. -/
theorem exists_decode_eq_of_hammingDist_le (n : ℕ) (peSel : Fin n → Bool) (t leakEC : ℕ)
    (hvol : ((Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ 2 * t)).card :
      ℝ) < (2 : ℝ) ^ leakEC) :
    ∃ ec : ECScheme n peSel leakEC, ec.IsTranslationEquivariant ∧
      ∀ a b, hammingDist a b ≤ t → ec.decode b (ec.syndrome a) = a := by
  classical
  obtain ⟨A, hA⟩ := exists_binaryInnerProductSyndrome_separating _ hvol
  let syn := binaryInnerProductSyndrome A
  have hsep : ∀ e : KeyBitString n peSel,
      hammingDist e 0 ≤ 2 * t → syn e = 0 → e = 0 := fun e he hs =>
    hA e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩) hs
  let T := Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ t)
  let rep : (Fin leakEC → Fin 2) → KeyBitString n peSel := fun s =>
    if h : ∃ e ∈ T, syn e = s then h.choose else 0
  have hrep (e : KeyBitString n peSel) (he : e ∈ T) :
      rep (syn e) ∈ T ∧ syn (rep (syn e)) = syn e := by
    have h : ∃ f ∈ T, syn f = syn e := ⟨e, he, rfl⟩
    simpa only [rep, dite_eq_left h] using h.choose_spec
  refine ⟨coset syn rep, coset_isTranslationEquivariant _ _, ?_⟩
  intro a b hab
  apply (coset_decode_eq_iff syn rep a b).mpr
  apply syndromeRepresentative_eq_of_hamming_separation syn t rep
    (fun e he => (hrep e he).1) (fun e he => (hrep e he).2) hsep
  rw [hammingDist_zero_right, sub_eq_neg_add, ← hammingDist_eq_hammingNorm, hammingDist_comm]
  exact hab

/-- The shared coset construction of the two reconciliation guarantees: a binary linear syndrome
whose representative fixes every error of Hamming weight ≤ `t` decodes the honest BSC law with
failure mass at most the honest ball-failure mass `r` plus the collision volume
`V(n_K, t)/2^leakEC` (`syndromeRepresentative_failure_le`,
`exists_binaryInnerProductSyndrome_collision_le`).  Translation invariance makes the guarantee
uniform over Alice's words. -/
private lemma exists_decodesWhp_coset_of_ball_compl_le (n : ℕ) (q : ℝ)
    (peSel xSel : Fin n → Bool) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t leakEC : ℕ) (r : ℝ)
    (hball : (∑ b : KeyBitString n peSel,
        if hammingDist 0 b ≤ t then
          (0 : ℝ) else Math.Concentration.BinarySymmetricTail.bscWeight q 0 b) ≤ r) :
    ∃ ec : ECScheme n peSel leakEC,
      ec.DecodesWhp (honestKeyErrWeight n q peSel xSel)
        (r + (Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ t)).card /
          (2 : ℝ) ^ leakEC) ∧
      ec.IsTranslationEquivariant := by
  simp only [honestKeyErrWeight_eq_bscWeight]
  let T := Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ t)
  let w := Math.Concentration.BinarySymmetricTail.bscWeight q (0 : KeyBitString n peSel)
  have hw := Math.Concentration.BinarySymmetricTail.bscWeight_nonneg hq0 hq1
    (0 : KeyBitString n peSel)
  obtain ⟨A, hA⟩ := exists_binaryInnerProductSyndrome_collision_le (m := leakEC) T w hw
    (sum_bscWeight q 0).le
  let syn := binaryInnerProductSyndrome A
  classical
  let rep : (Fin leakEC → Fin 2) → KeyBitString n peSel := fun s =>
    if h : ∃ e ∈ T, syn e = s then h.choose else 0
  have hrep (e : KeyBitString n peSel) (he : e ∈ T) :
      rep (syn e) ∈ T ∧ syn (rep (syn e)) = syn e := by
    have h : ∃ f ∈ T, syn f = syn e := ⟨e, he, rfl⟩
    simpa only [rep, dite_eq_left h] using h.choose_spec
  refine ⟨coset syn rep, fun a => ?_,
    coset_isTranslationEquivariant _ _⟩
  rw [coset_failure_mass]
  refine (syndromeRepresentative_failure_le syn T rep
    (fun e he => (hrep e he).1) (fun e he => (hrep e he).2) w hw).trans (add_le_add ?_ hA)
  simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist_comm] using hball

/-- A fixed linear coset decoder attains the radius-`t` collision budget plus the honest tail.

Averaging the error-weighted collision count over binary linear maps produces one seed.
Translation invariance makes its failure probability identical for every Alice word, so neither
expurgation nor a union over Alice words is needed. The added failure term is `V(n_K,t)/2^leakEC`;
thus `leakEC ≥ n_K*h₂(t/n_K) + log₂(1/κ)` suffices for collision budget `κ` when `t/n_K ≤ 1/2`.
This is Renner's tail-plus-collision argument (`lem:errcorrsmooth`, main.tex:7765–7775),
specialized to the additive BSC law and a fixed linear syndrome. -/
theorem exists_decodesWhp_linearSyndrome (n : ℕ) (q ε : ℝ) (peSel xSel : Fin n → Bool)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε) (t leakEC : ℕ)
    (hgate : (q + ε) * (Fintype.card {i : Fin n // peSel i = false} : ℝ) < (t + 1 : ℝ)) :
    ∃ ec : ECScheme n peSel leakEC,
      ec.DecodesWhp (honestKeyErrWeight n q peSel xSel)
        (Real.exp (-2 * (Fintype.card {i : Fin n // peSel i = false} : ℝ) * ε ^ 2) +
          (Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ t)).card /
            (2 : ℝ) ^ leakEC) ∧ ec.IsTranslationEquivariant :=
  exists_decodesWhp_coset_of_ball_compl_le n q peSel xSel hq0 hq1 t leakEC
    (Real.exp (-2 * (Fintype.card {i : Fin n // peSel i = false} : ℝ) * ε ^ 2))
    (bscWeight_ball_compl_le hq0 hq1 hε 0 t hgate)

/-- A fixed linear coset decoder attains the radius-`t` collision budget plus the honest decoding
tail at the KL (Chernoff) rate.

Sharper analogue of `exists_decodesWhp_linearSyndrome` (which prices the tail at the Hoeffding
rate `exp(−2·n_K·ε²)` and needs a margin `ε`): here the tail is
`exp(−n_K·klBer ((t+1)/n_K) q)` for `q·n_K < t + 1 ≤ n_K`, with no margin (Cover–Thomas,
*Elements of Information Theory*, §11.1).  `q < 1` is not a hypothesis: it follows from the
test and the radius bound. -/
theorem exists_decodesWhp_linearSyndrome_le_exp_klBer (n : ℕ) (q : ℝ)
    (peSel xSel : Fin n → Bool) (hq0 : 0 < q) (t leakEC : ℕ)
    (hgate : q * (Fintype.card {i : Fin n // peSel i = false} : ℝ) < (t + 1 : ℝ))
    (hball : (t + 1 : ℝ) ≤ (Fintype.card {i : Fin n // peSel i = false} : ℝ)) :
    ∃ ec : ECScheme n peSel leakEC,
      ec.DecodesWhp (honestKeyErrWeight n q peSel xSel)
        (Real.exp (-(Fintype.card {i : Fin n // peSel i = false} : ℝ) *
            Math.Concentration.BernoulliKL.klBer
              ((t + 1 : ℝ) / Fintype.card {i : Fin n // peSel i = false}) q) +
          (Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ t)).card /
            (2 : ℝ) ^ leakEC) ∧ ec.IsTranslationEquivariant := by
  -- `q < 1` follows from `q · N < t + 1 ≤ N` (and `N > 0` for the same reason).
  have hNpos : (0 : ℝ) < (Fintype.card {i : Fin n // peSel i = false} : ℝ) := by
    have h1 : (0 : ℝ) < (t + 1 : ℝ) := by positivity
    linarith
  have hq1 : q ≤ 1 := by
    have hlt : q * (Fintype.card {i : Fin n // peSel i = false} : ℝ) <
        (Fintype.card {i : Fin n // peSel i = false} : ℝ) := lt_of_lt_of_le hgate hball
    have hq : q < (Fintype.card {i : Fin n // peSel i = false} : ℝ) /
        (Fintype.card {i : Fin n // peSel i = false} : ℝ) := (lt_div_iff₀ hNpos).mpr hlt
    rw [div_self hNpos.ne'] at hq
    linarith
  exact exists_decodesWhp_coset_of_ball_compl_le n q peSel xSel hq0.le hq1 t leakEC
    (Real.exp (-(Fintype.card {i : Fin n // peSel i = false} : ℝ) *
      Math.Concentration.BernoulliKL.klBer
        ((t + 1 : ℝ) / Fintype.card {i : Fin n // peSel i = false}) q))
    (bscWeight_ball_compl_le_exp_neg_mul_klBer hq0 0 t hgate hball)

/-- Entropy-order reconciliation costs `s` additional syndrome bits for collision failure `2⁻ˢ`. -/
theorem exists_decodesWhp_linearSyndrome_of_entropy (n : ℕ) (q ε r : ℝ)
    (peSel xSel : Fin n → Bool) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε)
    (t leakEC s : ℕ)
    (hgate : (q + ε) * (Fintype.card {i : Fin n // peSel i = false} : ℝ) < (t + 1 : ℝ))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (ht : (t : ℝ) ≤ r * Fintype.card {i : Fin n // peSel i = false})
    (hleak : (Fintype.card {i : Fin n // peSel i = false} : ℝ) *
      Math.ClassicalEntropy.binaryEntropyBits r + s ≤ leakEC) :
    ∃ ec : ECScheme n peSel leakEC,
      ec.DecodesWhp (honestKeyErrWeight n q peSel xSel)
        (Real.exp (-2 * (Fintype.card {i : Fin n // peSel i = false} : ℝ) * ε ^ 2) +
          1 / (2 : ℝ) ^ s) ∧ ec.IsTranslationEquivariant := by
  obtain ⟨ec, hdec, heq⟩ := exists_decodesWhp_linearSyndrome n q ε peSel xSel
    hq0 hq1 hε t leakEC hgate
  have hcollision :=
    Math.ClassicalEntropy.card_filter_hammingDist_le_div_two_pow_le_of_entropy
      t leakEC s r hr0 hr1 ht hleak
  simp only [← one_div] at hcollision
  exact ⟨ec, fun a => (hdec a).trans (add_le_add le_rfl hcollision), heq⟩

/-- Entropy-order reconciliation at the KL (Chernoff) rate: `s` additional syndrome bits buy
collision failure `2⁻ˢ`, and the honest decoding tail is priced at the relative-entropy rate
`exp(−n_K·klBer ((t+1)/n_K) q)` instead of the Hoeffding rate (Cover–Thomas, *Elements of
Information Theory*, §11.1). -/
theorem exists_decodesWhp_of_entropy_le (n : ℕ) (q r : ℝ)
    (peSel xSel : Fin n → Bool) (hq0 : 0 < q)
    (t leakEC s : ℕ)
    (hgate : q * (Fintype.card {i : Fin n // peSel i = false} : ℝ) < (t + 1 : ℝ))
    (hball : (t + 1 : ℝ) ≤ (Fintype.card {i : Fin n // peSel i = false} : ℝ))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (ht : (t : ℝ) ≤ r * Fintype.card {i : Fin n // peSel i = false})
    (hleak : (Fintype.card {i : Fin n // peSel i = false} : ℝ) *
      Math.ClassicalEntropy.binaryEntropyBits r + s ≤ leakEC) :
    ∃ ec : ECScheme n peSel leakEC,
      ec.DecodesWhp (honestKeyErrWeight n q peSel xSel)
        (Real.exp (-(Fintype.card {i : Fin n // peSel i = false} : ℝ) *
            Math.Concentration.BernoulliKL.klBer
              ((t + 1 : ℝ) / Fintype.card {i : Fin n // peSel i = false}) q) +
          1 / (2 : ℝ) ^ s) ∧ ec.IsTranslationEquivariant := by
  obtain ⟨ec, hdec, heq⟩ := exists_decodesWhp_linearSyndrome_le_exp_klBer n q peSel xSel
    hq0 t leakEC hgate hball
  have hcollision :=
    Math.ClassicalEntropy.card_filter_hammingDist_le_div_two_pow_le_of_entropy
      t leakEC s r hr0 hr1 ht hleak
  simp only [← one_div] at hcollision
  exact ⟨ec, fun a => (hdec a).trans (add_le_add le_rfl hcollision), heq⟩

end QKD.BB84.ECScheme
