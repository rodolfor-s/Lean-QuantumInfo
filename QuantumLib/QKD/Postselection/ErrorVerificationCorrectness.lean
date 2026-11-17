import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-! # Error Verification Correctness -/


open scoped BigOperators

namespace InfoTheory.Postselection.ErrorVerification

variable {S T : Type*}


/-- The collision probability of a **uniformly random seed** on the fixed pair
    `(a, b)`, for a seed-indexed hash family `h : Sd → S → T`:

        Pr_{s ∼ Unif(Sd)}[h s a = h s b] = |{s : h s a = h s b}| / |Sd|.

    This is the seed-indexed counterpart of `collisionProb`; the average is over
    the seed type `Sd`, which is the randomness the protocol actually samples. -/
noncomputable def collisionProbIdx {S T Sd : Type*} [Fintype Sd] [DecidableEq T]
    (h : Sd → S → T) (a b : S) : ℝ :=
  ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) / Fintype.card Sd

/-- On distinct inputs, a seed-indexed family satisfying the δ-almost-universal-2
    counting bound has collision probability at most `δ`.  This is the
    seed-indexed counterpart of `collisionProb_le_delta`: the counting hypothesis
    `|{s : h s a = h s b}| ≤ δ · |Sd|` divided through by the (positive)
    seed count. -/
lemma collisionProbIdx_le_delta {S T Sd : Type*} [Fintype Sd] [Nonempty Sd] [DecidableEq T]
    (h : Sd → S → T) {δ : ℝ}
    (hAU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) ≤ δ * Fintype.card Sd)
    {a b : S} (hab : a ≠ b) :
    collisionProbIdx h a b ≤ δ := by
  have hcard : (0 : ℝ) < Fintype.card Sd := by
    exact_mod_cast Fintype.card_pos (α := Sd)
  rw [collisionProbIdx, div_le_iff₀ hcard]
  exact hAU a b hab

/-- The **joint** probability that the keys differ *and* seed-indexed error
    verification accepts:  `Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)]`, taken over the
    joint law `p` of `(S_A, S_B)` and an independent uniform seed `s ∼ Unif(Sd)`.

    Independence of `(S_A, S_B)` from the seed factors this pairwise into
    `Σ_{a ≠ b} p(a, b) · Pr_s[h s a = h s b]`, the seed-indexed counterpart of
    `jointDifferAcceptProb`. -/
noncomputable def jointDifferAcceptProbIdx {S T Sd : Type*} [Fintype S] [DecidableEq S]
    [Fintype Sd] [DecidableEq T] (p : S × S → ℝ) (h : Sd → S → T) : ℝ :=
  ∑ ab : S × S, if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0

/-- **Error-verification correctness, seed-indexed joint form.**

    For a seed-indexed hash family `h : Sd → S → T` whose collision counts obey
    the δ-almost-universal-2 bound `|{s : h s a = h s b}| ≤ δ · |Sd|` on distinct
    inputs, a uniformly random seed, and *any* joint weight `p` of `(S_A, S_B)` —
    including the adversarial, worst-case laws of the review — the joint
    probability that the keys differ and error verification nonetheless accepts
    is at most `δ`:

        Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)] ≤ δ.

    This is `errorVerification_joint_correctness` with the uniform average taken
    over seeds rather than over a `Finset` of functions, which is the form a
    concrete seed-indexed family (e.g. the BB84 hash family) supplies directly.

    **The sub-normalised mass hypothesis is deliberate.**  The weight `p` is
    required only to be nonnegative with `∑ ab, p ab ≤ 1`, *not* to be a
    normalised distribution (`IsJointDist`, which demands `∑ ab, p ab = 1`).  A
    quantum protocol hands this lemma the *accept-branch* weight — the joint law
    of `(S_A, S_B)` restricted to the parameter-estimation-passing outcomes —
    which is sub-normalised, its deficit being the abort probability.  Requiring
    equality would make the bound unusable at that call site.  The bound is
    monotone in the total mass, so the sub-normalised form is strictly stronger
    and costs nothing: do not "tidy" it back to `IsJointDist`.

    Security review, arXiv:2502.10340, §5.4.6. -/
theorem errorVerification_joint_correctness_indexed
    {S T Sd : Type*} [Fintype S] [DecidableEq S] [DecidableEq T] [Fintype Sd] [Nonempty Sd]
    (h : Sd → S → T) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) ≤ δ * Fintype.card Sd)
    {p : S × S → ℝ} (hp_nonneg : ∀ ab, 0 ≤ p ab) (hp_total : ∑ ab, p ab ≤ 1) :
    jointDifferAcceptProbIdx p h ≤ δ := by
  unfold jointDifferAcceptProbIdx
  -- Bound each term:  [a≠b] · p(a,b) · collisionProbIdx ≤ δ · p(a,b).
  have hterm : ∀ ab : S × S,
      (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0) ≤ δ * p ab := by
    intro ab
    split_ifs with hab
    · calc p ab * collisionProbIdx h ab.1 ab.2
          ≤ p ab * δ := by
            exact mul_le_mul_of_nonneg_left (collisionProbIdx_le_delta h hAU hab) (hp_nonneg ab)
        _ = δ * p ab := mul_comm _ _
    · exact mul_nonneg hδ (hp_nonneg ab)
  calc ∑ ab : S × S, (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0)
      ≤ ∑ ab : S × S, δ * p ab := Finset.sum_le_sum (fun ab _ => hterm ab)
    _ = δ * ∑ ab : S × S, p ab := by rw [Finset.mul_sum]
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hp_total hδ
    _ = δ := mul_one δ

/-- **Strongly-universal seed-indexed corollary.**

    If the seed-indexed family `h` is (exactly) universal — on distinct inputs at
    most a `1/|T|` fraction of the seeds collide, i.e.
    `|{s : h s a = h s b}| ≤ |Sd| / |T|`, which is the defining property of a
    universal hash family as stated seed-indexed — then the joint differ-and-
    accept probability is bounded by the reciprocal of the tag-space size:

        Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)] ≤ 1 / |T|.

    For `T` the `t`-bit tags this is the standard error-verification correctness
    parameter `ε_cor = 2^{-t}`.  It is the seed-indexed counterpart of
    `errorVerification_joint_correctness_strong`, obtained by rewriting
    `|Sd| / |T| = (1 / |T|) · |Sd|` and applying
    `errorVerification_joint_correctness_indexed` at `δ = 1 / |T|`.  As there,
    the weight `p` is only required to be sub-normalised (`∑ ab, p ab ≤ 1`), the
    form a quantum accept branch supplies. -/
theorem errorVerification_joint_correctness_indexed_of_universal
    {S T Sd : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Fintype Sd] [Nonempty Sd] (h : Sd → S → T)
    (hU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ)
        ≤ (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ))
    {p : S × S → ℝ} (hp_nonneg : ∀ ab, 0 ≤ p ab) (hp_total : ∑ ab, p ab ≤ 1) :
    jointDifferAcceptProbIdx p h ≤ 1 / Fintype.card T := by
  have hδ : (0 : ℝ) ≤ 1 / Fintype.card T :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  refine errorVerification_joint_correctness_indexed h hδ (fun a b hab => ?_) hp_nonneg hp_total
  have hrw : (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ)
      = (1 / Fintype.card T) * Fintype.card Sd := by ring
  rw [← hrw]
  exact hU a b hab

/-- **Error-verification correctness at an outcome-indexed sub-normalised weight.**

The form a measurement-outcome-indexed protocol supplies.  Instead of a law on key pairs, the
protocol hands over

* an outcome type `Ω` with a nonnegative weight `w` of total mass at most `1` (the Born weights of
  the round-outcome strings, sub-normalised because only part of the outcome space is retained),
* the two reconciled strings `A ω`, `B ω` read off each outcome,
* a further accept condition `acc ω` that does **not** read the seed (the parameter-estimation
  test), and
* the seed-indexed hash family `h`, the error-verification condition being `h s (A ω) = h s (B ω)`.

The conclusion bounds the seed-averaged joint mass of "the strings differ **and** every accept
condition holds" by `1 / |T|`.  It is `errorVerification_joint_correctness_indexed_of_universal`
composed with the grouping of outcomes into key pairs: the induced pair law
`p (a, b) = ∑_{ω : (A ω, B ω) = (a, b), acc ω} w ω` is nonnegative with total mass at most `1`,
which is exactly the sub-normalised hypothesis pair that lemma takes.

**Joint, never conditional.**  As throughout this file, the bound is on the *joint* event; the
conditional `Pr[differ | accept]` is not bounded by `1/|T|`
(`conditional_correctness_fails`). -/
theorem errorVerification_outcome_joint_correctness_of_universal
    {S T Sd Ω : Type*} [Finite S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Fintype Sd] [Nonempty Sd] [Fintype Ω]
    (h : Sd → S → T)
    (hU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ)
        ≤ (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ))
    (A B : Ω → S) (acc : Ω → Bool) (w : Ω → ℝ)
    (hw_nonneg : ∀ ω, 0 ≤ w ω) (hw_total : ∑ ω, w ω ≤ 1) :
    (1 / (Fintype.card Sd : ℝ)) *
        ∑ s : Sd, ∑ ω : Ω,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0)
      ≤ 1 / Fintype.card T := by
  classical
  have : Fintype S := Fintype.ofFinite S
  set p : S × S → ℝ :=
    fun ab => ∑ ω : Ω, if (A ω, B ω) = ab ∧ acc ω = true then w ω else 0 with hpdef
  have hp_nonneg : ∀ ab, 0 ≤ p ab := by
    intro ab
    refine Finset.sum_nonneg fun ω _ => ?_
    by_cases hc : (A ω, B ω) = ab ∧ acc ω = true
    · simpa [hc] using hw_nonneg ω
    · simp [hc]
  have hp_total : ∑ ab : S × S, p ab ≤ 1 := by
    have hswap : ∑ ab : S × S, p ab = ∑ ω : Ω, (if acc ω = true then w ω else 0) := by
      rw [hpdef, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hacc : acc ω = true
      · simp [hacc]
      · simp [hacc]
    rw [hswap]
    refine le_trans (Finset.sum_le_sum fun ω _ => ?_) hw_total
    by_cases hacc : acc ω = true
    · simp [hacc]
    · simpa [hacc] using hw_nonneg ω
  -- Both sides reduce to the same per-outcome sum.
  have hLHS : (1 / (Fintype.card Sd : ℝ)) *
        ∑ s : Sd, ∑ ω : Ω,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0) =
      ∑ ω : Ω,
        (if A ω ≠ B ω ∧ acc ω = true then w ω * collisionProbIdx h (A ω) (B ω) else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hc : A ω ≠ B ω ∧ acc ω = true
    · rw [ite_eq_left hc]
      have hcond : ∀ s : Sd,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0) =
            (if h s (A ω) = h s (B ω) then w ω else 0) := by
        intro s
        by_cases hs : h s (A ω) = h s (B ω)
        · simp [hs, hc.1, hc.2]
        · simp [hs]
      rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hcond s]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [collisionProbIdx]
      ring
    · rw [ite_eq_right hc]
      have hzero : ∀ s : Sd,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0)
            = 0 := by
        intro s
        refine ite_eq_right ?_
        rintro ⟨hne, hacc⟩
        exact hc ⟨hne, (Bool.and_eq_true _ _ |>.mp hacc).1⟩
      rw [Finset.sum_eq_zero fun s _ => hzero s, mul_zero]
  have hRHS : jointDifferAcceptProbIdx p h =
      ∑ ω : Ω,
        (if A ω ≠ B ω ∧ acc ω = true then w ω * collisionProbIdx h (A ω) (B ω) else 0) := by
    rw [jointDifferAcceptProbIdx]
    have hexp : ∀ ab : S × S,
        (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0) =
          ∑ ω : Ω, (if ab.1 ≠ ab.2 then
            (if (A ω, B ω) = ab ∧ acc ω = true then w ω else 0) *
              collisionProbIdx h ab.1 ab.2 else 0) := by
      intro ab
      by_cases hab : ab.1 ≠ ab.2
      · simp only [ite_eq_left hab, hpdef, Finset.sum_mul]
      · simp [hab]
    rw [Finset.sum_congr rfl fun ab (_ : ab ∈ Finset.univ) => hexp ab, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_eq_single (A ω, B ω)]
    · by_cases hc : A ω ≠ B ω ∧ acc ω = true
      · simp [hc.1, hc.2]
      · by_cases hne : A ω ≠ B ω
        · have hacc : ¬ acc ω = true := fun ha => hc ⟨hne, ha⟩
          simp [hne, hacc]
        · simp [hne]
    · intro ab _ hne
      by_cases hab : ab.1 ≠ ab.2
      · simp [hab, Ne.symm hne]
      · simp [hab]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hLHS, ← hRHS]
  exact errorVerification_joint_correctness_indexed_of_universal h hU hp_nonneg hp_total


end InfoTheory.Postselection.ErrorVerification
