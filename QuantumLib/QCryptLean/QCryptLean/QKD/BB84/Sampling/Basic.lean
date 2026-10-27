import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Probability.Distributions.Uniform
import QCryptLean.QKD.BB84.Registers

/-!
# Independent basis strings and matched-round shuffles

This module defines the probability law for two independent basis strings and a conditionally
uniform ordering of the identifiers where the strings agree. Alice and Bob may use fixed, unequal,
or degenerate one-round laws.

The basis comparison schedule follows Renner, arXiv:quant-ph/0512258v2, lines 673--736, and
fixed-batch sampling follows Pfister et al., arXiv:1506.07502v3, Sections IV--V. This module proves
only normalization, point masses, and shuffle cardinality; it does not establish a full sifting,
quantum-channel, or security connection.
-/

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- Product mass of a basis string under one fixed per-round basis law. -/
def basisStringWeight (N : ℕ) (p : PMF Basis) (a : Fin N → Basis) : ℝ≥0∞ :=
  ∏ i : Fin N, p (a i)

/-- The product masses of all length-`N` basis strings sum to one.

This is the finite product-law normalization used for independent basis choices in the
fixed-batch schedules of Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V.  It includes `N = 0` and arbitrary PMFs `p`. -/
theorem basisStringWeight_sum (N : ℕ) (p : PMF Basis) :
    (∑ a : Fin N → Basis, ∏ i : Fin N, p (a i)) = 1 := by
  rw [← Fintype.prod_sum]
  have hp : (∑ theta : Basis, p theta) = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact p.tsum_coe
  simp [hp]

/-- The explicit IID basis-string law built from its normalized product mass. -/
def basisStringLaw (N : ℕ) (p : PMF Basis) : PMF (Fin N → Basis) :=
  PMF.ofFintype (basisStringWeight N p) (basisStringWeight_sum N p)

/-- Point mass of the explicit basis-string law. -/
theorem basisStringLaw_apply (N : ℕ) (p : PMF Basis) (a : Fin N → Basis) :
    basisStringLaw N p a = ∏ i : Fin N, p (a i) := by
  rfl

/-- Round identifiers where Alice and Bob chose the same basis. -/
def Matched {N : ℕ} (a b : Fin N → Basis) : Finset (Fin N) :=
  Finset.univ.filter fun i => a i = b i

/-- An ordering of all rounds where Alice and Bob chose the same basis, with each
matched round appearing exactly once. -/
abbrev Shuffle {N : ℕ} (a b : Fin N → Basis) :=
  Fin (Matched a b).card ≃ {i : Fin N // i ∈ Matched a b}

/-- Increasing enumeration of the matched identifiers, including the empty set. -/
def increasingShuffle {N : ℕ} (a b : Fin N → Basis) : Shuffle a b :=
  ((Matched a b).orderIsoOfFin rfl).toEquiv

/-- Every matched-round shuffle type has the explicit increasing enumeration. -/
instance shuffleNonempty {N : ℕ} (a b : Fin N → Basis) : Nonempty (Shuffle a b) :=
  ⟨increasingShuffle a b⟩

/-- The number of matched-round orderings is the factorial of the matched-set size.

This cardinality is the denominator of the conditional uniform law on full orderings of the
already fixed matched set. -/
theorem card_shuffle {N : ℕ} (a b : Fin N → Basis) :
    Fintype.card (Shuffle a b) = (Matched a b).card.factorial := by
  simpa using Fintype.card_equiv (increasingShuffle a b)

/-- Basis strings together with a full ordering of their matched round identifiers. -/
structure RawControl (N : ℕ) where
  /-- Alice's basis string. -/
  a : Fin N → Basis
  /-- Bob's basis string. -/
  b : Fin N → Basis
  /-- A full ordering of the identifiers where the two basis strings agree. -/
  order : Shuffle a b
  deriving DecidableEq

/-- `RawControl` is explicitly the dependent triple of two strings and their shuffle. -/
def rawControlEquivSigma (N : ℕ) :
    RawControl N ≃ Σ a : Fin N → Basis, Σ b : Fin N → Basis, Shuffle a b where
  toFun omega := ⟨omega.a, omega.b, omega.order⟩
  invFun omega := ⟨omega.1, omega.2.1, omega.2.2⟩
  left_inv omega := by cases omega; rfl
  right_inv omega := by rcases omega with ⟨a, b, order⟩; rfl

/-- Finite enumeration transported from the explicit dependent-triple presentation. -/
noncomputable instance rawControlFintype (N : ℕ) : Fintype (RawControl N) :=
  Fintype.ofEquiv
    (Σ a : Fin N → Basis, Σ b : Fin N → Basis, Shuffle a b)
    (rawControlEquivSigma N).symm

/-- The all-Z basis string, used only for an explicit canonical raw control. -/
def constantZ (N : ℕ) : Fin N → Basis := fun _ => .z

/-- Explicit canonical raw control; no support witness or selected element is used. -/
def defaultRawControl (N : ℕ) : RawControl N :=
  ⟨constantZ N, constantZ N, increasingShuffle (constantZ N) (constantZ N)⟩

/-- Every raw-control type is inhabited by its explicit all-Z increasing control. -/
instance rawControlNonempty (N : ℕ) : Nonempty (RawControl N) :=
  ⟨defaultRawControl N⟩

/-- Alice and Bob draw basis strings independently, then draw a uniform matched-set ordering. -/
def rawControlLaw (N : ℕ) (pA pB : PMF Basis) : PMF (RawControl N) :=
  (basisStringLaw N pA).bind fun a =>
    (basisStringLaw N pB).bind fun b =>
      (PMF.uniformOfFintype (Shuffle a b)).bind fun order =>
        PMF.pure ⟨a, b, order⟩

/-- Point mass of the independent raw-control law.

The numerator contains independent Alice and Bob string weights.  The only dependent draw is the
uniform ordering of the already determined matched set.  The statement holds for every `N`, every
fixed pair of PMFs, and every raw control, without a positivity or support hypothesis. -/
theorem rawControlLaw_apply (N : ℕ) (pA pB : PMF Basis) (omega : RawControl N) :
    rawControlLaw N pA pB omega =
      ((∏ i : Fin N, pA (omega.a i)) * (∏ i : Fin N, pB (omega.b i))) /
        ((Matched omega.a omega.b).card.factorial : ℝ≥0∞) := by
  rcases omega with ⟨a₀, b₀, order₀⟩
  simp only [rawControlLaw, PMF.bind_apply, PMF.pure_apply,
    basisStringLaw_apply, PMF.uniformOfFintype_apply, tsum_fintype,
    card_shuffle, div_eq_mul_inv, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single a₀]
  · rw [Fintype.sum_eq_single b₀]
    · rw [Fintype.sum_eq_single order₀]
      · simp [mul_assoc]
      · intro order horder
        rw [ite_eq_right]
        intro h
        cases h
        exact horder rfl
    · intro b hb
      apply mul_eq_zero_of_right
      apply Fintype.sum_eq_zero
      intro order
      rw [ite_eq_right]
      intro h
      exact hb (congrArg (fun control : RawControl N => control.b) h).symm
  · intro a ha
    apply mul_eq_zero_of_right
    apply Fintype.sum_eq_zero
    intro b
    apply mul_eq_zero_of_right
    apply Fintype.sum_eq_zero
    intro order
    rw [ite_eq_right]
    intro h
    exact ha (congrArg (fun control : RawControl N => control.a) h).symm

/-- The real raw-control mass is the shuffle weight times the two real basis-string masses.

This is the complex-cast form used by the branch-value and retention identities; it is the
`ENNReal.toReal` reading of `rawControlLaw_apply` and holds for every `N`, every fixed pair of
PMFs and every raw control, without a positivity or support hypothesis. -/
theorem rawControlLaw_toReal_eq (N : ℕ) (pA pB : PMF Basis) (ω : RawControl N) :
    ((rawControlLaw N pA pB ω).toReal : ℂ) =
      (Fintype.card (Shuffle ω.a ω.b) : ℂ)⁻¹ *
        ((basisStringLaw N pA ω.a).toReal : ℂ) * ((basisStringLaw N pB ω.b).toReal : ℂ) := by
  rw [rawControlLaw_apply]
  simp only [basisStringLaw_apply, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_prod,
    ENNReal.toReal_natCast, card_shuffle]
  push_cast
  ring

/-! ## Definition-level probes -/

/-- The basis-string law is literally the finite PMF built from `basisStringWeight`. -/
theorem basisStringLaw_constructor (N : ℕ) (p : PMF Basis) :
    basisStringLaw N p =
      PMF.ofFintype (basisStringWeight N p) (basisStringWeight_sum N p) := by
  rfl

/-- No identifiers are matched in the zero-round case. -/
theorem matched_zero_card (a b : Fin 0 → Basis) : (Matched a b).card = 0 := by
  rfl

/-- Opposite one-round bases produce an empty matched set. -/
theorem matched_one_mismatch_card :
    (Matched (fun _ : Fin 1 => Basis.z) (fun _ => Basis.x)).card = 0 := by
  decide

/-- Equal one-round bases produce one matched identifier. -/
theorem matched_one_equal_card :
    (Matched (fun _ : Fin 1 => Basis.z) (fun _ => Basis.z)).card = 1 := by
  decide

/-- The explicit default control stores the constant-Z strings. -/
theorem defaultRawControl_strings (N : ℕ) :
    (defaultRawControl N).a = constantZ N ∧
      (defaultRawControl N).b = constantZ N := by
  exact ⟨rfl, rfl⟩

/-- The raw-control law is literally the two independent string binds followed by the shuffle. -/
theorem rawControlLaw_constructor (N : ℕ) (pA pB : PMF Basis) :
    rawControlLaw N pA pB =
      (basisStringLaw N pA).bind fun a =>
        (basisStringLaw N pB).bind fun b =>
          (PMF.uniformOfFintype (Shuffle a b)).bind fun order =>
            PMF.pure ⟨a, b, order⟩ := by
  rfl

end QKD.BB84.Sampling
