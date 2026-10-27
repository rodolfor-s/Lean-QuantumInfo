import Mathlib.Tactic.IntervalCases
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.TwoUniversalExact
import QCryptLean.Math.CodingTheory.SyndromeDecoding

/-! # Binary Inner Product Hash -/


open Math.CodingTheory

noncomputable section

namespace InfoTheory.QuantumLHL

variable {I : Type*} [Fintype I]

/-- Seed type for the binary inner-product hash on `I → Fin 2`: an `ℓ`-tuple of linear
functionals (rows), one per output bit. -/
abbrev BinaryHashSeed (I : Type*) (ℓ : ℕ) : Type _ := Fin ℓ → I → Fin 2

/-- One output bit of the binary hash: the `𝔽₂` inner product of a seed row `row` with a bit
string `x`, i.e. `(∑ i, row_i · x_i) mod 2`. -/
private def keyHashRowBit {I : Type*} [Fintype I] (row x : I → Fin 2) : Fin 2 :=
  ⟨(∑ i, (row i).val * (x i).val) % 2, Nat.mod_lt _ (by norm_num)⟩

private lemma keyHashRowBit_add {I : Type*} [Fintype I]
    (row u t : I → Fin 2) :
    keyHashRowBit row (u + t) = keyHashRowBit row u + keyHashRowBit row t := by
  refine Fin.ext ?_
  change (∑ i, (row i).val * ((u i + t i : Fin 2)).val) % 2
      = ((keyHashRowBit row u : Fin 2) + keyHashRowBit row t).val
  rw [Fin.val_add]
  change _ = ((∑ i, (row i).val * (u i).val) % 2 + (∑ i, (row i).val * (t i).val) % 2) % 2
  rw [← Nat.add_mod, ← Finset.sum_add_distrib, Finset.sum_nat_mod,
    Finset.sum_nat_mod (f := fun i => (row i).val * (u i).val + (row i).val * (t i).val)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.val_add, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add]

/-- The binary inner-product hash is an additive map of bit strings. -/
def binaryInnerProductSyndrome {ℓ : ℕ} (A : BinaryHashSeed I ℓ) :
    (I → Fin 2) →+ (Fin ℓ → Fin 2) where
  toFun x j := keyHashRowBit (A j) x
  map_zero' := by
    ext j
    simp [keyHashRowBit]
  map_add' x y := funext fun j => keyHashRowBit_add (A j) x y

/-- The binary inner-product family returns its output bits in their natural order. -/
def binaryInnerProductHashFamily (I : Type*) [Fintype I] [DecidableEq I] (ℓ : ℕ) :
    HashFamily (BinaryHashSeed I ℓ) (I → Fin 2) (Fin ℓ → Fin 2) where
  hash := fun A => binaryInnerProductSyndrome A

/-- Value of a single hash row after updating exactly one index `i0` of the seed row: the
`i0`-term uses the new bit `v`, the remaining indices are unchanged. -/
private lemma keyHashRowBit_update_val {I : Type*} [Fintype I] [DecidableEq I]
    (i0 : I) (row : I → Fin 2) (v : Fin 2) (x : I → Fin 2) :
    (keyHashRowBit (Function.update row i0 v) x).val =
      (v.val * (x i0).val + ∑ i ∈ Finset.univ.erase i0, (row i).val * (x i).val) % 2 := by
  change (∑ i, (Function.update row i0 v i).val * (x i).val) % 2 = _
  congr 1
  rw [← Finset.add_sum_erase Finset.univ
      (fun i => (Function.update row i0 v i).val * (x i).val) (Finset.mem_univ i0)]
  rw [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- Arithmetic core: flipping the seed bit at an index where `x` and `x'` disagree
(`b ≠ b'`, both in `Fin 2`) toggles the row-collision predicate. -/
private lemma parity_flip_bit (a b b' R R' : ℕ)
    (ha : a < 2) (hb : b < 2) (hb' : b' < 2) (hne : b ≠ b') :
    (((a + 1) % 2) * b + R) % 2 = (((a + 1) % 2) * b' + R') % 2 ↔
      ¬ ((a * b + R) % 2 = (a * b' + R') % 2) := by
  interval_cases a <;> interval_cases b <;> interval_cases b' <;> omega

/-- An involution `t` on a finite type with `∀ a, P (t a) ↔ ¬ P a` pairs the `P`-set with its
complement, so `P` holds on exactly half the type. -/
private lemma keyCard_filter_involution_neg {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (t : α → α)
    (hinv : Function.Involutive t) (hiff : ∀ a, P (t a) ↔ ¬ P a) :
    (Finset.univ.filter P).card * 2 = Fintype.card α := by
  have hbij : (Finset.univ.filter P).card = (Finset.univ.filter (fun a => ¬ P a)).card := by
    apply Finset.card_bij' (fun a _ => t a) (fun a _ => t a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hiff]; exact not_not.mpr ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hiff]; exact ha
    · intro a _; exact hinv a
    · intro a _; exact hinv a
  have hsum : (Finset.univ.filter P).card
      + (Finset.univ.filter (fun a => ¬ P a)).card = Fintype.card α := by
    rw [← Finset.card_univ]; exact Finset.card_filter_add_card_filter_not P
  omega

/-- **Exact per-row halving.** When `x` and `x'` differ at index `i0`, the row-collision set
is *exactly* half of all seed rows over the bit-index domain. -/
private lemma keyHashRow_collision_card_eq
    {I : Type*} [Fintype I] [DecidableEq I] {x x' : I → Fin 2}
    (i0 : I) (hdiff : x i0 ≠ x' i0) :
    (Finset.univ.filter (fun row : I → Fin 2 =>
      keyHashRowBit row x = keyHashRowBit row x')).card * 2
      = Fintype.card (I → Fin 2) := by
  refine keyCard_filter_involution_neg _
    (fun row => Function.update row i0 (row i0 + 1)) ?_ ?_
  · intro row
    funext i
    rcases eq_or_ne i i0 with hi | hi
    · subst hi
      have hx : ∀ y : Fin 2, y + 1 + 1 = y := by decide
      simp [Function.update_self, hx]
    · simp only [Function.update_of_ne hi]
  · intro row
    have hXne : (x i0).val ≠ (x' i0).val := fun h => hdiff (Fin.ext h)
    have hval : ((row i0) + 1 : Fin 2).val = ((row i0).val + 1) % 2 := by
      rw [Fin.val_add]; rfl
    set R := ∑ i ∈ Finset.univ.erase i0, (row i).val * (x i).val with hR
    set R' := ∑ i ∈ Finset.univ.erase i0, (row i).val * (x' i).val with hR'
    simp only [Fin.ext_iff]
    have e1 := keyHashRowBit_update_val i0 row (row i0 + 1) x
    have e2 := keyHashRowBit_update_val i0 row (row i0 + 1) x'
    have e3 := keyHashRowBit_update_val i0 row (row i0) x
    have e4 := keyHashRowBit_update_val i0 row (row i0) x'
    rw [Function.update_eq_self] at e3 e4
    rw [e1, e2, e3, e4, hval]
    exact parity_flip_bit (row i0).val (x i0).val (x' i0).val R R'
      (row i0).isLt (x i0).isLt (x' i0).isLt hXne

/-- **Exact joint collision count.** The number of `ℓ`-row seeds on which two bit strings differing
at some index collide, times `2 ^ ℓ`, equals `|I → Fin 2| ^ ℓ`. -/
private lemma binaryInnerProductHash_collision_card_eq
    {I : Type*} [Fintype I] [DecidableEq I] {ℓ : ℕ} {x x' : I → Fin 2}
    (i0 : I) (hdiff : x i0 ≠ x' i0) :
    (Finset.univ.filter (fun A : BinaryHashSeed I ℓ =>
      binaryInnerProductSyndrome A x = binaryInnerProductSyndrome A x')).card * 2 ^ ℓ
      = (Fintype.card (I → Fin 2)) ^ ℓ := by
  let C : Finset (I → Fin 2) :=
    Finset.univ.filter (fun row => keyHashRowBit row x = keyHashRowBit row x')
  have hset :
      Finset.univ.filter (fun A : BinaryHashSeed I ℓ =>
        binaryInnerProductSyndrome A x = binaryInnerProductSyndrome A x') =
        Fintype.piFinset (fun _ : Fin ℓ => C) := by
    ext A
    simp [C, funext_iff, binaryInnerProductSyndrome]
  have hcard :
      (Finset.univ.filter (fun A : BinaryHashSeed I ℓ =>
        binaryInnerProductSyndrome A x = binaryInnerProductSyndrome A x')).card =
        C.card ^ ℓ := by
    rw [hset, Fintype.card_piFinset_const]
  have hrow : C.card * 2 = Fintype.card (I → Fin 2) :=
    keyHashRow_collision_card_eq i0 hdiff
  rw [hcard, ← mul_pow, hrow]

/-- **Exact (`2*`-universality) of the binary inner-product hash family.**

For any two distinct bit strings `x ≠ x' : I → Fin 2`, the number of seeds on which they collide,
times the output alphabet size `2 ^ ℓ`, equals the seed-count **exactly**:
`#{A : hash A x = hash A x'} · 2 ^ ℓ = |BinaryHashSeed I ℓ|`.

`x ≠ x'` differ at some index; the difference vector is a nonzero `𝔽₂`-vector, so each row of the
uniform seed halves the collision set exactly, giving an exact `(1/2)^ℓ` collision fraction rather
than a bound. -/
theorem isExactTwoUniversal_binaryInnerProductHashFamily
    (I : Type*) [Fintype I] [DecidableEq I] (ℓ : ℕ) :
    (binaryInnerProductHashFamily I ℓ).IsExactTwoUniversal := by
  intro x x' hne
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ x' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hS : Fintype.card (BinaryHashSeed I ℓ) = (Fintype.card (I → Fin 2)) ^ ℓ := by
    simp only [BinaryHashSeed, Fintype.card_fun, Fintype.card_fin]
  simp only [binaryInnerProductHashFamily, Fintype.card_fun, Fintype.card_fin, hS]
  convert (binaryInnerProductHash_collision_card_eq (I := I) (ℓ := ℓ) i0 hi0) using 1
  · congr 1
  · simp only [Fintype.card_fun, Fintype.card_fin]

variable {m : ℕ}

/-- Distinct strings collide for exactly the inverse alphabet fraction of all linear seeds. -/
lemma sum_binaryInnerProductSyndrome_collision [DecidableEq I] (x y : I → Fin 2) (hxy : x ≠ y) :
    (∑ A : BinaryHashSeed I m, if binaryInnerProductSyndrome A x = binaryInnerProductSyndrome A y
      then (1 : ℝ) else 0) =
      (Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m := by
  simp only [Finset.sum_boole]
  have h := isExactTwoUniversal_binaryInnerProductHashFamily I m x y hxy
  change (Finset.univ.filter (fun A : BinaryHashSeed I m =>
    binaryInnerProductSyndrome A x =
      binaryInnerProductSyndrome A y)).card * Fintype.card (Fin m → Fin 2) =
        Fintype.card (BinaryHashSeed I m) at h
  rw [eq_div_iff (by positivity)]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  exact_mod_cast h

variable [DecidableEq I]

/-- Averaging over the linear seed bounds the competitors of any fixed error pattern. -/
lemma sum_collisionCount_le (T : Finset (I → Fin 2)) (e : I → Fin 2) :
    (∑ A : BinaryHashSeed I m, collisionCount (binaryInnerProductSyndrome A) T e) ≤
      T.card * ((Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m) := by
  unfold collisionCount
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _y ∈ T, (Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m := by
      apply Finset.sum_le_sum
      intro y _
      by_cases h : y = e
      · subst y
        simp only [ne_eq, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero]
        positivity
      · simpa only [h, ne_eq, not_false_eq_true, true_and] using
          (sum_binaryInnerProductSyndrome_collision (m := m) y e h).le
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Some fixed linear seed meets the average weighted collision bound. -/
lemma exists_binaryInnerProductSyndrome_collision_le (T : Finset (I → Fin 2)) (w : (I → Fin 2) → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hsum : ∑ e, w e ≤ 1) :
    ∃ A : BinaryHashSeed I m,
      (∑ e, w e * collisionCount (binaryInnerProductSyndrome A) T e) ≤ T.card / (2 : ℝ) ^ m := by
  have havg : (∑ A : BinaryHashSeed I m,
      ∑ e, w e * collisionCount (binaryInnerProductSyndrome A) T e) ≤
      ∑ _A : BinaryHashSeed I m, (T.card : ℝ) / (2 : ℝ) ^ m := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ e, w e * (T.card * ((Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m)) :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (sum_collisionCount_le T e) (hw e)
      _ = (∑ e, w e) * (T.card * ((Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (T.card * ((Fintype.card (BinaryHashSeed I m) : ℝ) / (2 : ℝ) ^ m)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  obtain ⟨A, _, hA⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨A, hA⟩

omit [DecidableEq I] in
/-- A small candidate set admits a syndrome with no nonzero kernel word in it. -/
lemma exists_binaryInnerProductSyndrome_separating (T : Finset (I → Fin 2))
    (hT : (T.card : ℝ) < (2 : ℝ) ^ m) :
    ∃ A : BinaryHashSeed I m, ∀ e ∈ T, binaryInnerProductSyndrome A e = 0 → e = 0 := by
  classical
  obtain ⟨A, hA⟩ := exists_binaryInnerProductSyndrome_collision_le (m := m) T
    (fun e => if e = 0 then 1 else 0) (fun e => by positivity) (by simp)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hA
  refine ⟨A, fun e he hs => ?_⟩
  by_contra hne
  have hcount := one_le_collisionCount (binaryInnerProductSyndrome A) T 0 e he hne
    (by simpa using hs)
  have hlt : (T.card : ℝ) / (2 : ℝ) ^ m < 1 :=
    (div_lt_one (by positivity)).mpr hT
  linarith

end InfoTheory.QuantumLHL

end
