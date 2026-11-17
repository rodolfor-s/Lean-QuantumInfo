import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Linear Codes -/


noncomputable section

namespace Math.CodingTheory


/-- A classical linear code over F₂ = ZMod 2 -/
structure LinearCode (n k : ℕ) where
  /-- Generator matrix: k × n matrix over F₂ -/
  generatorMatrix : Matrix (Fin k) (Fin n) (ZMod 2)
  /-- The generator matrix has full rank k -/
  generator_full_rank : generatorMatrix.rank = k

/-- The codewords of a linear code: c = Gᵀm for message vector m -/
def LinearCode.codewords {n k : ℕ} (C : LinearCode n k) : Set (Fin n → ZMod 2) :=
  { c | ∃ m : Fin k → ZMod 2, c = C.generatorMatrix.transpose.mulVec m }

/-- Codewords form a subspace (closure under addition). -/
theorem LinearCode.codewords_add {n k : ℕ} (C : LinearCode n k)
    (c1 c2 : Fin n → ZMod 2) (hc1 : c1 ∈ C.codewords) (hc2 : c2 ∈ C.codewords) :
    (c1 + c2) ∈ C.codewords := by
  obtain ⟨m1, hm1⟩ := hc1
  obtain ⟨m2, hm2⟩ := hc2
  use m1 + m2
  simp only [Matrix.mulVec_add, hm1, hm2]

/-- Zero vector is a codeword. -/
theorem LinearCode.zero_mem_codewords {n k : ℕ} (C : LinearCode n k) :
    (0 : Fin n → ZMod 2) ∈ C.codewords := by
  use 0
  simp only [Matrix.mulVec_zero]

/-- Codewords are closed under negation. -/
theorem LinearCode.codewords_neg {n k : ℕ} (C : LinearCode n k)
    (c : Fin n → ZMod 2) (hc : c ∈ C.codewords) : (-c) ∈ C.codewords := by
  obtain ⟨m, hm⟩ := hc
  use -m
  simp only [Matrix.mulVec_neg, hm]

/-- Codewords are closed under subtraction. -/
theorem LinearCode.codewords_sub {n k : ℕ} (C : LinearCode n k)
    (c1 c2 : Fin n → ZMod 2) (hc1 : c1 ∈ C.codewords) (hc2 : c2 ∈ C.codewords) :
    (c1 - c2) ∈ C.codewords := by
  have h := C.codewords_add c1 (-c2) hc1 (C.codewords_neg c2 hc2)
  simp only [sub_eq_add_neg]
  exact h


/-- Hamming weight of a vector: number of nonzero coordinates -/
def hammingWeight {n : ℕ} (v : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- Hamming weight is zero iff the vector is zero. -/
theorem hammingWeight_eq_zero_iff {n : ℕ} (v : Fin n → ZMod 2) :
    hammingWeight v = 0 ↔ v = 0 := by
  unfold hammingWeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    ext i
    simpa using h (Finset.mem_univ i)
  · intro h i _
    simp [h]

/-- Hamming weight is at most n. -/
theorem hammingWeight_le {n : ℕ} (v : Fin n → ZMod 2) :
    hammingWeight v ≤ n := by
  unfold hammingWeight
  calc (Finset.univ.filter (fun i => v i ≠ 0)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

/-- Hamming distance between two vectors. -/
def hammingDistance {n : ℕ} (v w : Fin n → ZMod 2) : ℕ :=
  hammingWeight (v - w)

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm {n : ℕ} (v w : Fin n → ZMod 2) :
    hammingDistance v w = hammingDistance w v := by
  unfold hammingDistance hammingWeight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq]
  -- In ZMod 2: v i - w i ≠ 0 ↔ w i - v i ≠ 0 (since -x = x in ZMod 2)
  constructor <;> (intro h; simp only [sub_ne_zero] at h ⊢; exact h.symm)

/-- Hamming distance is zero iff vectors are equal. -/
theorem hammingDistance_eq_zero_iff {n : ℕ} (v w : Fin n → ZMod 2) :
    hammingDistance v w = 0 ↔ v = w := by
  unfold hammingDistance
  rw [hammingWeight_eq_zero_iff, sub_eq_zero]

/-- Triangle inequality for Hamming distance. -/
lemma hammingDistance_triangle {n : ℕ} (u v w : Fin n → ZMod 2) :
    hammingDistance u w ≤ hammingDistance u v + hammingDistance v w := by
  unfold hammingDistance hammingWeight
  -- u - w = (u - v) + (v - w)
  have h : u - w = (u - v) + (v - w) := by ring
  rw [h]
  -- If (u-v) i + (v-w) i ≠ 0, then either (u-v) i ≠ 0 or (v-w) i ≠ 0
  calc (Finset.univ.filter (fun i => ((u - v) + (v - w)) i ≠ 0)).card
      ≤ (Finset.univ.filter (fun i => (u - v) i ≠ 0) ∪
         Finset.univ.filter (fun i => (v - w) i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        by_contra hc
        push Not at hc
        simp only [Pi.add_apply, hc.1, hc.2, add_zero, ne_eq, not_true_eq_false] at hi
    _ ≤ (Finset.univ.filter (fun i => (u - v) i ≠ 0)).card +
        (Finset.univ.filter (fun i => (v - w) i ≠ 0)).card := Finset.card_union_le _ _


/-- The set of Hamming weights of nonzero codewords. -/
def LinearCode.nonzeroWeights {n k : ℕ} (C : LinearCode n k) : Set ℕ :=
  { w | ∃ c ∈ C.codewords, c ≠ 0 ∧ w = hammingWeight c }

/-- There exists a nonzero codeword iff k > 0 (the code is non-trivial).
    For k > 0, any nonzero message m gives a nonzero codeword Gᵀm. -/
lemma LinearCode.exists_nonzero_codeword {n k : ℕ} (C : LinearCode n k) (hk : 0 < k) :
    ∃ c ∈ C.codewords, c ≠ 0 := by
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hk
  by_contra hno
  push Not at hno
  have hzero : ∀ m : Fin k → ZMod 2, C.generatorMatrix.transpose.mulVec m = 0 := by
    intro m
    have hmem : C.generatorMatrix.transpose.mulVec m ∈ C.codewords := ⟨m, rfl⟩
    exact hno (C.generatorMatrix.transpose.mulVec m) hmem
  have hall_zero : ∀ i : Fin k, C.generatorMatrix i = 0 := by
    intro i
    let e_i : Fin k → ZMod 2 := fun j => if j = i then 1 else 0
    have h := hzero e_i
    ext j
    have hj := congr_fun h j
    simp only [Matrix.mulVec, Matrix.transpose_apply, Pi.zero_apply] at hj
    rw [dotProduct.eq_1] at hj
    rw [Finset.sum_eq_single i] at hj
    · have hei : e_i i = 1 := ite_eq_left rfl
      rw [hei, mul_one] at hj
      exact hj
    · intro b _ hne
      change C.generatorMatrix b j * e_i b = 0
      have heb : e_i b = 0 := ite_eq_right (fun hbi => hne hbi)
      rw [heb, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hrank_zero : C.generatorMatrix.rank = 0 := by
    have hzmat : C.generatorMatrix = 0 := by
      ext i j
      exact congr_fun (hall_zero i) j
    rw [hzmat]
    exact Matrix.rank_zero
  have hrank := C.generator_full_rank
  omega

/-- Minimum distance of a code: minimum Hamming weight of nonzero codewords.
    Defined as the infimum of nonzero codeword weights. Returns 0 for trivial codes (k=0).

    Uses `sInf` (infimum in ℕ with ⨅ ∅ = 0) on the set of weights of nonzero codewords. -/
noncomputable def LinearCode.minDistance {n k : ℕ} (C : LinearCode n k) : ℕ :=
  sInf { w : ℕ | ∃ c ∈ C.codewords, c ≠ 0 ∧ hammingWeight c = w }

/-- Minimum distance equals minimum Hamming weight of nonzero codewords.

    **Proof strategy**: By definition, d = min{wt(c) : c ∈ C, c ≠ 0}.
    For linear codes, d = min{wt(c₁ - c₂) : c₁, c₂ ∈ C, c₁ ≠ c₂}
                       = min{wt(c) : c ∈ C, c ≠ 0}
    since c₁ - c₂ ∈ C (linearity). -/
theorem LinearCode.minDistance_spec {n k : ℕ} (C : LinearCode n k) :
    ∀ c ∈ C.codewords, c ≠ 0 → C.minDistance ≤ hammingWeight c := by
  intro c hc hne
  unfold minDistance
  apply Nat.sInf_le
  exact ⟨c, hc, hne, rfl⟩

/-- Minimum distance is positive for nontrivial codes. -/
theorem LinearCode.minDistance_pos {n k : ℕ} (C : LinearCode n k)
    (h : ∃ c ∈ C.codewords, c ≠ 0) : 0 < C.minDistance := by
  unfold minDistance
  rw [Nat.pos_iff_ne_zero]
  intro heq
  rw [Nat.sInf_eq_zero] at heq
  rcases heq with ⟨c, hc, hne, hw⟩ | hempty
  · exact hne ((hammingWeight_eq_zero_iff c).mp hw)
  · obtain ⟨c, hc, hne⟩ := h
    have hmem : hammingWeight c ∈ {w | ∃ c ∈ C.codewords, c ≠ 0 ∧ hammingWeight c = w} :=
      ⟨c, hc, hne, rfl⟩
    rw [hempty] at hmem
    exact hmem


/-- A code can correct up to ⌊(d-1)/2⌋ errors -/
def LinearCode.errorCorrectionCapability {n k : ℕ} (C : LinearCode n k) : ℕ :=
  (C.minDistance - 1) / 2

/-- Error correction bound: if two codewords differ by more than 2t positions,
    any vector within distance t of one is not within distance t of the other. -/
theorem LinearCode.lt_hammingDistance_of_ne_of_two_mul_lt_minDistance {n k : ℕ} (C : LinearCode n k)
    (c1 c2 : Fin n → ZMod 2) (hc1 : c1 ∈ C.codewords) (hc2 : c2 ∈ C.codewords)
    (hne : c1 ≠ c2) (t : ℕ) (ht : 2 * t < C.minDistance)
    (v : Fin n → ZMod 2) (hv1 : hammingDistance v c1 ≤ t) :
    hammingDistance v c2 > t := by
  -- c1 - c2 is a nonzero codeword
  have hdiff_cw : c1 - c2 ∈ C.codewords := C.codewords_sub c1 c2 hc1 hc2
  have hdiff_ne : c1 - c2 ≠ 0 := sub_ne_zero.mpr hne
  -- So d(c1, c2) = wt(c1 - c2) ≥ minDistance
  have hd12 : C.minDistance ≤ hammingDistance c1 c2 := by
    unfold hammingDistance
    exact C.minDistance_spec (c1 - c2) hdiff_cw hdiff_ne
  -- Triangle inequality: d(c1, c2) ≤ d(c1, v) + d(v, c2)
  have htri := hammingDistance_triangle c1 v c2
  -- d(c1, v) = d(v, c1) by symmetry
  have hsym : hammingDistance c1 v = hammingDistance v c1 := hammingDistance_comm c1 v
  -- Combining: minDistance ≤ d(c1, c2) ≤ d(v, c1) + d(v, c2) ≤ t + d(v, c2)
  -- So d(v, c2) ≥ minDistance - t > 2t - t = t
  rw [hsym] at htri
  have h1 : C.minDistance ≤ hammingDistance v c1 + hammingDistance v c2 := Nat.le_trans hd12 htri
  omega


/-- The dual code C⊥ consists of all vectors orthogonal to every codeword.
    For a code with generator matrix G, the dual has parity check matrix G. -/
def LinearCode.dual {n k : ℕ} (C : LinearCode n k) : Set (Fin n → ZMod 2) :=
  { v | ∀ c ∈ C.codewords, ∑ i, v i * c i = 0 }

/-- The dual code is closed under addition. -/
theorem LinearCode.dual_add {n k : ℕ} (C : LinearCode n k)
    (v w : Fin n → ZMod 2) (hv : v ∈ C.dual) (hw : w ∈ C.dual) : (v + w) ∈ C.dual := by
  intro c hc
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hv c hc, hw c hc, add_zero]

/-- The dual code is closed under negation. -/
theorem LinearCode.dual_neg {n k : ℕ} (C : LinearCode n k)
    (v : Fin n → ZMod 2) (hv : v ∈ C.dual) : (-v) ∈ C.dual := by
  intro c hc
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hv c hc, neg_zero]

/-- The dual code is closed under subtraction. -/
theorem LinearCode.dual_sub {n k : ℕ} (C : LinearCode n k)
    (v w : Fin n → ZMod 2) (hv : v ∈ C.dual) (hw : w ∈ C.dual) : (v - w) ∈ C.dual := by
  rw [sub_eq_add_neg]
  exact C.dual_add v (-w) hv (C.dual_neg w hw)

/-- A vector is in the dual iff it's orthogonal to all rows of G. -/
theorem LinearCode.mem_dual_iff {n k : ℕ} (C : LinearCode n k) (v : Fin n → ZMod 2) :
    v ∈ C.dual ↔ ∀ j : Fin k, ∑ i, v i * C.generatorMatrix j i = 0 := by
  constructor
  · -- Forward: v orthogonal to all codewords → v orthogonal to all rows of G
    intro hv j
    -- j-th row of G is the codeword Gᵀeⱼ
    let e_j : Fin k → ZMod 2 := fun i => if i = j then 1 else 0
    have hcw : C.generatorMatrix.transpose.mulVec e_j ∈ C.codewords := ⟨e_j, rfl⟩
    have heq : ∑ i, v i * (C.generatorMatrix.transpose.mulVec e_j) i = 0 := hv _ hcw
    -- Show that Gᵀeⱼ i = G j i
    have hmul : ∀ i, C.generatorMatrix.transpose.mulVec e_j i = C.generatorMatrix j i := by
      intro i
      simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct.eq_1]
      rw [Finset.sum_eq_single j]
      · have hej : e_j j = 1 := ite_eq_left rfl
        rw [hej, mul_one]
      · intro b _ hne
        change C.generatorMatrix b i * e_j b = 0
        have heb : e_j b = 0 := ite_eq_right (fun h => hne h)
        rw [heb, mul_zero]
      · intro habs
        exact absurd (Finset.mem_univ j) habs
    simp_rw [hmul] at heq
    exact heq
  · -- Backward: v orthogonal to all rows of G → v orthogonal to all codewords
    intro hrows c hc
    obtain ⟨m, hm⟩ := hc
    rw [hm]
    -- c_i = (Gᵀm)_i = Σⱼ G j i * m j
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct.eq_1]
    -- ⟨v, c⟩ = Σᵢ vᵢ (Σⱼ G j i * mⱼ) = Σⱼ mⱼ (Σᵢ vᵢ G j i)
    calc ∑ i, v i * ∑ j, C.generatorMatrix j i * m j
        = ∑ i, ∑ j, v i * (C.generatorMatrix j i * m j) := by
          congr 1; ext i; rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, v i * (C.generatorMatrix j i * m j) := Finset.sum_comm
      _ = ∑ j, ∑ i, m j * (v i * C.generatorMatrix j i) := by
          congr 1; ext j; congr 1; ext i; ring
      _ = ∑ j, m j * ∑ i, v i * C.generatorMatrix j i := by
          congr 1; ext j; rw [← Finset.mul_sum]
      _ = ∑ j, m j * 0 := by simp only [hrows]
      _ = 0 := by simp only [mul_zero, Finset.sum_const_zero]


/-- The double dual of a set (vectors orthogonal to C.dual) -/
def LinearCode.doubleDual {n k : ℕ} (C : LinearCode n k) : Set (Fin n → ZMod 2) :=
  { w | ∀ v ∈ C.dual, ∑ i, w i * v i = 0 }

/-- Every codeword is in the double dual: C ⊆ C⊥⊥ -/
theorem LinearCode.codewords_subset_doubleDual {n k : ℕ} (C : LinearCode n k) :
    C.codewords ⊆ C.doubleDual := by
  intro c hc v hv
  -- v ∈ C.dual means ⟨v, c'⟩ = 0 for all c' ∈ C.codewords
  -- In particular ⟨v, c⟩ = 0
  have h := hv c hc
  -- Need to show ∑ i, c i * v i = 0, but we have ∑ i, v i * c i = 0
  calc ∑ i, c i * v i = ∑ i, v i * c i := by congr 1; ext i; ring
    _ = 0 := h

/-- **Double Dual Theorem**: C⊥⊥ ⊆ C. Uses the bilinear form double orthogonal
    theorem from Mathlib. -/
theorem LinearCode.doubleDual_subset_codewords {n k : ℕ} (C : LinearCode n k) :
    C.doubleDual ⊆ C.codewords := by
  intro w hw
  -- Step 1: Define the codewords as a submodule W = range(Gᵀ.mulVecLin)
  let W : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    LinearMap.range C.generatorMatrix.transpose.mulVecLin
  -- Step 2: identity — w ∈ C.codewords ↔ w ∈ W
  have h_bridge : ∀ x : Fin n → ZMod 2, x ∈ W ↔ x ∈ C.codewords := by
    intro x
    simp only [W, LinearMap.mem_range, codewords, Set.mem_ofPred_eq, Matrix.mulVecLin_apply]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
  -- Step 3: Build a nondegenerate reflexive bilinear form B(v,w) = Σᵢ vᵢwᵢ
  have h_form : ∃ B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2),
      B.Nondegenerate ∧ B.IsRefl ∧
      ∀ v w, B v w = ∑ i, v i * w i := by
    refine ⟨LinearMap.mk₂ (ZMod 2) (fun v w => ∑ i, v i * w i)
      (fun v₁ v₂ w => by simp_rw [Pi.add_apply, add_mul, Finset.sum_add_distrib])
      (fun r v w => by
        simp only [Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_assoc]; rw [← Finset.mul_sum])
      (fun v w₁ w₂ => by simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun r v w => by
        simp only [Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm]; rw [← Finset.mul_sum]),
      ⟨?_, ?_⟩, ?_, fun v w => rfl⟩
    · -- SeparatingLeft: if ∀ w, Σ v_i w_i = 0, then v = 0
      intro v hv; ext i
      have := hv (fun j => if j = i then 1 else 0)
      simp only [LinearMap.mk₂_apply] at this
      rw [Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hbi; simp [hbi]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · -- SeparatingRight: if ∀ v, Σ v_i w_i = 0, then w = 0
      intro w hw; ext i
      have := hw (fun j => if j = i then 1 else 0)
      simp only [LinearMap.mk₂_apply] at this
      rw [show ∑ x, (if x = i then (1 : ZMod 2) else 0) * w x =
        ∑ x, w x * (if x = i then 1 else 0) from by congr 1; ext x; ring] at this
      rw [Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hbi; simp [hbi]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · -- Reflexive (symmetric): B(v,w) = 0 → B(w,v) = 0
      intro v w hvw
      simp only [LinearMap.mk₂_apply] at hvw ⊢
      rw [show ∑ i, w i * v i = ∑ i, v i * w i from by congr 1; ext i; ring]
      exact hvw
  -- Step 4: C.dual = ↑(B.orthogonal W)
  obtain ⟨B, hB_nondeg, hB_refl, hB_eq⟩ := h_form
  have h_dual : C.dual = ↑(B.orthogonal W) := by
    ext v
    simp only [dual, Set.mem_ofPred_eq, SetLike.mem_coe,
      LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hv x hx
      rw [hB_eq]
      have hx' := (h_bridge x).mp hx
      rw [show ∑ i, x i * v i = ∑ i, v i * x i from by congr 1; ext i; ring]
      exact hv x hx'
    · intro hv c hc
      have hc' := (h_bridge c).mpr hc
      have := hv c hc'
      change (B c) v = 0 at this
      rw [hB_eq] at this
      rw [show ∑ i, v i * c i = ∑ i, c i * v i from by congr 1; ext i; ring]
      exact this
  -- Step 5: C.doubleDual = ↑(B.orthogonal (B.orthogonal W))
  have h_ddual : C.doubleDual = ↑(B.orthogonal (B.orthogonal W)) := by
    ext u
    simp only [doubleDual, Set.mem_ofPred_eq, SetLike.mem_coe,
      LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hu v hv
      rw [hB_eq]
      have hv' : v ∈ C.dual := h_dual ▸ hv
      rw [show ∑ i, v i * u i = ∑ i, u i * v i from by congr 1; ext i; ring]
      exact hu v hv'
    · intro hu v hv
      have hv' : v ∈ B.orthogonal W := by
        have : v ∈ (↑(B.orthogonal W) : Set _) := h_dual ▸ hv
        exact this
      have := hu v hv'
      change (B v) u = 0 at this
      rw [hB_eq] at this
      rw [show ∑ i, u i * v i = ∑ i, v i * u i from by congr 1; ext i; ring]
      exact this
  -- Step 6: Apply orthogonal_orthogonal and conclude
  have h_key : B.orthogonal (B.orthogonal W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal hB_nondeg hB_refl W
  rw [h_ddual] at hw
  rw [h_key] at hw
  exact (h_bridge w).mp hw

/-- Double dual equals codewords: C⊥⊥ = C -/
theorem LinearCode.doubleDual_eq_codewords {n k : ℕ} (C : LinearCode n k) :
    C.doubleDual = C.codewords :=
  Set.eq_of_subset_of_subset C.doubleDual_subset_codewords C.codewords_subset_doubleDual

/-- Membership characterization: d ∈ C iff d ⊥ C⊥ -/
theorem LinearCode.mem_codewords_iff_orthogonal_to_dual {n k : ℕ} (C : LinearCode n k)
    (d : Fin n → ZMod 2) :
    d ∈ C.codewords ↔ ∀ v ∈ C.dual, ∑ i, d i * v i = 0 := by
  rw [← C.doubleDual_eq_codewords]
  rfl

end Math.CodingTheory

end
