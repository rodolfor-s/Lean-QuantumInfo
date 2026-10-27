import Mathlib.Basic.Complex.Basic
import QCryptLean.Math.CodingTheory.CSS.ErrorModel
import QCryptLean.Math.CodingTheory.LinearCodes

/-!
# CSS syndromes and decoding combinatorics

Nested binary codes, syndromes, minimum-weight representatives and Pauli phase arithmetic.
-/

open Math.CodingTheory

noncomputable section

namespace Math.CodingTheory.CSS

/-- CSS code constructed from C₁ ⊇ C₂ -/
structure CSSCode (n : ℕ) where
  /-- Dimension of the larger classical code C₁. -/
  k1 : ℕ
  /-- Dimension of the stabilizer subcode C₂. -/
  k2 : ℕ
  /-- The larger binary linear code containing all computational codewords. -/
  C1 : LinearCode n k1
  /-- The binary linear subcode whose cosets label the encoded basis states. -/
  C2 : LinearCode n k2
  C2_subset_C1 : C2.codewords ⊆ C1.codewords
  k2_le_k1 : k2 ≤ k1

/-- Number of logical qubits encoded by a CSS code -/
def CSSCode.numLogicalQubits {n : ℕ} (code : CSSCode n) : ℕ :=
  code.k1 - code.k2

/-!
## Distance Properties
-/

/-- Bit flip distance: minimum weight of nontrivial logical X operators.
    These are nonzero vectors in C₁ \ C₂ (codewords of C₁ not in the stabilizer code C₂).
    Since C₂ ⊆ C₁, this measures how far apart distinct logical X coset representatives are. -/
noncomputable def CSSCode.bitFlipDistance {n : ℕ} (code : CSSCode n) : ℕ :=
  sInf (hammingWeight '' { v | v ∈ code.C1.codewords ∧ v ∉ code.C2.codewords })

/-- Phase flip correction capability: minimum weight of nontrivial logical Z operators.
    These are vectors in C₂⊥ \ C₁⊥ (dual of C₂ but not stabilizers from C₁⊥).
    Since C₂ ⊆ C₁ implies C₁⊥ ⊆ C₂⊥, this is the minimum weight of
    coset representatives of C₂⊥/C₁⊥. -/
noncomputable def CSSCode.phaseFlipDistance {n : ℕ} (code : CSSCode n) : ℕ :=
  sInf (hammingWeight '' { v | v ∈ code.C2.dual ∧ v ∉ code.C1.dual })

/-- CSS code distance is minimum of bit and phase flip distances -/
def CSSCode.distance {n : ℕ} (code : CSSCode n) : ℕ :=
  min code.bitFlipDistance code.phaseFlipDistance

/-!
## Syndromes

For CSS codes, error correction is based on syndrome measurement:
- X syndrome: detects bit flip errors via inner products with C₁⊥
- Z syndrome: detects phase flip errors via inner products with C₂

Two errors have the same syndrome iff they differ by an element of the
appropriate code (C₁ for X errors, C₂⊥ for Z errors).
-/

/-- Inner product over F₂ -/
def innerProductF2 {n : ℕ} (v w : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, v i * w i

/-- X syndrome: the function v ↦ ⟨e, v⟩ for v ∈ C₁⊥.
    Two X error patterns have the same syndrome iff they differ by an element of C₁.
    Abstractly, the X syndrome identifies the coset e + C₁ in F₂ⁿ/C₁. -/
def PauliError.xSyndromeFunc {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    code.C1.dual → ZMod 2 :=
  fun ⟨v, _⟩ => innerProductF2 e.xPattern v

/-- Z syndrome: the function w ↦ ⟨f, w⟩ for w ∈ C₂.
    Two Z error patterns have the same syndrome iff they differ by an element of C₂⊥.
    Abstractly, the Z syndrome identifies the coset f + C₂⊥ in F₂ⁿ/C₂⊥. -/
def PauliError.zSyndromeFunc {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    code.C2.codewords → ZMod 2 :=
  fun ⟨w, _⟩ => innerProductF2 e.zPattern w

/-- Two X error patterns have the same syndrome iff they differ by a codeword in C₁ -/
def PauliError.SameXSyndrome {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.xPattern - e₂.xPattern) ∈ code.C1.codewords

/-- Two Z error patterns have the same syndrome iff they differ by an element of C₂⊥ -/
def PauliError.SameZSyndrome {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.zPattern - e₂.zPattern) ∈ code.C2.dual

/-- **Syndrome Type for CSS Codes**

    The syndrome of a Pauli error captures which coset it belongs to.
    Two errors have the same syndrome iff their syndrome functions are equal.

    The X syndrome is a function C₁⊥ → ZMod 2 (testing against dual codewords)
    The Z syndrome is a function C₂ → ZMod 2 (testing against codewords)

    Key property: errors with equal syndromes get the same correction,
    since correction is defined as a function of the syndrome directly. -/
@[ext]
structure CSSCode.Syndrome {n : ℕ} (code : CSSCode n) where
  /-- Bit-error syndrome, evaluated against each dual codeword of C₁. -/
  xSyn : code.C1.dual → ZMod 2
  /-- Phase-error syndrome, evaluated against each codeword of C₂. -/
  zSyn : code.C2.codewords → ZMod 2

/-- Extract the syndrome of a Pauli error -/
def PauliError.syndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) : code.Syndrome :=
  ⟨e.xSyndromeFunc code, e.zSyndromeFunc code⟩

/-- Two errors have equal syndromes iff they satisfy SameXSyndrome and SameZSyndrome -/
theorem PauliError.syndrome_eq_iff {n : ℕ} (code : CSSCode n) (e₁ e₂ : PauliError n) :
    e₁.syndrome code = e₂.syndrome code ↔
    (e₁.SameXSyndrome code e₂ ∧ e₁.SameZSyndrome code e₂) := by
  constructor
  · -- Same syndrome functions → same coset membership
    intro heq
    constructor
    · -- X syndrome: show e₁.x - e₂.x ∈ C₁
      -- Same X syndrome function means ⟨e₁.x, v⟩ = ⟨e₂.x, v⟩ for all v ∈ C₁⊥
      -- This means ⟨e₁.x - e₂.x, v⟩ = 0 for all v ∈ C₁⊥
      -- By duality (C₁⊥⊥ = C₁ for linear codes), this means e₁.x - e₂.x ∈ C₁
      unfold SameXSyndrome
      -- The syndrome functions being equal means they agree on all inputs
      have hfun : e₁.xSyndromeFunc code = e₂.xSyndromeFunc code := by
        have h := congrArg CSSCode.Syndrome.xSyn heq
        exact h
      -- This means the difference is orthogonal to all of C₁⊥
      -- By double dual theorem: d ∈ C iff d ⊥ C⊥
      rw [LinearCode.mem_codewords_iff_orthogonal_to_dual]
      intro v hv
      -- hfun says the syndrome functions are equal, so they agree on v
      have heq : xSyndromeFunc code e₁ ⟨v, hv⟩ = xSyndromeFunc code e₂ ⟨v, hv⟩ :=
        congrFun hfun ⟨v, hv⟩
      unfold xSyndromeFunc innerProductF2 at heq
      -- heq : ∑ i, e₁.xPattern i * v i = ∑ i, e₂.xPattern i * v i
      -- Goal: ∑ i, (e₁.xPattern - e₂.xPattern) i * v i = 0
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
    · -- Z syndrome: show e₁.z - e₂.z ∈ C₂⊥
      unfold SameZSyndrome
      have hfun : e₁.zSyndromeFunc code = e₂.zSyndromeFunc code := by
        have h := congrArg CSSCode.Syndrome.zSyn heq
        exact h
      -- Same argument: diff is orthogonal to C₂, so diff ∈ C₂⊥
      -- By definition of dual: v ∈ C⊥ iff ∀ c ∈ C.codewords, ⟨v, c⟩ = 0
      rw [LinearCode.dual]
      simp only [Set.mem_ofPred_eq]
      intro c hc
      -- hfun says the syndrome functions are equal, so they agree on c
      have heq : zSyndromeFunc code e₁ ⟨c, hc⟩ = zSyndromeFunc code e₂ ⟨c, hc⟩ :=
        congrFun hfun ⟨c, hc⟩
      unfold zSyndromeFunc innerProductF2 at heq
      -- heq : ∑ i, e₁.zPattern i * c i = ∑ i, e₂.zPattern i * c i
      -- Goal: ∑ i, (e₁.zPattern - e₂.zPattern) i * c i = 0
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
  · -- Same coset membership → same syndrome functions
    intro ⟨hx, hz⟩
    unfold syndrome xSyndromeFunc zSyndromeFunc
    ext
    · -- X syndrome function equality
      rename_i x
      obtain ⟨v, hv⟩ := x
      simp only
      unfold innerProductF2
      -- e₁.x - e₂.x ∈ C₁ and v ∈ C₁⊥, so ⟨v, e₁.x - e₂.x⟩ = 0
      have hdiff : e₁.xPattern - e₂.xPattern ∈ code.C1.codewords := hx
      have horth : v ∈ code.C1.dual := hv
      -- By definition of dual: ⟨v, c⟩ = 0 for all c ∈ C₁
      have hinner : ∑ i, v i * (e₁.xPattern - e₂.xPattern) i = 0 :=
        horth (e₁.xPattern - e₂.xPattern) hdiff
      -- Expand and distribute
      simp only [Pi.sub_apply, mul_sub] at hinner
      rw [Finset.sum_sub_distrib] at hinner
      -- Commutativity: e.x * v = v * e.x
      have hcomm₁ : ∑ i, e₁.xPattern i * v i = ∑ i, v i * e₁.xPattern i := by
        congr 1; ext i; ring
      have hcomm₂ : ∑ i, e₂.xPattern i * v i = ∑ i, v i * e₂.xPattern i := by
        congr 1; ext i; ring
      rw [hcomm₁, hcomm₂]
      -- hinner says ∑(v * e₁.x) - ∑(v * e₂.x) = 0, so they're equal
      exact sub_eq_zero.mp hinner
    · -- Z syndrome function equality
      rename_i x
      obtain ⟨w, hw⟩ := x
      simp only
      unfold innerProductF2
      have hdiff : e₁.zPattern - e₂.zPattern ∈ code.C2.dual := hz
      -- By definition of dual: ⟨diff, w⟩ = 0 for all w ∈ C₂
      have hinner : ∑ i, (e₁.zPattern - e₂.zPattern) i * w i = 0 :=
        hdiff w hw
      simp only [Pi.sub_apply, sub_mul] at hinner
      rw [Finset.sum_sub_distrib] at hinner
      exact sub_eq_zero.mp hinner

/-!
## Symplectic Inner Product and Pauli Commutation

The Pauli group has the commutation relation: (X^a Z^b)(X^c Z^d) = (-1)^{bc} X^{a+c} Z^{b+d}.
For n-qubit Paulis, the phase is (-1)^{⟨b,c⟩} where ⟨·,·⟩ is the inner product over F₂.
-/

/-- Inner product over F₂ (counts positions where both are 1, mod 2).

    **Note on naming**: This computes the standard F₂ bilinear form ⟨a,b⟩ = ∑ aᵢbᵢ,
    not the symplectic form on the full 2n-dimensional Pauli space. The "symplectic"
    structure arises from *how* this is called: `symplecticInnerProduct z₁ x₂` computes
    the z₁·x₂ component of the symplectic pairing ω((x₁,z₁),(x₂,z₂)) = x₁·z₂ + z₁·x₂.
    See `symplecticInnerProduct_eq_innerProductF2` for the definitional equality with
    `innerProductF2`. -/
def symplecticInnerProduct {n : ℕ} (a b : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, a i * b i

/-- The phase factor (-1)^{⟨a,b⟩} arising from Pauli commutation.
    Returns 1 if inner product is 0, returns -1 if inner product is 1. -/
def pauliCommutationSign {n : ℕ} (a b : Fin n → ZMod 2) : ℂ :=
  if symplecticInnerProduct a b = 0 then 1 else -1

/-!
## Error Equivalence

Two Pauli errors are equivalent (act the same on code states UP TO SIGN) if they
differ by a stabilizer. For CSS codes:
- X errors e₁, e₂ are equivalent if e₁ - e₂ ∈ C₂
- Z errors f₁, f₂ are equivalent if f₁ - f₂ ∈ C₁⊥

**IMPORTANT**: Equivalent errors act the same only up to a sign factor
(-1)^{⟨e₂.z, s_x⟩} where s_x = e₁.x - e₂.x is the X-stabilizer difference.
This sign arises from the non-commutativity of X and Z operators.
-/

/-- Two Pauli errors are equivalent on the code space if they differ by a stabilizer -/
def PauliError.EquivOnCode {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.xPattern - e₂.xPattern) ∈ code.C2.codewords ∧
  (e₁.zPattern - e₂.zPattern) ∈ code.C1.dual

/-!
## Minimum-Weight Coset Representatives

For CSS codes, X and Z errors are corrected independently. The key to a working
decoder is to pick minimum-weight representatives from syndrome cosets:
- X coset: all vectors with the same X syndrome (differ by elements of C₁)
- Z coset: all vectors with the same Z syndrome (differ by elements of C₂⊥)

The minimum-weight decoder guarantees that the correction has weight ≤ any
error in the same coset, which is essential for the proof.
-/

/-- The X-syndrome coset of a vector: all vectors with the same X syndrome.
    Two vectors are in the same X coset iff they differ by an element of C₁. -/
def CSSCode.xCoset {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set (Fin n → ZMod 2) :=
  { w | (v - w) ∈ code.C1.codewords }

/-- The Z-syndrome coset of a vector: all vectors with the same Z syndrome.
    Two vectors are in the same Z coset iff they differ by an element of C₂⊥. -/
def CSSCode.zCoset {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set (Fin n → ZMod 2) :=
  { w | (v - w) ∈ code.C2.dual }

/-- Every vector is in its own X coset. -/
theorem CSSCode.mem_xCoset_self {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    v ∈ code.xCoset v := by
  unfold xCoset
  simp only [Set.mem_ofPred_eq, sub_self]
  exact code.C1.zero_mem_codewords

/-- Every vector is in its own Z coset. -/
theorem CSSCode.mem_zCoset_self {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    v ∈ code.zCoset v := by
  unfold zCoset
  simp only [Set.mem_ofPred_eq, sub_self]
  intro c _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- X cosets are nonempty. -/
theorem CSSCode.xCoset_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.xCoset v).Nonempty :=
  ⟨v, code.mem_xCoset_self v⟩

/-- Z cosets are nonempty. -/
theorem CSSCode.zCoset_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.zCoset v).Nonempty :=
  ⟨v, code.mem_zCoset_self v⟩

/-- The set of Hamming weights achieved by elements of an X coset. -/
def CSSCode.xCosetWeights {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set ℕ :=
  hammingWeight '' (code.xCoset v)

/-- The set of Hamming weights achieved by elements of a Z coset. -/
def CSSCode.zCosetWeights {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set ℕ :=
  hammingWeight '' (code.zCoset v)

/-- X coset weights are nonempty. -/
theorem CSSCode.xCosetWeights_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.xCosetWeights v).Nonempty := by
  unfold xCosetWeights
  exact Set.Nonempty.image hammingWeight (code.xCoset_nonempty v)

/-- Z coset weights are nonempty. -/
theorem CSSCode.zCosetWeights_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.zCosetWeights v).Nonempty := by
  unfold zCosetWeights
  exact Set.Nonempty.image hammingWeight (code.zCoset_nonempty v)

/-- The minimum X weight in a coset. -/
noncomputable def CSSCode.minXWeight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : ℕ :=
  sInf (code.xCosetWeights v)

/-- The minimum Z weight in a coset. -/
noncomputable def CSSCode.minZWeight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : ℕ :=
  sInf (code.zCosetWeights v)

/-- There exists an element of the X coset achieving the minimum weight. -/
theorem CSSCode.exists_minXWeight_rep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    ∃ w ∈ code.xCoset v, hammingWeight w = code.minXWeight v := by
  have hne := code.xCosetWeights_nonempty v
  -- Nat.sInf_mem says: if s is nonempty, then sInf s ∈ s
  have hinf_mem : code.minXWeight v ∈ code.xCosetWeights v := Nat.sInf_mem hne
  -- The infimum is in the image of hammingWeight
  unfold xCosetWeights at hinf_mem
  rw [Set.mem_image] at hinf_mem
  obtain ⟨w, hw_coset, hw_wt⟩ := hinf_mem
  exact ⟨w, hw_coset, hw_wt⟩

/-- There exists an element of the Z coset achieving the minimum weight. -/
theorem CSSCode.exists_minZWeight_rep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    ∃ w ∈ code.zCoset v, hammingWeight w = code.minZWeight v := by
  have hne := code.zCosetWeights_nonempty v
  have hinf_mem : code.minZWeight v ∈ code.zCosetWeights v := Nat.sInf_mem hne
  unfold zCosetWeights at hinf_mem
  rw [Set.mem_image] at hinf_mem
  obtain ⟨w, hw_coset, hw_wt⟩ := hinf_mem
  exact ⟨w, hw_coset, hw_wt⟩

/-- Minimum-weight X coset representative (chosen by Classical.choose). -/
noncomputable def CSSCode.minWeightXRep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  Classical.choose (code.exists_minXWeight_rep v)

/-- Minimum-weight Z coset representative (chosen by Classical.choose). -/
noncomputable def CSSCode.minWeightZRep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  Classical.choose (code.exists_minZWeight_rep v)

/-- The min-weight X rep is in the X coset. -/
theorem CSSCode.minWeightXRep_mem {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    code.minWeightXRep v ∈ code.xCoset v :=
  (Classical.choose_spec (code.exists_minXWeight_rep v)).1

/-- The min-weight Z rep is in the Z coset. -/
theorem CSSCode.minWeightZRep_mem {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    code.minWeightZRep v ∈ code.zCoset v :=
  (Classical.choose_spec (code.exists_minZWeight_rep v)).1

/-- The min-weight X rep achieves the minimum weight. -/
theorem CSSCode.minWeightXRep_weight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightXRep v) = code.minXWeight v :=
  (Classical.choose_spec (code.exists_minXWeight_rep v)).2

/-- The min-weight Z rep achieves the minimum weight. -/
theorem CSSCode.minWeightZRep_weight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightZRep v) = code.minZWeight v :=
  (Classical.choose_spec (code.exists_minZWeight_rep v)).2

/-- Key lemma: The min X weight is at most the weight of any element in the coset. -/
theorem CSSCode.minXWeight_le {n : ℕ} (code : CSSCode n) (v w : Fin n → ZMod 2)
    (hw : w ∈ code.xCoset v) : code.minXWeight v ≤ hammingWeight w := by
  unfold minXWeight xCosetWeights
  apply Nat.sInf_le
  exact ⟨w, hw, rfl⟩

/-- Key lemma: The min Z weight is at most the weight of any element in the coset. -/
theorem CSSCode.minZWeight_le {n : ℕ} (code : CSSCode n) (v w : Fin n → ZMod 2)
    (hw : w ∈ code.zCoset v) : code.minZWeight v ≤ hammingWeight w := by
  unfold minZWeight zCosetWeights
  apply Nat.sInf_le
  exact ⟨w, hw, rfl⟩

/-- The min-weight X rep has weight at most the weight of the original vector. -/
theorem CSSCode.minWeightXRep_weight_le {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightXRep v) ≤ hammingWeight v := by
  rw [code.minWeightXRep_weight v]
  exact code.minXWeight_le v v (code.mem_xCoset_self v)

/-- The min-weight Z rep has weight at most the weight of the original vector. -/
theorem CSSCode.minWeightZRep_weight_le {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightZRep v) ≤ hammingWeight v := by
  rw [code.minWeightZRep_weight v]
  exact code.minZWeight_le v v (code.mem_zCoset_self v)

/-- Minimum-weight Pauli correction for an error.
    This picks minimum-weight representatives for both X and Z components. -/
noncomputable def CSSCode.minWeightCorrection {n : ℕ} (code : CSSCode n)
    (e : PauliError n) : PauliError n :=
  ⟨code.minWeightXRep e.xPattern, code.minWeightZRep e.zPattern⟩

/-- The min-weight correction has the same X syndrome as the original error. -/
theorem CSSCode.minWeightCorrection_sameXSyndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    e.SameXSyndrome code (code.minWeightCorrection e) := by
  unfold PauliError.SameXSyndrome minWeightCorrection
  simp only
  exact code.minWeightXRep_mem e.xPattern

/-- The min-weight correction has the same Z syndrome as the original error. -/
theorem CSSCode.minWeightCorrection_sameZSyndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    e.SameZSyndrome code (code.minWeightCorrection e) := by
  unfold PauliError.SameZSyndrome minWeightCorrection
  simp only
  exact code.minWeightZRep_mem e.zPattern

/-- The min-weight correction has X weight at most the original error's X weight. -/
theorem CSSCode.minWeightCorrection_xWeight_le {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    (code.minWeightCorrection e).xWeight ≤ e.xWeight := by
  unfold PauliError.xWeight minWeightCorrection
  simp only
  exact code.minWeightXRep_weight_le e.xPattern

/-- The min-weight correction has Z weight at most the original error's Z weight. -/
theorem CSSCode.minWeightCorrection_zWeight_le {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    (code.minWeightCorrection e).zWeight ≤ e.zWeight := by
  unfold PauliError.zWeight minWeightCorrection
  simp only
  exact code.minWeightZRep_weight_le e.zPattern

/-!
## Main Error Correction Theorem

The fundamental theorem of CSS codes: there exists a syndrome-based recovery
procedure that corrects all errors within the correction capability.

Key insight: The recovery map depends ONLY on the syndrome, not on knowing
which specific error occurred. Different correctable errors with the same
syndrome are equivalent (differ by a stabilizer).
-/

/-- **Syndrome Distinguishes Correctable Errors** (Key Lemma)

    If two errors e₁ and e₂ both have weight ≤ t and have the same syndrome,
    then they are equivalent on the code space (differ by a stabilizer).

    **Proof idea**: Same syndrome means e₁ - e₂ ∈ C₁ (for X) and e₁ - e₂ ∈ C₂⊥ (for Z).
    By triangle inequality, wt(e₁ - e₂) ≤ wt(e₁) + wt(e₂) ≤ 2t < d.
    A nonzero codeword in C₁ has weight ≥ d(C₁) ≥ d, contradiction.
    So e₁ - e₂ = 0 (for X errors) or e₁ - e₂ ∈ C₂ (stabilizer).

    This is the core of why CSS codes work: low-weight errors with the
    same syndrome must be equivalent. -/
theorem CSSCode.syndrome_determines_equivalence {n : ℕ} (code : CSSCode n)
    (t : ℕ) (ht : 2 * t + 1 ≤ code.distance)
    (e₁ e₂ : PauliError n)
    (hx₁ : e₁.xWeight ≤ t) (hx₂ : e₂.xWeight ≤ t)
    (hz₁ : e₁.zWeight ≤ t) (hz₂ : e₂.zWeight ≤ t)
    (hsame_x : e₁.SameXSyndrome code e₂)
    (hsame_z : e₁.SameZSyndrome code e₂) :
    e₁.EquivOnCode code e₂ := by
  constructor
  · -- X pattern: show diff ∈ C2.codewords
    -- Key insight: diff ∈ C1.codewords (from SameXSyndrome) and wt(diff) ≤ 2t < d.
    -- Either diff ∈ C2 (done) or diff ∈ C1 \ C2, giving bitFlipDistance ≤ wt(diff) ≤ 2t < d.
    have hdiff : e₁.xPattern - e₂.xPattern ∈ code.C1.codewords := hsame_x
    by_cases hC2 : e₁.xPattern - e₂.xPattern ∈ code.C2.codewords
    · exact hC2
    · exfalso
      -- diff ∈ C1 \ C2, so bitFlipDistance ≤ wt(diff)
      have hmin : code.bitFlipDistance ≤ hammingWeight (e₁.xPattern - e₂.xPattern) := by
        unfold CSSCode.bitFlipDistance
        apply Nat.sInf_le
        rw [Set.mem_image]
        exact ⟨e₁.xPattern - e₂.xPattern, ⟨hdiff, hC2⟩, rfl⟩
      -- Triangle inequality: wt(e₁ - e₂) ≤ wt(e₁) + wt(e₂)
      have hwt_bound : hammingWeight (e₁.xPattern - e₂.xPattern) ≤ e₁.xWeight + e₂.xWeight := by
        unfold PauliError.xWeight
        have htri := hammingDistance_triangle e₁.xPattern 0 e₂.xPattern
        unfold hammingDistance at htri
        simp only [sub_zero, zero_sub] at htri
        -- In ZMod 2, -x = x (characteristic 2)
        have hneg : -e₂.xPattern = e₂.xPattern := by
          ext i; simp only [Pi.neg_apply]; exact CharTwo.neg_eq (e₂.xPattern i)
        rw [hneg] at htri
        exact htri
      have hwt_2t : e₁.xWeight + e₂.xWeight ≤ 2 * t := by omega
      have hdist_bf : code.distance ≤ code.bitFlipDistance := Nat.min_le_left _ _
      omega
  · -- Z pattern: show diff ∈ C1.dual
    -- diff ∈ C2.dual (from SameZSyndrome). Either diff ∈ C1.dual (done) or
    -- diff ∈ C2.dual \ C1.dual, giving phaseFlipDistance ≤ wt(diff) ≤ 2t < distance.
    have hdiff_in_C2_dual : e₁.zPattern - e₂.zPattern ∈ code.C2.dual := hsame_z
    by_cases h_stab : e₁.zPattern - e₂.zPattern ∈ code.C1.dual
    · exact h_stab
    · exfalso
      -- phaseFlipDistance ≤ wt(diff) since diff ∈ C2.dual \ C1.dual
      have hmin : code.phaseFlipDistance ≤ hammingWeight (e₁.zPattern - e₂.zPattern) := by
        unfold CSSCode.phaseFlipDistance
        apply Nat.sInf_le
        rw [Set.mem_image]
        exact ⟨e₁.zPattern - e₂.zPattern, ⟨hdiff_in_C2_dual, h_stab⟩, rfl⟩
      have hwt_bound : hammingWeight (e₁.zPattern - e₂.zPattern) ≤ e₁.zWeight + e₂.zWeight := by
        unfold PauliError.zWeight
        have htri := hammingDistance_triangle e₁.zPattern 0 e₂.zPattern
        unfold hammingDistance at htri
        simp only [sub_zero, zero_sub] at htri
        have hneg : -e₂.zPattern = e₂.zPattern := by
          ext i; simp only [Pi.neg_apply]; exact CharTwo.neg_eq (e₂.zPattern i)
        rw [hneg] at htri
        exact htri
      have hwt_2t : e₁.zWeight + e₂.zWeight ≤ 2 * t := by omega
      have hdist_pf : code.distance ≤ code.phaseFlipDistance := Nat.min_le_right _ _
      omega

/-!
## Helper Lemmas for equiv_act_same

The proof of `equiv_act_same` requires showing that Pauli errors related by stabilizers
act the same (up to phase) on code states. This involves:
1. Decomposing the error operators
2. Using that stabilizers act trivially on code states
3. Computing the phase from Pauli commutation
-/

/-- Helper: The symplectic inner product of first components times inner product of rest. -/
lemma symplecticInnerProduct_succ {n : ℕ} (a b : Fin (n + 1) → ZMod 2) :
    symplecticInnerProduct a b =
      a 0 * b 0 + symplecticInnerProduct (a ∘ Fin.succ) (b ∘ Fin.succ) := by
  unfold symplecticInnerProduct
  rw [Fin.sum_univ_succ]
  simp only [Function.comp_apply]

/-- Helper lemma: ZMod 2 dichotomy - any element is 0 or 1 -/
private lemma ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  have hlt : v < 2 := hv
  interval_cases v
  · left; rfl
  · right; rfl

/-- pauliCommutationSign decomposes over Fin (n+1) as product of first and rest.
    This is the key to the inductive proof of pauliError_mul. -/
lemma pauliCommutationSign_succ {n : ℕ} (a b : Fin (n + 1) → ZMod 2) :
    pauliCommutationSign a b =
    (if a 0 * b 0 = 1 then -1 else 1 : ℂ) *
    pauliCommutationSign (a ∘ Fin.succ) (b ∘ Fin.succ) := by
  unfold pauliCommutationSign
  rw [symplecticInnerProduct_succ]
  -- Now we have: if (a 0 * b 0 + inner_rest) = 0 then 1 else -1
  --            = (if a 0 * b 0 = 1 then -1 else 1) * (if inner_rest = 0 then 1 else -1)
  set x := a 0 * b 0 with hx_def
  set y := symplecticInnerProduct (a ∘ Fin.succ) (b ∘ Fin.succ) with hy_def
  rcases ZMod2_eq_zero_or_one x with hx0 | hx1 <;> rcases ZMod2_eq_zero_or_one y with hy0 | hy1
  · -- x = 0, y = 0: sum = 0
    simp only [hx0, hy0, zero_add, ↓reduceIte]
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    simp only [hne, ↓reduceIte, mul_one]
  · -- x = 0, y = 1: sum = 1
    simp only [hx0, hy1, zero_add]
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hne, h1ne, ↓reduceIte, one_mul]
  · -- x = 1, y = 0: sum = 1
    simp only [hx1, hy0, add_zero, ↓reduceIte]
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h1ne, ↓reduceIte, mul_one]
  · -- x = 1, y = 1: sum = 0 (1 + 1 = 0 in ZMod 2)
    have hsum : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [hx1, hy1, hsum, ↓reduceIte]
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h1ne, ↓reduceIte]
    ring

/-- Helper: (-1)^v for v ∈ ZMod 2, as a complex number -/
private def negOnePow (v : ZMod 2) : ℂ := if v = 0 then 1 else -1

/-- Key property: negOnePow (a + b) = negOnePow a * negOnePow b -/
private lemma negOnePow_add (a b : ZMod 2) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  match a, b with
  | 0, 0 => simp only [negOnePow, add_zero, ↓reduceIte, mul_one]
  | 0, 1 => simp only [negOnePow, zero_add, ↓reduceIte, one_mul]
  | 1, 0 => simp only [negOnePow, add_zero, ↓reduceIte, mul_one]
  | 1, 1 => -- 1 + 1 = 0 in ZMod 2
    unfold negOnePow
    have h_add : (1 : ZMod 2) + 1 = 0 := by decide
    have h_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h_add, ↓reduceIte, h_one_ne_zero, neg_mul_neg, mul_one]

/-- pauliCommutationSign is negOnePow of the symplectic inner product -/
private lemma pauliCommutationSign_eq_negOnePow {n : ℕ} (a b : Fin n → ZMod 2) :
    pauliCommutationSign a b = negOnePow (symplecticInnerProduct a b) := by
  unfold pauliCommutationSign negOnePow
  rfl

/-- Helper: pauliCommutationSign splits over sums of inner products -/
lemma pauliCommutationSign_mul {n : ℕ} (a₁ a₂ b₁ b₂ : Fin n → ZMod 2)
    (h : symplecticInnerProduct (a₁ + a₂) (b₁ + b₂) =
         symplecticInnerProduct a₁ b₁ + symplecticInnerProduct a₁ b₂ +
         symplecticInnerProduct a₂ b₁ + symplecticInnerProduct a₂ b₂) :
    pauliCommutationSign (a₁ + a₂) (b₁ + b₂) =
    pauliCommutationSign a₁ b₁ * pauliCommutationSign a₁ b₂ *
    pauliCommutationSign a₂ b₁ * pauliCommutationSign a₂ b₂ := by
  simp only [pauliCommutationSign_eq_negOnePow, h]
  -- Use negOnePow_add repeatedly
  rw [negOnePow_add, negOnePow_add, negOnePow_add]

/-- The symplectic inner product equals the inner product over F₂.
    Just a naming convenience. -/
lemma symplecticInnerProduct_eq_innerProductF2 {n : ℕ}
    (a b : Fin n → ZMod 2) : symplecticInnerProduct a b = innerProductF2 a b := rfl

/-- Helper: pauliCommutationSign is 1 when inner product is 0 -/
lemma pauliCommutationSign_zero {n : ℕ} (a b : Fin n → ZMod 2)
    (h : symplecticInnerProduct a b = 0) : pauliCommutationSign a b = 1 := by
  unfold pauliCommutationSign
  simp only [h, ↓reduceIte]

/-- Helper: pauliCommutationSign is -1 when inner product is 1 -/
lemma pauliCommutationSign_one {n : ℕ} (a b : Fin n → ZMod 2)
    (h : symplecticInnerProduct a b = 1) : pauliCommutationSign a b = -1 := by
  unfold pauliCommutationSign
  simp only [h]
  -- 1 ≠ 0 in ZMod 2
  have hne : (1 : ZMod 2) ≠ 0 := by norm_num
  simp only [hne, ↓reduceIte]

/-- Helper: The inner product of a zero pattern with anything is 0 -/
lemma symplecticInnerProduct_zero_left {n : ℕ} (b : Fin n → ZMod 2) :
    symplecticInnerProduct (fun _ => 0) b = 0 := by
  unfold symplecticInnerProduct
  simp only [zero_mul, Finset.sum_const_zero]

/-- Helper: The inner product of anything with a zero pattern is 0 -/
lemma symplecticInnerProduct_zero_right {n : ℕ} (a : Fin n → ZMod 2) :
    symplecticInnerProduct a (fun _ => 0) = 0 := by
  unfold symplecticInnerProduct
  simp only [mul_zero, Finset.sum_const_zero]

end Math.CodingTheory.CSS

end
