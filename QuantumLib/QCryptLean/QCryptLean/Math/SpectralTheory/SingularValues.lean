import QCryptLean.Math.LinearAlgebra.SubmoduleDimension
import QCryptLean.Math.SpectralTheory.Eigenvalues
import QCryptLean.Math.SpectralTheory.ExteriorPowerNorm
import QCryptLean.Math.SpectralTheory.KyFan.Basic
import QCryptLean.Math.SpectralTheory.LiebThirringHigher
import QCryptLean.Math.SpectralTheory.TensorSpectrum

/-!
# Singular values and exterior powers

Sorted singular values and an orthonormal singular frame identify leading products with
exterior-power operator norms and prove their power inequalities.

## Main declarations

Definitions include `sortedSingularValues`.
Main results include `singularValue_prod_eq_exteriorPower_opNorm`,
`singularValue_prod_pow_le_pow_singularValue`.

## References

Bhatia, *Matrix Analysis*, §IX.2.
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory


/-- `sqrt(P) * Q * sqrt(P)` is PSD when `P` and `Q` are PSD. -/
lemma posSemidef_sqrt_conj {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (_hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (CFC.sqrt P * Q * CFC.sqrt P).PosSemidef := by
  have hSqrt := (CFC.sqrt_nonneg (a := P)).posSemidef
  have hSqrtH : (CFC.sqrt P).conjTranspose = CFC.sqrt P :=
    hSqrt.isHermitian
  have h := hQ.conjTranspose_mul_mul_same (CFC.sqrt P)
  rwa [hSqrtH] at h

/-! ## Singular values and the Araki easy-half via Weyl product inequalities

The integer "easy half" `tr(Bᵐ·(Bᴴ)ᵐ).re ≤ tr((Bᴴ·B)ᵐ).re` is the trace form of
Araki's antisymmetric-tensor-power inequality. Following Bhatia, *Matrix
Analysis*, IX.2, we prove it using the **singular values** `sᵢ(B)` (the
descending square roots of the eigenvalues of `Bᴴ·B`):

* `tr(Bᵐ·(Bᴴ)ᵐ).re = ‖Bᵐ‖²_F = Σᵢ sᵢ(Bᵐ)²`  (a Frobenius identity),
* `Σᵢ sᵢ(Bᵐ)² ≤ Σᵢ sᵢ(B)²ᵐ`  (Weyl's product inequality `sₖ(Bᵐ) ≤ sₖ(B)ᵐ`,
  summed via the `⋀ᵏ` compound-matrix log-majorization), and
* `Σᵢ sᵢ(B)²ᵐ = tr((Bᴴ·B)ᵐ).re`  (since `sᵢ(B)² = λᵢ(Bᴴ·B)` and
  `tr(Pᵐ) = Σ λᵢᵐ` for the PSD matrix `P = Bᴴ·B`).

The two compound-matrix facts are the genuine spectral content and are stated as
the honest leaves `singularValue_prod_pow_le_pow_singularValue` and
`trace_pow_mul_conjTranspose_pow_re_le_singularValue_sum`; the closing identity
`singularValue_pow_sum_eq_trace` is proved here. -/

/-- The descending (`eigenvalues₀`) eigenvalues of a positive-semidefinite
matrix are non-negative. They enumerate the same values as the `n`-indexed
`eigenvalues` (which are nonneg for PSD), reindexed by an equivalence. -/
lemma _root_.Matrix.PosSemidef.eigenvalues₀_nonneg {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (j : Fin (Fintype.card (Fin N))) :
    0 ≤ hA.1.eigenvalues₀ j := by
  have h2 := hA.eigenvalues_nonneg
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N))) j)
  rw [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] at h2
  exact h2

/-- The singular values of `B`, sorted in non-increasing order: `sᵢ(B)` is the
descending square root of the `i`-th eigenvalue of the positive-semidefinite
matrix `Bᴴ·B`. Indexed by `ℕ` (returning `0` past index `N-1`) so that both
power sums over `Fin N` and `⋀ᵏ` partial products over `Finset.range k` read off
the same family.

Explicit construction (no choice): `Bᴴ·B` is PSD (`posSemidef_conjTranspose_mul`),
its `eigenvalues₀` are the descending eigenvalues, and `Real.sqrt` of a
non-increasing nonneg family is non-increasing. Reference: Bhatia, *Matrix
Analysis*, IX.2 (singular value decomposition). -/
noncomputable def sortedSingularValues {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) :
    ℕ → ℝ :=
  fun i =>
    if h : i < Fintype.card (Fin N) then
      Real.sqrt ((posSemidef_conjTranspose_mul B).1.eigenvalues₀ ⟨i, h⟩)
    else 0

/-- `sortedSingularValues B i` is non-negative (it is a real square root). -/
lemma sortedSingularValues_nonneg {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) :
    0 ≤ sortedSingularValues B i := by
  unfold sortedSingularValues
  split
  · exact Real.sqrt_nonneg _
  · exact le_refl 0

/-- Closing identity: the singular-value power sum equals the PSD trace.

`Σᵢ sᵢ(B)²ᵐ = tr((Bᴴ·B)ᵐ).re`. Since `sᵢ(B)² = λᵢ(Bᴴ·B)` (the eigenvalues of
the PSD matrix `Bᴴ·B`, which are `≥ 0`), we have `sᵢ(B)²ᵐ = λᵢ(Bᴴ·B)ᵐ`, and
`tr(Pᵐ) = Σᵢ λᵢ(P)ᵐ` for the PSD matrix `P = Bᴴ·B`. The sorted (`eigenvalues₀`)
and unsorted (`eigenvalues`) families differ by a permutation, which the sum
ignores. Reference: Bhatia, *Matrix Analysis*, IX.2. -/
lemma singularValue_pow_sum_eq_trace {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    (∑ i : Fin N, (sortedSingularValues B (i : ℕ)) ^ (2 * m))
      = ((Bᴴ * B) ^ m).trace.re := by
  set hP := posSemidef_conjTranspose_mul B with hP_def
  have hbnd : ∀ i : Fin N, (i : ℕ) < Fintype.card (Fin N) := fun i => by
    rw [Fintype.card_fin]; exact i.isLt
  -- The descending eigenvalues of `Bᴴ·B`, reindexed by `Fin N`.
  set lam : Fin N → ℝ := fun i => hP.1.eigenvalues₀ ⟨(i : ℕ), hbnd i⟩ with hlam
  -- `tr((Bᴴ·B)ᵐ).re = Σᵢ λᵢ(Bᴴ·B)ᵐ` (real, via the unsorted eigenvalues).
  have htrace : ((Bᴴ * B) ^ m).trace = ∑ i : Fin N, (hP.1.eigenvalues i : ℂ) ^ m :=
    trace_pow_eq_sum_eigenvalues_pow (Bᴴ * B) hP.1 m
  -- Each left summand is `(lam i)ᵐ` (`sᵢ(B)²ᵐ = λᵢ(Bᴴ·B)ᵐ`, `λ ≥ 0`).
  have hsq : ∀ i : Fin N, (sortedSingularValues B (i : ℕ)) ^ (2 * m) = (lam i) ^ m := by
    intro i
    have hnn : 0 ≤ lam i := Matrix.PosSemidef.eigenvalues₀_nonneg hP ⟨(i : ℕ), hbnd i⟩
    rw [hlam] at hnn ⊢
    simp only [sortedSingularValues, dite_eq_left (hbnd i), pow_mul, Real.sq_sqrt hnn]
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  -- Reindex sorted → unsorted via `eigenPerm`; the complex power sum equals the trace.
  set e₀f := Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin (Bᴴ * B) hP.1 with he₀f
  have hcast : ((∑ i : Fin N, (lam i) ^ m : ℝ) : ℂ)
      = ∑ i : Fin N, (hP.1.eigenvalues i : ℂ) ^ m := by
    push_cast
    have hstep : (∑ i : Fin N, (lam i : ℂ) ^ m) = ∑ i : Fin N, (e₀f i : ℂ) ^ m := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hlam, he₀f, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin, Function.comp_apply,
        Math.LinearAlgebra.SubmoduleDim.finToCardFin]
    have hperm : (∑ i : Fin N, (hP.1.eigenvalues i : ℂ) ^ m)
        = ∑ i : Fin N, (e₀f (eigenPerm N i) : ℂ) ^ m := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [he₀f, eigenvalues_eq_eigenvalues₀Fin_comp (Bᴴ * B) hP.1 i]
    rw [hstep, hperm, ← Equiv.sum_comp (eigenPerm N)]
  -- Conclude on real parts.
  rw [show ((Bᴴ * B) ^ m).trace.re = (∑ i : Fin N, (lam i) ^ m : ℝ) by
    rw [htrace, ← hcast, Complex.ofReal_re]]

/-- **Frobenius identity** for the easy-half product trace.

`tr(Bᵐ·(Bᴴ)ᵐ).re = Σᵢ sᵢ(Bᵐ)²`. Since `(Bᴴ)ᵐ = (Bᵐ)ᴴ` and trace is cyclic,
`tr(Bᵐ·(Bᴴ)ᵐ) = tr((Bᵐ)ᴴ·Bᵐ) = tr((Bᵐ)ᴴ·Bᵐ)`, whose real part is the
singular-value power sum `Σᵢ sᵢ(Bᵐ)²` by `singularValue_pow_sum_eq_trace` at the
matrix `Bᵐ` and exponent `1`. This is `‖Bᵐ‖²_F` written in singular values.
Reference: Bhatia, *Matrix Analysis*, IX.2. -/
lemma trace_pow_mul_conjTranspose_pow_eq_singularValue_pow_two_sum {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    (B ^ m * (Bᴴ) ^ m).trace.re
      = ∑ i : Fin N, (sortedSingularValues (B ^ m) (i : ℕ)) ^ 2 := by
  have h := singularValue_pow_sum_eq_trace (B ^ m) 1
  simp only [pow_one, mul_one] at h
  rw [h, Matrix.conjTranspose_pow, Matrix.trace_mul_comm]

/-- The singular values of `B`, listed in non-increasing order: for `i ≤ j`,
`sⱼ(B) ≤ sᵢ(B)`. They are `Real.sqrt` of the descending eigenvalues
(`eigenvalues₀`, antitone by `eigenvalues₀_antitone`) of the PSD matrix `Bᴴ·B`,
and `Real.sqrt` is monotone; past index `N-1` the family is `0`, which is `≤` any
square root. Reference: Bhatia, *Matrix Analysis*, IX.2 (SVD ordering). -/
lemma sortedSingularValues_antitone {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) :
    ∀ i j : ℕ, i ≤ j → sortedSingularValues B j ≤ sortedSingularValues B i := by
  intro i j hij
  unfold sortedSingularValues
  by_cases hj : j < Fintype.card (Fin N)
  · have hi : i < Fintype.card (Fin N) := lt_of_le_of_lt hij hj
    rw [dite_eq_left hi, dite_eq_left hj]
    apply Real.sqrt_le_sqrt
    exact (posSemidef_conjTranspose_mul B).1.eigenvalues₀_antitone (by exact_mod_cast hij)
  · rw [dite_eq_right hj]
    split
    · exact Real.sqrt_nonneg _
    · exact le_refl 0

/-- A strictly monotone family `g : Fin k → ℕ` out-grows its index: `(j : ℕ) ≤ g j`.
Strong induction on `j.val`: the predecessor index `j-1` (when `j > 0`) has value
`≤ g(j-1) < g j`. -/
private lemma le_strictMono_fin_nat {k : ℕ} (g : Fin k → ℕ) (hg : StrictMono g)
    (j : Fin k) : (j : ℕ) ≤ g j := by
  rcases k with _ | k'
  · exact absurd j.isLt (by omega)
  · induction j using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h1 : g i.castSucc < g i.succ := hg (by simp [Fin.lt_def])
      have h2 : (i.castSucc : ℕ) ≤ g i.castSucc := ih
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega

/-- The `j`-th element (in increasing order) of a `k`-subset `S` of `Fin N` has
value at least `j`: `j ≤ (S.orderEmbOfFin h j : ℕ)`. The sorted enumeration of a
subset is strictly monotone into `ℕ`, and a strictly monotone family on `Fin k`
out-grows its index. Used to bound a subset product by the leading product of an
antitone family. -/
private lemma le_val_orderEmbOfFin {N k : ℕ} (S : Finset (Fin N)) (h : S.card = k)
    (j : Fin k) : (j : ℕ) ≤ ((S.orderEmbOfFin h j : Fin N) : ℕ) := by
  -- `g : Fin k → ℕ`, `g = val ∘ orderEmbOfFin`, is strictly monotone; hence `j ≤ g j`.
  have hmono : StrictMono (fun j : Fin k => ((S.orderEmbOfFin h j : Fin N) : ℕ)) :=
    fun a b hab => by exact_mod_cast (S.orderEmbOfFin h).strictMono hab
  exact le_strictMono_fin_nat _ hmono j

/-- **Max subset product = leading product** (the combinatorial half of the SVD
variational identity): for an antitone non-negative family `sᵢ = sortedSingularValues X i`,
the supremum over all `k`-subsets `S ⊆ Fin N` of the subset products `∏_{i∈S} sᵢ`
equals the product over the leading `k` indices `∏_{i<k} sᵢ`.

The leading product dominates every subset product (a `k`-subset's `j`-th smallest
element has value `≥ j`, and the antitone `s` makes `s(aⱼ) ≤ s(j)`); for `k ≤ N`
it is attained by `S = {0,…,k-1}`, and for `k > N` both sides vanish (the subtype
of `k`-subsets is empty, `sSup ∅ = 0`, and `sₖ(X) = 0` past index `N-1`).
Reference: Bhatia,
*Matrix Analysis*, IX.2 (the top-`k` singular-value product is the largest
`k`-fold product). -/
lemma max_subset_prod_eq_leading_prod {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    (⨆ (S : {S : Finset (Fin N) // S.card = k}),
        ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i)
      = ∏ i ∈ Finset.range k, sortedSingularValues X i := by
  classical
  -- Each subset product is ≤ the leading product.
  have hsub_le : ∀ S : {S : Finset (Fin N) // S.card = k},
      (∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i)
        ≤ ∏ i ∈ Finset.range k, sortedSingularValues X i := by
    rintro ⟨S, hS⟩
    -- Reindex the subset product through the sorted order embedding.
    have hreindex : ∏ i ∈ S, sortedSingularValues X i
        = ∏ j : Fin k, sortedSingularValues X (S.orderEmbOfFin hS j) := by
      conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S hS]
      rw [Finset.prod_map]
      rfl
    have hlead : ∏ i ∈ Finset.range k, sortedSingularValues X i
        = ∏ j : Fin k, sortedSingularValues X (j : ℕ) := by
      rw [Finset.prod_range fun i => sortedSingularValues X i]
    rw [hreindex, hlead]
    apply Finset.prod_le_prod₀
    · exact fun j _ => sortedSingularValues_nonneg X _
    · intro j _
      exact sortedSingularValues_antitone X (j : ℕ) _ (le_val_orderEmbOfFin S hS j)
  rcases Nat.lt_or_ge N k with hkN | hkN
  swap
  · -- `k ≤ N`: the leading product is attained by the canonical `k`-subset `{0,…,k-1}`.
    set Slead : Finset (Fin N) := Finset.map (Fin.castLEEmb hkN) (Finset.univ : Finset (Fin k))
      with hSlead
    have hcard : Slead.card = k := by
      rw [hSlead, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hprodlead : ∏ i ∈ Slead, sortedSingularValues X i
        = ∏ i ∈ Finset.range k, sortedSingularValues X i := by
      rw [hSlead, Finset.prod_map, Finset.prod_range fun i => sortedSingularValues X i]
      exact Finset.prod_congr rfl (fun j _ => by simp [Fin.castLEEmb])
    have hne : Nonempty {S : Finset (Fin N) // S.card = k} := ⟨⟨Slead, hcard⟩⟩
    apply le_antisymm
    · apply ciSup_le
      intro S
      exact hsub_le S
    · rw [← hprodlead]
      exact le_ciSup (f := fun S : {S : Finset (Fin N) // S.card = k} =>
        ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i)
        (Set.Finite.bddAbove (Set.finite_range _)) ⟨Slead, hcard⟩
  · -- `k > N`: no `k`-subset of `Fin N` exists, the `iSup` is over an empty type, and the
    -- leading product vanishes (`sₖ(X) = 0` for index `≥ N`).
    have hempty : IsEmpty {S : Finset (Fin N) // S.card = k} := by
      refine ⟨fun S => ?_⟩
      have hle : S.1.card ≤ N := by
        calc S.1.card ≤ (Finset.univ : Finset (Fin N)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = N := by rw [Finset.card_univ, Fintype.card_fin]
      rw [S.2] at hle; omega
    have hsup0 : (⨆ (S : {S : Finset (Fin N) // S.card = k}),
        ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i) = 0 :=
      Real.iSup_of_isEmpty _
    rw [hsup0]
    -- The leading product contains the zero factor at index `N` (since `N < k`).
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hkN)
    simp only [sortedSingularValues, Fintype.card_fin]
    rw [dite_eq_right (by omega)]

/-- **Adjoint pairing of `toEuclideanLin`** (the defining relation of the
Hermitian transpose): for the Euclidean linear maps of a square matrix `X` and
its product `Xᴴ·X`,
`⟨X a, X b⟩ = ⟨a, (Xᴴ·X) b⟩`.

This is `⟨X a, X b⟩ = ⟨Xᴴ(X a)? …⟩`, but more directly: expanding the Euclidean
inner product as `star a ⬝ᵥ b` and using `mulVec`/`vecMul` adjunction
(`star_mulVec`, `dotProduct`/`mulVec` associativity), the left pairing
`star(X·a) ⬝ᵥ (X·b) = star a ⬝ᵥ ((Xᴴ·X)·b)`. The structural content is the
defining adjoint property `⟨X·, ·⟩ = ⟨·, Xᴴ·⟩` on `EuclideanSpace`. Reference:
Bhatia, *Matrix Analysis*, IX.2 (the Gram form `Xᴴ X`). -/
lemma inner_toEuclideanLin_self {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (a b : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (toEuclideanLin X a) (toEuclideanLin X b)
      = inner ℂ a (toEuclideanLin (Xᴴ * X) b) := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  -- Goal: `(X *ᵥ b) ⬝ᵥ star (X *ᵥ a) = ((Xᴴ * X) *ᵥ b) ⬝ᵥ star a`.
  -- `star (X *ᵥ a) = star a ᵥ* Xᴴ`, `(Xᴴ*X) *ᵥ b = Xᴴ *ᵥ (X *ᵥ b)`; then `dotProduct`/`mulVec`
  -- adjunction folds both sides to `(X *ᵥ b) ⬝ᵥ (star a ᵥ* Xᴴ)`.
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm (Xᴴ *ᵥ _),
    Matrix.dotProduct_mulVec, dotProduct_comm]

/-- **Existence of a right singular frame** (the SVD existence statement of Bhatia
IX.2). For any square matrix `X` over `ℂ` there is an orthonormal family
`v : Fin N → EuclideanSpace ℂ (Fin N)` that is

* an eigenbasis of `XᴴX` with eigenvalue `sᵢ(X)²`
  (`toEuclideanLin (Xᴴ * X) (v i) = sᵢ(X)² • v i`), ordered so that the descending
  `sortedSingularValues X i = √λᵢ(XᴴX)` line up with `v i` index-for-index, and
* whose images `X vᵢ` are the (unnormalized) left singular vectors:
  `‖toEuclideanLin X (v i)‖ = sᵢ(X)`, pairwise orthogonal whenever the two
  singular values are non-zero (`X vᵢ ⊥ X vⱼ` for `i ≠ j`, `sᵢ, sⱼ ≠ 0`).

The structural content (carried in the conclusion, not assumed) is that `v` is the
descending (`eigenvalues₀`-ordered) orthonormal eigenbasis of the PSD matrix `XᴴX`,
matching `sortedSingularValues`' own `eigenvalues₀` indexing, so the singular
values read off `v` in the same order. Mathlib provides
`IsHermitian.spectral_theorem` / `eigenvectorUnitary` for the PSD matrix
`XᴴX = posSemidef_conjTranspose_mul`, but no packaged SVD, so this existence
statement is authored here. Reference: Bhatia, *Matrix Analysis*, IX.2
(singular value decomposition). -/
lemma exists_rightSingularFrame {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    ∃ v : Fin N → EuclideanSpace ℂ (Fin N), Orthonormal ℂ v ∧
      (∀ i : Fin N, (toEuclideanLin (Xᴴ * X)) (v i)
        = (sortedSingularValues X (i : ℕ) ^ 2 : ℂ) • v i) ∧
      (∀ i j : Fin N, ‖toEuclideanLin X (v i)‖ = sortedSingularValues X (i : ℕ) ∧
        (sortedSingularValues X (i : ℕ) ≠ 0 → sortedSingularValues X (j : ℕ) ≠ 0 → i ≠ j →
          inner ℂ (toEuclideanLin X (v i)) (toEuclideanLin X (v j)) = (0 : ℂ))) := by
  classical
  set hP := posSemidef_conjTranspose_mul X with hP_def
  -- `e : Fin (card (Fin N)) ≃ Fin N` reindexes `eigenvalues₀ ⟨i,_⟩ = eigenvalues (e ⟨i,_⟩)`.
  set e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N))) with he
  have hbnd : ∀ i : Fin N, (i : ℕ) < Fintype.card (Fin N) := fun i => by
    rw [Fintype.card_fin]; exact i.isLt
  -- `v i := eigenvectorBasis (e ⟨i,_⟩)`, the eigenvector for `eigenvalues₀ ⟨i,_⟩ = sᵢ²`.
  set v : Fin N → EuclideanSpace ℂ (Fin N) :=
    fun i => hP.1.eigenvectorBasis (e ⟨(i : ℕ), hbnd i⟩) with hv_def
  -- The eigenvalue at index `i` is `sortedSingularValues X i ^ 2`.
  have hval : ∀ i : Fin N,
      hP.1.eigenvalues (e ⟨(i : ℕ), hbnd i⟩) = sortedSingularValues X (i : ℕ) ^ 2 := by
    intro i
    have hsv : sortedSingularValues X (i : ℕ)
        = Real.sqrt (hP.1.eigenvalues₀ ⟨(i : ℕ), hbnd i⟩) := by
      simp only [sortedSingularValues, dite_eq_left (hbnd i)]
    rw [hsv, Real.sq_sqrt (Matrix.PosSemidef.eigenvalues₀_nonneg hP ⟨(i : ℕ), hbnd i⟩)]
    -- `eigenvalues (e j) = eigenvalues₀ (e.symm (e j)) = eigenvalues₀ j`.
    rw [Matrix.IsHermitian.eigenvalues, ← he, Equiv.symm_apply_apply]
  -- Orthonormality: `v` is the eigenvectorBasis precomposed with the injection `i ↦ e ⟨i,_⟩`.
  have hON : Orthonormal ℂ v := by
    have hinj : Function.Injective (fun i : Fin N => e ⟨(i : ℕ), hbnd i⟩) := fun i₁ i₂ hi =>
      Fin.ext (Fin.mk.inj (e.injective hi))
    exact (hP.1.eigenvectorBasis.orthonormal).comp _ hinj
  -- Eigenvalue equation: `(Xᴴ*X) (v i) = sᵢ² • v i`.
  have heq : ∀ i : Fin N, (toEuclideanLin (Xᴴ * X)) (v i)
      = (sortedSingularValues X (i : ℕ) ^ 2 : ℂ) • v i := by
    intro i
    have hmv := hP.1.mulVec_eigenvectorBasis (e ⟨(i : ℕ), hbnd i⟩)
    rw [hv_def, Matrix.toLpLin_apply,
      show (hP.1.eigenvectorBasis (e ⟨(i : ℕ), hbnd i⟩)).ofLp
        = ⇑(hP.1.eigenvectorBasis (e ⟨(i : ℕ), hbnd i⟩)) from rfl, hmv, hval i,
      ← WithLp.toLp_smul, ← Complex.ofReal_pow, Complex.coe_smul]
  refine ⟨v, hON, heq, fun i j => ⟨?_, fun _ _ hij => ?_⟩⟩
  · -- `‖X vᵢ‖ = sᵢ`: `‖X vᵢ‖² = re⟨vᵢ,(XᴴX) vᵢ⟩ = sᵢ²·‖vᵢ‖² = sᵢ²`, and both sides are `≥ 0`.
    have hnorm2 : ‖(toEuclideanLin X) (v i)‖ ^ 2 = sortedSingularValues X (i : ℕ) ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_toEuclideanLin_self, heq i,
        inner_smul_right, inner_self_eq_one_of_norm_eq_one (hON.norm_eq_one i), mul_one,
        ← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    exact (pow_left_inj₀ (norm_nonneg _) (sortedSingularValues_nonneg X i) two_ne_zero).mp hnorm2
  · -- Orthogonality of images: `⟨X vᵢ,X vⱼ⟩ = sⱼ²·⟨vᵢ,vⱼ⟩ = 0` for `i ≠ j` (ON basis).
    rw [inner_toEuclideanLin_self, heq j, inner_smul_right, hON.inner_eq_zero hij, mul_zero]

/-- **Operator norm of a map diagonal on an orthonormal basis** (the abstract
core of the singular-value / compound-matrix opNorm identity). Let `b` be an
orthonormal basis of a finite-dimensional inner product space `E` indexed by a
nonempty fintype `ι`, and let `T : E →L[ℂ] F` map the basis vectors to a
*pairwise-orthogonal* family `{T (b i)}` with norms `‖T (b i)‖ = d i` for a
non-negative `d : ι → ℝ`. Then the operator norm of `T` is the largest of the
`d i`:
`‖T‖ = ⨆ i, d i`.

Proof (Bessel/Parseval): for any `x`, `T x = Σᵢ ⟨bᵢ,x⟩ • T bᵢ` (linearity +
`OrthonormalBasis.sum_repr`), and the summands are pairwise orthogonal, so by the
Pythagorean identity `‖T x‖² = Σᵢ ‖⟨bᵢ,x⟩‖²·(d i)² ≤ (⨆ d)²·Σᵢ‖⟨bᵢ,x⟩‖²
= (⨆ d)²·‖x‖²` (Parseval), giving `‖T‖ ≤ ⨆ d`; conversely each `‖T bᵢ‖ = d i ≤ ‖T‖`
(unit vector `bᵢ`), so `⨆ d ≤ ‖T‖`. No `≠ 0` hypothesis is needed — a zero `d i`
just contributes a zero image, vacuously orthogonal. Reusable real-analysis /
operator-norm lemma; not in Mathlib (only `sSup_sphere_eq_norm` and Parseval
separately). Reference: Bhatia, *Matrix Analysis*, IX.2 (diagonal map between
orthonormal bases). -/
theorem opNorm_eq_iSup_of_diagonal_onb {ι : Type*} [Fintype ι] [Nonempty ι]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] F) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hnorm : ∀ i, ‖T (b i)‖ = d i)
    (hortho : ∀ i j, i ≠ j → inner ℂ (T (b i)) (T (b j)) = (0 : ℂ)) :
    ‖T‖ = ⨆ i, d i := by
  classical
  have hd_bdd : BddAbove (Set.range d) := Set.Finite.bddAbove (Set.finite_range _)
  -- General Pythagorean sum: `‖Σ wᵢ‖² = Σ ‖wᵢ‖²` for a pairwise-orthogonal family.
  have hsum_sq : ∀ (w : ι → F), (∀ i j, i ≠ j → inner ℂ (w i) (w j) = (0 : ℂ)) →
      ‖∑ i, w i‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
    intro w hw
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum, map_sum, Finset.sum_eq_single i]
    · rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
    · intro j _ hji
      rw [hw i j (Ne.symm hji)]; rfl
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- Expansion of `T x` in the ON basis `b`.
  have hexp : ∀ x : E, T x = ∑ i, (b.repr x i) • T (b i) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_smul T _ _)
  -- The scaled image family `i ↦ (b.repr x i) • T (b i)` is pairwise orthogonal.
  have hpyth : ∀ x : E, ‖T x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 * (d i) ^ 2 := by
    intro x
    rw [hexp x, hsum_sq _ (fun i j hij => by
      rw [inner_smul_left, inner_smul_right, hortho i j hij, mul_zero, mul_zero])]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_smul, mul_pow, hnorm i]
  refine le_antisymm ?_ ?_
  · -- `‖T‖ ≤ ⨆ d`: pointwise `‖T x‖² ≤ (⨆ d)²·‖x‖²` via Parseval.
    have hsup_nn : 0 ≤ ⨆ i, d i := le_ciSup_of_le hd_bdd (Classical.arbitrary ι) (hd _)
    refine T.opNorm_le_bound hsup_nn (fun x => ?_)
    -- `‖T x‖² ≤ (⨆ d)²·‖x‖²`, then take square roots.
    have hbound : ‖T x‖ ^ 2 ≤ (⨆ i, d i) ^ 2 * ‖x‖ ^ 2 := by
      rw [hpyth x]
      have hpars : ∑ i, ‖(b.repr x).ofLp i‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [← b.sum_sq_norm_inner_right x]
        exact Finset.sum_congr rfl (fun i _ => by rw [b.repr_apply_apply])
      rw [← hpars, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [mul_comm ((⨆ j, d j) ^ 2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact pow_le_pow_left₀ (hd i) (le_ciSup_of_le hd_bdd i le_rfl) 2
    have hxnn : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [hbound, norm_nonneg (T x), mul_nonneg hsup_nn hxnn,
      sq_nonneg (‖T x‖ - (⨆ i, d i) * ‖x‖)]
  · -- `⨆ d ≤ ‖T‖`: each `d i = ‖T (b i)‖ ≤ ‖T‖·‖b i‖ = ‖T‖`.
    refine ciSup_le (fun i => ?_)
    rw [← hnorm i]
    calc ‖T (b i)‖ ≤ ‖T‖ * ‖b i‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [b.orthonormal.norm_eq_one i, mul_one]

/-- **Orthonormal wedge singular basis with diagonal images** (the deep
exterior-power core of Bhatia IX.2). For `k ≤ N` and an orthonormal right
singular frame `v` of `X` (orthonormal, with `‖X vᵢ‖ = sᵢ(X)` and the images
pairwise orthogonal for distinct non-zero singular values), there is an
orthonormal basis `wb` of the `k`-th wedge space
`⋀ᵏ(EuclideanSpace ℂ (Fin N))` indexed by the `k`-subsets `{S // S.card = k}`,
such that the `k`-th exterior power `⋀ᵏ X` acts *diagonally* on it:

* `‖⋀ᵏ X (wb S)‖ = ∏_{i∈S} sᵢ(X)` (the image wedge has norm the subset product), and
* `⋀ᵏ X (wb S) ⊥ ⋀ᵏ X (wb T)` for `S ≠ T` (pairwise orthogonal images).

This is the genuine spectral content: `wb S = ⋀_{i∈S} vᵢ` is orthonormal because
`v` is (the Gram determinant of a wedge factors into the Gram of its vectors), and
`⋀ᵏ X (wb S) = ⋀_{i∈S}(X vᵢ)` has wedge-norm `∏ ‖X vᵢ‖ = ∏ sᵢ` and is orthogonal
across distinct `S` because the `X vᵢ` are pairwise orthogonal with norm `sᵢ`
(`hdiag`/`hortho`; a zero `sᵢ` kills the wedge, consistent with the zero product).
Reference: Bhatia, *Matrix
Analysis*, IX.2 (the left singular wedges are orthonormal; `⋀ᵏX` is diagonal
between the wedge singular bases). -/
theorem wedge_basis_image_orthonormal {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (hkN : k ≤ N) (v : Fin N → EuclideanSpace ℂ (Fin N)) (hv : Orthonormal ℂ v)
    (hdiag : ∀ i : Fin N, ‖toEuclideanLin X (v i)‖ = sortedSingularValues X (i : ℕ))
    (hortho : ∀ i j : Fin N, sortedSingularValues X (i : ℕ) ≠ 0 →
      sortedSingularValues X (j : ℕ) ≠ 0 → i ≠ j →
      inner ℂ (toEuclideanLin X (v i)) (toEuclideanLin X (v j)) = (0 : ℂ)) :
    ∃ wb : OrthonormalBasis {S : Finset (Fin N) // S.card = k} ℂ
        (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))),
      (∀ S : {S : Finset (Fin N) // S.card = k},
        ‖(exteriorPower.map k (Matrix.toEuclideanLin X)) (wb S)‖
          = ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i) ∧
      (∀ S T : {S : Finset (Fin N) // S.card = k}, S ≠ T →
        inner ℂ ((exteriorPower.map k (Matrix.toEuclideanLin X)) (wb S))
          ((exteriorPower.map k (Matrix.toEuclideanLin X)) (wb T)) = (0 : ℂ)) := by
  classical
  -- The (pairwise-orthogonal, singular-value-normed) image frame `g i = X vᵢ`.
  let g : Fin N → EuclideanSpace ℂ (Fin N) := fun i => toEuclideanLin X (v i)
  -- A zero singular value forces a zero image vector (its norm is `sᵢ = 0`).
  have hzero : ∀ i : Fin N, sortedSingularValues X (i : ℕ) = 0 → g i = 0 := by
    intro i hi
    have := hdiag i
    rw [hi] at this
    exact norm_eq_zero.mp this
  -- Every Gram entry of the image frame across *distinct* indices vanishes:
  -- a zero singular value kills the vector, otherwise `hortho` applies.
  have hgortho : ∀ i j : Fin N, i ≠ j → inner ℂ (g i) (g j) = (0 : ℂ) := by
    intro i j hij
    by_cases hi : sortedSingularValues X (i : ℕ) = 0
    · rw [hzero i hi, inner_zero_left]
    · by_cases hj : sortedSingularValues X (j : ℕ) = 0
      · rw [hzero j hj, inner_zero_right]
      · exact hortho i j hi hj hij
  -- Diagonal Gram entry: `⟨g i, g i⟩ = (sᵢ² : ℂ)` (its norm is `sᵢ`).
  have hgdiag : ∀ i : Fin N,
      inner ℂ (g i) (g i) = ((sortedSingularValues X (i : ℕ) ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [inner_self_eq_norm_sq_to_K, show g i = toEuclideanLin X (v i) from rfl, hdiag i]
    norm_cast
  -- The orthonormal wedge basis of the right singular frame `v`.
  have hON := wedge_of_orthonormal_is_orthonormal (k := k) v hv
  have : Nonempty {S : Finset (Fin N) // S.card = k} := by
    have hkcard : k ≤ (Finset.univ : Finset (Fin N)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; exact hkN
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq hkcard
    exact ⟨⟨S, hS⟩⟩
  set wbBasis := basisOfOrthonormalOfCardEqFinrank hON
    (card_powersetCard_subtype_eq_finrank_wedge (N := N) (k := k)) with hwbBasis
  have hwbBasisON : Orthonormal ℂ ⇑wbBasis := by
    rw [hwbBasis, coe_basisOfOrthonormalOfCardEqFinrank]; exact hON
  set wb := wbBasis.toOrthonormalBasis hwbBasisON with hwb
  -- `wb S` is the basis wedge `⋀_{i∈S} vᵢ`; its `⋀ᵏX` image is `⋀_{i∈S}(X vᵢ)`.
  have hwbS : ∀ S : {S : Finset (Fin N) // S.card = k},
      wb S = exteriorPower.ιMulti_family ℂ k v (toPowersetCard S) := by
    intro S
    rw [hwb, Module.Basis.coe_toOrthonormalBasis, hwbBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
  have hmapS : ∀ S : {S : Finset (Fin N) // S.card = k},
      (exteriorPower.map k (Matrix.toEuclideanLin X)) (wb S)
        = exteriorPower.ιMulti_family ℂ k g (toPowersetCard S) := by
    intro S
    rw [hwbS S, exteriorPower.map_apply_ιMulti_family]
    rfl
  refine ⟨wb, ?_, ?_⟩
  · -- Norm of the image wedge: `‖⋀_{i∈S}(X vᵢ)‖ = ∏_{i∈S} sᵢ`.
    intro S
    -- `‖·‖² = (⟨·,·⟩).re = (det Gram_SS).re`; the Gram is diagonal with entries `s² `.
    have hnormsq : ‖(exteriorPower.map k (Matrix.toEuclideanLin X)) (wb S)‖ ^ 2
        = ∏ i ∈ (S : Finset (Fin N)), (sortedSingularValues X i) ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hmapS S,
        wedge_inner_eq_gram_det g g S S]
      -- The Gram matrix is diagonal: entry `(a,a) = s²`, off-diagonal `0`.
      have hGdiag : (Matrix.of (fun a b : Fin k =>
          inner ℂ (g (S.1.orderEmbOfFin S.2 a)) (g (S.1.orderEmbOfFin S.2 b))))
            = Matrix.diagonal (fun a : Fin k =>
                ((sortedSingularValues X (S.1.orderEmbOfFin S.2 a) ^ 2 : ℝ) : ℂ)) := by
        ext a b
        simp only [Matrix.of_apply, Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab; rw [ite_eq_left rfl, hgdiag]
        · rw [ite_eq_right hab, hgortho _ _
            (fun h => hab ((S.1.orderEmbOfFin S.2).injective h))]
      rw [hGdiag, Matrix.det_diagonal,
        show ∀ z : ℂ, RCLike.re z = z.re from fun _ => rfl,
        ← Complex.ofReal_prod, Complex.ofReal_re]
      -- Reindex `∏ i ∈ S, s_i² = ∏ a : Fin k, s_{S a}²` through the order embedding.
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ (S : Finset (Fin N)) S.2, Finset.prod_map]
      rfl
    -- Take square roots: both sides are non-negative.
    have hprodnn : 0 ≤ ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i :=
      Finset.prod_nonneg (fun i _ => sortedSingularValues_nonneg X i)
    have hsq : (∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i) ^ 2
        = ∏ i ∈ (S : Finset (Fin N)), (sortedSingularValues X i) ^ 2 := by
      rw [Finset.prod_pow]
    exact (pow_left_inj₀ (norm_nonneg _) hprodnn two_ne_zero).mp (hnormsq.trans hsq.symm)
  · -- Cross-orthogonality: `S ≠ T` ⇒ `⟨⋀(X v)_S, ⋀(X v)_T⟩ = det(cross Gram) = 0`.
    intro S T hST
    rw [hmapS S, hmapS T, wedge_inner_eq_gram_det g g S T]
    -- Some `T`-index lies outside `S` (equal cardinality, `S ≠ T`) ⇒ zero column.
    have hTnotsub : ¬ (T.1 ⊆ S.1) := by
      intro hsub
      exact hST (Subtype.ext ((Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2])).symm))
    obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp hTnotsub
    obtain ⟨b, hb⟩ : ∃ b : Fin k, T.1.orderEmbOfFin T.2 b = x := by
      have hmem : x ∈ Finset.map (T.1.orderEmbOfFin T.2).toEmbedding Finset.univ := by
        rw [Finset.map_orderEmbOfFin_univ T.1 T.2]; exact hxT
      simp only [Finset.mem_map, Finset.mem_univ, true_and] at hmem
      obtain ⟨b, hb⟩ := hmem; exact ⟨b, hb⟩
    apply Matrix.det_eq_zero_of_column_eq_zero b
    intro a
    simp only [Matrix.of_apply]
    rw [hb]
    apply hgortho
    intro hcontra
    exact hxS (hcontra ▸ Finset.orderEmbOfFin_mem S.1 S.2 a)

/-- The `k > N` branch of `exteriorPower_opNorm_eq_max_subset_prod`: here the wedge space is the
zero module, so both `‖⋀ᵏX‖` and the `iSup` over the empty `{S // S.card = k}` are `0`. -/
private lemma exteriorPower_opNorm_eq_max_subset_prod_gt {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (hkN : N < k) :
    ‖LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin X))‖
      = ⨆ (S : {S : Finset (Fin N) // S.card = k}),
          ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i := by
  classical
  -- No `k`-subset of `Fin N` exists: a subset of `Fin N` has at most `N < k` elements.
  have hcard : ∀ S : Finset (Fin N), S.card ≠ k := fun S hS =>
    (card_finset_fin_le S).not_gt (hS ▸ hkN)
  have : IsEmpty {S : Finset (Fin N) // S.card = k} := ⟨fun S => hcard S.1 S.2⟩
  -- The wedge space is `Subsingleton` (its `Module.Basis.exteriorPower` is empty-indexed).
  have : IsEmpty (Set.powersetCard (Fin N) k) :=
    ⟨fun s => hcard s (Set.powersetCard.card_eq s)⟩
  have : Subsingleton (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) :=
    not_nontrivial_iff_subsingleton.mp fun _ =>
      ((euclBasis N).exteriorPower k).index_nonempty.elim isEmptyElim
  -- An operator on a `Subsingleton` space has norm `0`, and so does the empty `iSup`.
  exact (ContinuousLinearMap.opNorm_subsingleton _).trans (Real.iSup_of_isEmpty _).symm

/-- The `k ≤ N` branch of `exteriorPower_opNorm_eq_max_subset_prod`: applies the diagonal-`opNorm`
principle to the wedge orthonormal basis image from `wedge_basis_image_orthonormal`. -/
private lemma exteriorPower_opNorm_eq_max_subset_prod_le {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (v : Fin N → EuclideanSpace ℂ (Fin N)) (hv : Orthonormal ℂ v)
    (hdiag : ∀ i : Fin N, ‖toEuclideanLin X (v i)‖ = sortedSingularValues X (i : ℕ))
    (hortho : ∀ i j : Fin N, sortedSingularValues X (i : ℕ) ≠ 0 →
      sortedSingularValues X (j : ℕ) ≠ 0 → i ≠ j →
      inner ℂ (toEuclideanLin X (v i)) (toEuclideanLin X (v j)) = (0 : ℂ))
    (hkN : k ≤ N) :
    ‖LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin X))‖
      = ⨆ (S : {S : Finset (Fin N) // S.card = k}),
          ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i := by
  classical
  have : Nonempty {S : Finset (Fin N) // S.card = k} := by
    have hkcard : k ≤ (Finset.univ : Finset (Fin N)).card := (Finset.card_fin N).symm ▸ hkN
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq hkcard
    exact ⟨⟨S, hS⟩⟩
  -- `⋀ᵏX` maps the orthonormal wedge basis `wb` to pairwise-orthogonal images of norm
  -- `∏_{i∈S} sᵢ(X)`.
  exact (wedge_basis_image_orthonormal X k hkN v hv hdiag hortho).elim fun wb hwb =>
    opNorm_eq_iSup_of_diagonal_onb wb _
      (fun S => ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i)
      (fun S => Finset.prod_nonneg (fun i _ => sortedSingularValues_nonneg X i)) hwb.1 hwb.2

/-- **Exterior-power operator norm = max subset product** (the diagonal-on-an-ON-basis
core of Bhatia IX.2). Given an orthonormal right singular frame `v` for `X` — i.e.
`v` is orthonormal, its images have the singular-value norms
`‖X vᵢ‖ = sᵢ(X)` (`hdiag`), and those images are pairwise orthogonal for distinct
non-zero singular values (`hortho`) — the operator norm of the `k`-th exterior
power `⋀ᵏ X` equals the supremum over `k`-subsets `S ⊆ Fin N` of the products
`∏_{i∈S} sᵢ(X)`.

The structural content (carried via the hypotheses `hv`, `hdiag`, `hortho`,
supplied by `exists_rightSingularFrame`): `⋀ᵏ` of the ON frame `v` is an ON basis
of the wedge space (`exteriorPower` of an ON basis, made ON by `wedgeEquiv_norm`),
and `⋀ᵏ X` sends each basis wedge `v_S = ⋀_{i∈S} vᵢ` to `(∏_{i∈S} sᵢ(X))` times an
*orthonormal* image wedge `⋀_{i∈S}(X vᵢ)/sᵢ`. So `⋀ᵏ X` is diagonal between two ON
bases with diagonal entries `∏_{i∈S} sᵢ(X)`, hence its operator norm
(`ContinuousLinearMap.sSup_sphere_eq_norm` over the unit sphere of the ON wedge
basis) is the largest diagonal magnitude.

The `k > N` and `k ≤ N` cases are discharged by
`exteriorPower_opNorm_eq_max_subset_prod_gt` / `_le`; splitting them gives each heavy
wedge-`opNorm` `isDefEq` its own budget, so this fits default heartbeats with no override.
Reference: Bhatia, *Matrix Analysis*, IX.2 (`⋀ᵏX` diagonal between the wedge singular bases). -/
lemma exteriorPower_opNorm_eq_max_subset_prod {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (v : Fin N → EuclideanSpace ℂ (Fin N)) (hv : Orthonormal ℂ v)
    (hdiag : ∀ i : Fin N, ‖toEuclideanLin X (v i)‖ = sortedSingularValues X (i : ℕ))
    (hortho : ∀ i j : Fin N, sortedSingularValues X (i : ℕ) ≠ 0 →
      sortedSingularValues X (j : ℕ) ≠ 0 → i ≠ j →
      inner ℂ (toEuclideanLin X (v i)) (toEuclideanLin X (v j)) = (0 : ℂ)) :
    ‖LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin X))‖
      = ⨆ (S : {S : Finset (Fin N) // S.card = k}),
          ∏ i ∈ (S : Finset (Fin N)), sortedSingularValues X i :=
  (Nat.lt_or_ge N k).elim (exteriorPower_opNorm_eq_max_subset_prod_gt X k)
    (exteriorPower_opNorm_eq_max_subset_prod_le X k v hv hdiag hortho)

/-- **Singular-value product = exterior-power operator norm** (the SVD variational
identity of Bhatia IX.2): the leading order-`k` product of singular values of a
square matrix `X` equals the operator norm of the `k`-th exterior power of its
Euclidean linear map:
`∏_{i<k} sᵢ(X) = ‖⋀ᵏ X‖`.

Here `⋀ᵏ X` is `exteriorPower.map k (toEuclideanLin X)`, viewed as a continuous
endomorphism of `⋀ᵏ(EuclideanSpace ℂ (Fin N))` with the canonical inner-product
norm (`Math.SpectralTheory.wedgeNormedAddCommGroup`, making the wedge of an
orthonormal basis orthonormal). Its content is the SVD of `X`: writing
`X = U Σ Vᴴ`, the exterior power acts diagonally on the wedges
`v_{i₁} ∧ ⋯ ∧ v_{iₖ}` of the right singular vectors with eigenvalue
`∏_{j∈S} sⱼ(X)`, so the largest (the operator norm of a normal-on-an-ON-basis
map) is the leading product `∏_{i<k} sᵢ(X)`.

Holds for all `k`: for `k > N` both sides are `0` (the wedge space is the zero
module and `sᵢ(X) = 0` past index `N-1`); for `k = 0` both sides are `1`.

Reference: Bhatia, *Matrix Analysis*, IX.2 (`‖⋀ᵏX‖ = ∏_{i<k} sᵢ(X)`);
Horn-Johnson, *Topics in Matrix Analysis*, 3.3.x. -/
lemma singularValue_prod_eq_exteriorPower_opNorm {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    (∏ i ∈ Finset.range k, sortedSingularValues X i)
      = ‖LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin X))‖ :=
  -- Take the SVD right singular frame `v`, diagonalize `⋀ᵏ X` on its wedge ON basis to read off
  -- the operator norm as the max `k`-subset singular-value product, and collapse that max to
  -- the leading product (`max_subset_prod_eq_leading_prod`).
  (exists_rightSingularFrame X).elim fun v hv =>
    (max_subset_prod_eq_leading_prod X k).symm.trans
      (exteriorPower_opNorm_eq_max_subset_prod X k v hv.1 (fun i => (hv.2.2 i i).1)
        (fun i j => (hv.2.2 i j).2)).symm

/-- Operator-norm submultiplicativity for a power of the continuous `k`-th exterior
power map. -/
private lemma exteriorPower_opNorm_pow_le {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (k m : ℕ)
    (hm : 0 < m) :
    ‖(LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin B))) ^ m‖
      ≤ ‖LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin B))‖ ^ m :=
  norm_pow_le' _ hm

/-- `m = 0` branch of Weyl's product inequality, split off so its wedge-`opNorm`
reconciliation (`‖⋀ᵏ id‖ ≤ 1`) gets its own heartbeat budget. The right product is
`∏ 1 = 1`; the left is `‖⋀ᵏ(toEuclideanLin B⁰)‖ = ‖⋀ᵏ id‖ = ‖id‖ ≤ 1`. -/
private lemma singularValue_prod_pow_le_pow_singularValue_zero {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    (∏ i ∈ Finset.range k, sortedSingularValues (B ^ 0) i)
      ≤ (∏ i ∈ Finset.range k, (sortedSingularValues B i) ^ 0) := by
  simp only [pow_zero, Finset.prod_const_one]
  rw [singularValue_prod_eq_exteriorPower_opNorm (1 : Matrix (Fin N) (Fin N) ℂ) k]
  -- `⋀ᵏ(toEuclideanLin 1) = ⋀ᵏ id` fixes every wedge, so its operator norm is at most `1`.
  have hid : ∀ x, exteriorPower.map k (Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ)) x
      = x := fun x => by
    rw [Matrix.toLpLin_one, exteriorPower.map_id, LinearMap.id_apply]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x =>
    ((congrArg norm (hid x)).trans (one_mul _).symm).le

/-- `m ≥ 1` branch of Weyl's product inequality, split off so its two wedge-`opNorm`
reconciliations get their own heartbeat budget. -/
private lemma singularValue_prod_pow_le_pow_singularValue_pos {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m k : ℕ) (hm : 0 < m) :
    (∏ i ∈ Finset.range k, sortedSingularValues (B ^ m) i)
      ≤ (∏ i ∈ Finset.range k, (sortedSingularValues B i) ^ m) := by
  -- Rewrite the leading singular-value products as exterior-power operator norms, turn
  -- `⋀ᵏ(Bᵐ)` into `(⋀ᵏB)ᵐ`, and apply operator-norm submultiplicativity (`m > 0`, so no
  -- `NormOneClass` on the possibly-trivial wedge space is needed).
  calc ∏ i ∈ Finset.range k, sortedSingularValues (B ^ m) i
      = _ := singularValue_prod_eq_exteriorPower_opNorm (B ^ m) k
    _ = _ := congrArg norm (exteriorPower_toCLM_pow B k m)
    _ ≤ _ := exteriorPower_opNorm_pow_le B k m hm
    _ = (∏ i ∈ Finset.range k, sortedSingularValues B i) ^ m :=
        (congrArg (· ^ m) (singularValue_prod_eq_exteriorPower_opNorm B k)).symm
    _ = ∏ i ∈ Finset.range k, sortedSingularValues B i ^ m := (Finset.prod_pow _ _ _).symm

/-- **Weyl's product inequality** (compound-matrix / `⋀ᵏ` form): the leading
order-`k` singular-value product of `Bᵐ` is dominated by that of `B`'s
`m`-th-power singular values:
`∏_{i<k} sᵢ(Bᵐ) ≤ ∏_{i<k} sᵢ(B)ᵐ`.

This is the rank-`k` compound-matrix (antisymmetric tensor power `⋀ᵏ`) statement
`sₖ(Bᵐ) ≤ sₖ(B)ᵐ` summed over the top `k` indices, equivalently the
log-majorization `λ(BᵐᴴBᵐ) ≺_log λ((BᴴB)ᵐ)`. It is proved here by the SVD
variational argument of Bhatia IX.2: each leading product is the operator norm of a
compound (`⋀ᵏ`) map (`singularValue_prod_eq_exteriorPower_opNorm`), compound
multiplicativity `⋀ᵏ(Bᵐ) = (⋀ᵏB)ᵐ` (`exteriorPower_toCLM_pow`) turns the
`Bᵐ` norm into `‖(⋀ᵏB)ᵐ‖`, and operator-norm submultiplicativity
`‖fᵐ‖ ≤ ‖f‖ᵐ` closes the inequality.

The `m = 0` and `m ≥ 1` cases are discharged by
`singularValue_prod_pow_le_pow_singularValue_zero` / `_pos`; splitting them gives each
heavy wedge-`opNorm` `isDefEq` its own budget, so this fits default heartbeats with no override.

Reference: Bhatia, *Matrix Analysis*, IX.2; Horn-Johnson, *Topics in Matrix
Analysis*, Thm 3.3.2 (compound matrix / Weyl product inequality). -/
lemma singularValue_prod_pow_le_pow_singularValue {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m k : ℕ) :
    (∏ i ∈ Finset.range k, sortedSingularValues (B ^ m) i)
      ≤ (∏ i ∈ Finset.range k, (sortedSingularValues B i) ^ m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact singularValue_prod_pow_le_pow_singularValue_zero B k
  · exact singularValue_prod_pow_le_pow_singularValue_pos B m k hm


end Math.SpectralTheory
