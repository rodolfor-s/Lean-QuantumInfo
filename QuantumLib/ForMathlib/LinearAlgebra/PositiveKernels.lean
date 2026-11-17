import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Kernel ↔ Matrix identity for real symmetric PSD kernels

Small linear-algebra helpers consumed by `SeedAvgVarianceCore.lean`.

A "kernel" is a function `K : X → X → ℝ`. We identity to `Matrix X X ℝ` via
`Matrix.of`, and translate between the bilinear form `∑ x x', K x x' · v x · v x'`
and the matrix expression `v ⬝ᵥ (Matrix.of K).mulVec v`.

## Main statements
- `kernel_bilinear_eq_dotProduct_mulVec`: kernel bilinear form equals the
  matrix dot-product / mulVec expression.
- `kernel_diag_sum_eq_trace`: diagonal sum equals matrix trace.
- `kernel_inner_eq_trace_of_sym`: entrywise sum `∑ K x x' · L x x'` equals
  `Tr((Matrix.of K) * (Matrix.of L))` for symmetric `L`.
- `posSemidef_of_kernel_sym_posSemidef`: a symmetric kernel that is PSD as a
  bilinear form yields a PSD matrix `Matrix.of K`.
- `trace_mul_nonneg_of_posSemidef`: PSD-PSD trace product is non-negative.
- `sum_kernels_posSemidef_nonneg`: for two real symmetric PSD kernels,
  `∑ x x' K x x' · L x x' ≥ 0`.
- `kernel_bilinear_swap`, `kernel_sym_bilinear`,
  `kernel_sym_inner_of_sym_left`: symmetrization-invariance helpers for
  bilinear and entrywise pairings.
-/

open Matrix
open scoped MatrixOrder

namespace Math.LinearAlgebra

/-- Bilinear form `∑ x x', K x x' · v x · v x'` equals `v ⬝ᵥ (Matrix.of K).mulVec v`. -/
lemma kernel_bilinear_eq_dotProduct_mulVec
    {X : Type*} [Fintype X] (K : X → X → ℝ) (v : X → ℝ) :
    (∑ x : X, ∑ x' : X, K x x' * v x * v x') =
      v ⬝ᵥ (Matrix.of K).mulVec v := by
  unfold dotProduct mulVec
  simp only [Matrix.of_apply, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- Diagonal sum equals the trace of `Matrix.of K`. -/
lemma kernel_diag_sum_eq_trace
    {X : Type*} [Fintype X] (K : X → X → ℝ) :
    (∑ x : X, K x x) = (Matrix.of K).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.of_apply]

/-- For symmetric `L`, the entrywise sum `∑ x x', K x x' · L x x'` equals
`Tr((Matrix.of K) * (Matrix.of L))`. -/
lemma kernel_inner_eq_trace_of_sym
    {X : Type*} [Fintype X] (K L : X → X → ℝ)
    (hL_sym : ∀ x x', L x x' = L x' x) :
    (∑ x : X, ∑ x' : X, K x x' * L x x') =
      ((Matrix.of K) * (Matrix.of L)).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [hL_sym x' x]

/-- For symmetric real PSD kernel `K` (PSD as bilinear form), the matrix
`Matrix.of K` is positive semidefinite. -/
lemma posSemidef_of_kernel_sym_posSemidef
    {X : Type*} [Fintype X] (K : X → X → ℝ)
    (hK_sym : ∀ x x', K x x' = K x' x)
    (hK_psd : ∀ v : X → ℝ, 0 ≤ ∑ x : X, ∑ x' : X, K x x' * v x * v x') :
    (Matrix.of K).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: for ℝ, IsHermitian ↔ Mᵀ = M.
    rw [Matrix.IsHermitian]
    ext x x'
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact hK_sym x' x
  · intro v
    -- For real v, star v = v.
    have hstar : (star v : X → ℝ) = v := by
      funext x; simp [star_trivial]
    rw [hstar, ← kernel_bilinear_eq_dotProduct_mulVec]
    exact hK_psd v

/-- Trace inequality: for two real PSD matrices `M, N` over `ℝ` with `Fintype X`,
`Tr(M N) ≥ 0`. The proof uses the PSD square-root and cyclic invariance of the trace. -/
lemma trace_mul_nonneg_of_posSemidef
    {X : Type*} [Fintype X]
    (M N : Matrix X X ℝ) (hM : M.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ (M * N).trace := by
  classical
  -- Tr(M N) = Tr(sqrt N * M * sqrt N) using cyclic + sqrt squared.
  have hsqrtN : (CFC.sqrt N).PosSemidef := (CFC.sqrt_nonneg N).posSemidef
  have hsqrtN_sq : CFC.sqrt N * CFC.sqrt N = N :=
    CFC.sqrt_mul_sqrt_self N (ha := hN.nonneg)
  have hsqrtN_herm : (CFC.sqrt N).IsHermitian := hsqrtN.isHermitian
  -- (sqrtN)† * M * sqrtN is PSD (M is PSD).
  have hConjPSD : ((CFC.sqrt N).conjTranspose * M * CFC.sqrt N).PosSemidef :=
    hM.conjTranspose_mul_mul_same (CFC.sqrt N)
  -- And conjTranspose = id for Hermitian.
  have hConj_eq : (CFC.sqrt N).conjTranspose = CFC.sqrt N := hsqrtN_herm
  rw [hConj_eq] at hConjPSD
  -- Now `(sqrt N * M * sqrt N).PosSemidef`, hence its trace is non-negative.
  have htr_nonneg : 0 ≤ (CFC.sqrt N * M * CFC.sqrt N).trace :=
    hConjPSD.trace_nonneg
  -- And `(M * N).trace = (sqrt N * M * sqrt N).trace` by `trace_mul_cycle`
  -- after rewriting `N = sqrt N * sqrt N`.
  have heq : (M * N).trace = (CFC.sqrt N * M * CFC.sqrt N).trace := by
    conv_lhs => rw [← hsqrtN_sq]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [heq]
  exact htr_nonneg

/-- **Sum-of-products of PSD kernels is non-negative.**

For two real symmetric PSD kernels `K` and `L`, `∑ x x', K x x' · L x x' ≥ 0`. -/
lemma sum_kernels_posSemidef_nonneg
    {X : Type*} [Fintype X] (K L : X → X → ℝ)
    (hK_sym : ∀ x x', K x x' = K x' x)
    (hL_sym : ∀ x x', L x x' = L x' x)
    (hK_psd : ∀ v : X → ℝ, 0 ≤ ∑ x : X, ∑ x' : X, K x x' * v x * v x')
    (hL_psd : ∀ v : X → ℝ, 0 ≤ ∑ x : X, ∑ x' : X, L x x' * v x * v x') :
    0 ≤ ∑ x : X, ∑ x' : X, K x x' * L x x' := by
  rw [kernel_inner_eq_trace_of_sym K L hL_sym]
  have hKmat : (Matrix.of K).PosSemidef := posSemidef_of_kernel_sym_posSemidef K hK_sym hK_psd
  have hLmat : (Matrix.of L).PosSemidef := posSemidef_of_kernel_sym_posSemidef L hL_sym hL_psd
  exact trace_mul_nonneg_of_posSemidef _ _ hKmat hLmat

/-- **Bilinear form is invariant under transposing the kernel.** Direct
consequence of swapping the order of summation and renaming the dummy
variables. -/
lemma kernel_bilinear_swap
    {X : Type*} [Fintype X] (f : X → X → ℝ) (c : X → ℝ) :
    (∑ x : X, ∑ x' : X, f x' x * c x * c x') =
      (∑ x : X, ∑ x' : X, f x x' * c x * c x') := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Bilinear form of the symmetrization equals the bilinear form of the
original kernel. -/
lemma kernel_sym_bilinear
    {X : Type*} [Fintype X] (G : X → X → ℝ) (c : X → ℝ) :
    (∑ x : X, ∑ x' : X, ((G x x' + G x' x) / 2) * c x * c x') =
      ∑ x : X, ∑ x' : X, G x x' * c x * c x' := by
  have hsplit :
      (∑ x : X, ∑ x' : X, ((G x x' + G x' x) / 2) * c x * c x') =
        ((∑ x : X, ∑ x' : X, G x x' * c x * c x') +
          (∑ x : X, ∑ x' : X, G x' x * c x * c x')) / 2 := by
    rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  rw [hsplit, kernel_bilinear_swap]
  ring

/-- Replacing `G` by its symmetrization in the entrywise sum
`∑ A x x' * G x x'` does not change the value, provided `A` is symmetric. -/
lemma kernel_sym_inner_of_sym_left
    {X : Type*} [Fintype X] (A G : X → X → ℝ)
    (hA_sym : ∀ x x', A x x' = A x' x) :
    (∑ x : X, ∑ x' : X, A x x' * ((G x x' + G x' x) / 2)) =
      ∑ x : X, ∑ x' : X, A x x' * G x x' := by
  have hsplit :
      (∑ x : X, ∑ x' : X, A x x' * ((G x x' + G x' x) / 2)) =
        ((∑ x : X, ∑ x' : X, A x x' * G x x') +
          (∑ x : X, ∑ x' : X, A x x' * G x' x)) / 2 := by
    rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  -- Symmetry of `A` lets us identify `∑ A x x' * G x' x` with `∑ A x x' * G x x'`.
  have hcomm :
      (∑ x : X, ∑ x' : X, A x x' * G x' x) =
        (∑ x : X, ∑ x' : X, A x x' * G x x') := by
    have hrewrite :
        (∑ x : X, ∑ x' : X, A x x' * G x' x) =
          (∑ x : X, ∑ x' : X, A x' x * G x' x) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
      rw [hA_sym x x']
    rw [hrewrite, Finset.sum_comm]
  rw [hsplit, hcomm]; ring

end Math.LinearAlgebra
