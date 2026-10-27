import Mathlib.LinearAlgebra.Lagrange
import QCryptLean.Math.SpectralTheory.MatrixCFC
import QCryptLean.Math.SpectralTheory.Matrix

/-! # Functional calculus of Hermitian block-diagonal matrices -/

noncomputable section
namespace Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Polynomial evaluation acts separately on diagonal blocks. -/
private lemma aeval_blockDiagonal {X Q : Type*} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q]
    (M : X → Matrix Q Q ℂ) (q : Polynomial ℝ) :
    (Polynomial.aeval (Matrix.blockDiagonal M)) q
      = Matrix.blockDiagonal (fun x => (Polynomial.aeval (M x)) q) := by
  classical
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hp, hr, ← Matrix.blockDiagonal_add]
      exact congrArg _ (funext fun x => (map_add (Polynomial.aeval (M x)) p r).symm)
  | monomial k c =>
      have hR : (fun x => (Polynomial.aeval (M x)) (Polynomial.monomial k c))
          = fun x => (c : ℝ) • (M x) ^ k := by
        funext x
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [hR, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, ← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_smul]
      rfl

/-- Real continuous functional calculus acts separately on Hermitian diagonal blocks. -/
theorem cfc_blockDiagonal {X Q : Type*} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q]
    (M : X → Matrix Q Q ℂ) (hM : ∀ x, IsSelfAdjoint (M x)) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal M) = Matrix.blockDiagonal (fun x => cfc f (M x)) := by
  classical
  have hBD : IsSelfAdjoint (Matrix.blockDiagonal M) := by
    change (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
    rw [Matrix.blockDiagonal_conjTranspose]
    exact congrArg _ (funext fun x => hM x)
  set s : Finset ℝ :=
    (Matrix.finite_real_spectrum (A := Matrix.blockDiagonal M)).toFinset ∪
      Finset.univ.biUnion (fun x : X => (Matrix.finite_real_spectrum (A := M x)).toFinset)
    with hs
  set q : Polynomial ℝ := Lagrange.interpolate s id f with hq
  have hval : ∀ μ ∈ s, Polynomial.eval μ q = f μ := by
    intro μ hμ
    exact Lagrange.eval_interpolate_at_node (s := s) (v := (id : ℝ → ℝ)) f (Set.injOn_id _) hμ
  have hmain : cfc f (Matrix.blockDiagonal M)
      = (Polynomial.aeval (Matrix.blockDiagonal M)) q := by
    rw [← cfc_polynomial (R := ℝ) q (Matrix.blockDiagonal M)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hμ)
  have hblk : ∀ x, cfc f (M x) = (Polynomial.aeval (M x)) q := by
    intro x
    rw [← cfc_polynomial (R := ℝ) q (M x)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x,
        by rw [Set.Finite.mem_toFinset]; exact hμ⟩)
  rw [hmain, aeval_blockDiagonal]
  exact congrArg _ (funext fun x => (hblk x).symm)

end Matrix
