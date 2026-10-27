import Mathlib.LinearAlgebra.Projection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Symmetry.Basic

/-! # Commutant -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X : Type*} [Fintype X]

/-- Matrices commuting with every element of a set form a complex subspace. -/
def commutant (S : Set (Op X)) : Submodule ℂ (Op X) where
  carrier := {M | ∀ A ∈ S, A * M = M * A}
  add_mem' := by intro A B hA hB C hC; rw [mul_add, add_mul, hA C hC, hB C hC]
  zero_mem' := by intro A _; rw [mul_zero, zero_mul]
  smul_mem' := by intro c A hA B hB; rw [Matrix.mul_smul, Matrix.smul_mul, hA B hB]

/-- Passing to a linear span does not change the commutant. -/
theorem commutant_span (S : Set (Op X)) :
    commutant S = commutant (Submodule.span ℂ S : Set (Op X)) := by
  apply le_antisymm
  · intro M hM A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact hM A hA
    | zero => rw [zero_mul, mul_zero]
    | add A B _ _ hA hB => rw [add_mul, mul_add, hA, hB]
    | smul c A _ hA => rw [Matrix.smul_mul, Matrix.mul_smul, hA]
  · intro M hM A hA
    exact hM A (Submodule.subset_span hA)

omit [Fintype X] in
/-- The span of the site-permutation matrices, allowing linear dependence. -/
def permSpan [DecidableEq X] (k : ℕ) : Submodule ℂ (Op (Fin k → X)) :=
  Submodule.span ℂ (Set.range fun σ : Equiv.Perm (Fin k) => permutationRepresentation σ)

/-- The commutant of a unitary family. -/
def repCommutant [DecidableEq X] {G : Type*} (U : G → UnitaryOp X) :
    Submodule ℂ (Op X) := commutant (Set.range fun g => (U g).val)

/-- The representation commutant dimension that controls symmetry-reduced exponents. -/
def repCommutantFinrank [DecidableEq X] {G : Type*} (U : G → UnitaryOp X) : ℕ :=
  Module.finrank ℂ (repCommutant U)
/-- A Schur decomposition of the commutant into full matrix blocks with actual register types. -/
def IsSchurBlockDiagonalCommutant [DecidableEq X] {G I : Type*}
    (U : G → UnitaryOp X) (M : I → Type*) : Prop :=
  Nonempty (repCommutant U ≃ₗ[ℂ] ((i : I) → Matrix (M i) (M i) ℂ))

/-- A Schur block presentation computes the symmetry-reduced commutant dimension. -/
theorem repCommutant_finrank_eq_sum_card_sq [DecidableEq X] {G I : Type*} [Fintype I]
    (U : G → UnitaryOp X) (M : I → Type*) [∀ i, Fintype (M i)]
    (hU : IsSchurBlockDiagonalCommutant U M) :
    repCommutantFinrank U = ∑ i, (Fintype.card (M i)) ^ 2 := by
  obtain ⟨e⟩ := hU
  unfold repCommutantFinrank
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype ℂ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix, Module.finrank_self]
  ring


open scoped Kronecker

/-- Finite-group bicommutant equality, by an averaged projection on the vectorized orbit span. -/
theorem finiteGroup_bicommutant [DecidableEq X] {G : Type*} [Group G] [Finite G]
    (ρ : G →* Op X) :
    commutant (commutant (Set.range ρ) : Set (Op X)) = Submodule.span ℂ (Set.range ρ) := by
  classical
  let := Fintype.ofFinite G
  let v : Op X →ₗ[ℂ] (X × X → ℂ) :=
    { toFun := fun A p => A p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let r : G →* Op (X × X) :=
    { toFun := fun g => ρ g ⊗ₖ (1 : Op X)
      map_one' := by rw [map_one, one_kronecker_one]
      map_mul' := by intro g h; rw [map_mul, ← mul_kronecker_mul, Matrix.one_mul] }
  let W := Submodule.map v (Submodule.span ℂ (Set.range ρ))
  let P := LinearMap.toMatrix' (Submodule.projection W _ W.exists_isCompl.choose_spec)
  let Q := (Fintype.card G : ℂ)⁻¹ • ∑ g, r g * P * r g⁻¹
  have hv (A B : Op X) : (A ⊗ₖ (1 : Op X)) *ᵥ v B = v (A * B) := by
    ext ⟨i, j⟩
    change ((A ⊗ₖ (1 : Op X)) *ᵥ (fun p => B p.1 p.2)) (i, j) = (A * B) i j
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
      kroneckerMap_apply, Matrix.one_apply]
  have hPm (x : X × X → ℂ) : P *ᵥ x ∈ W := by
    rw [LinearMap.toMatrix'_mulVec]
    exact Submodule.projection_apply_mem W.exists_isCompl.choose_spec x
  have hPf (x : X × X → ℂ) (hx : x ∈ W) : P *ᵥ x = x := by
    rw [LinearMap.toMatrix'_mulVec]
    exact (Submodule.projection_eq_self_iff W.exists_isCompl.choose_spec x).mpr hx
  have hinv (g : G) (x : X × X → ℂ) (hx : x ∈ W) : r g *ᵥ x ∈ W := by
    obtain ⟨A, hA, rfl⟩ := hx
    change (ρ g ⊗ₖ (1 : Op X)) *ᵥ v A ∈ W
    rw [hv]
    refine ⟨ρ g * A, ?_, rfl⟩
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨h, rfl⟩ := hA
      exact Submodule.subset_span ⟨g * h, map_mul ρ g h⟩
    | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.mul_add]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hA
  have hQm (x : X × X → ℂ) : Q *ᵥ x ∈ W := by
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hinv g _ (hPm _)
  have hQf (x : X × X → ℂ) (hx : x ∈ W) : Q *ᵥ x = x := by
    have ht (g : G) : (r g * P * r g⁻¹) *ᵥ x = x := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPf _ (hinv g⁻¹ x hx),
        Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp only [ht, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ (show (Fintype.card G : ℂ) ≠ 0 from
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]
  have hQc (g : G) : Commute (r g) Q := by
    change r g * Q = Q * r g
    dsimp only [Q]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Finset.sum_mul]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
    change r g * (r h * P * r h⁻¹) = r (g * h) * P * r (g * h)⁻¹ * r g
    rw [_root_.mul_inv_rev, map_mul, map_mul]
    simp only [Matrix.mul_assoc, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rw [map_mul, Matrix.mul_assoc]
  have hL (A : Op X) (i k j l : X) :
      ((A ⊗ₖ (1 : Op X)) * Q) (i, k) (j, l) =
        (A * (show Op X from fun a b => Q (a, k) (b, l))) i j := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply]
    rfl
  have hR (A : Op X) (i k j l : X) :
      (Q * (A ⊗ₖ (1 : Op X))) (i, k) (j, l) =
        ((show Op X from fun a b => Q (a, k) (b, l)) * A) i j := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply]
    rfl
  apply le_antisymm
  · intro T hT
    have hb (k l : X) : (show Op X from fun a b => Q (a, k) (b, l)) ∈ commutant (Set.range ρ) := by
      rintro A ⟨g, rfl⟩
      ext i j
      have hc := congrFun (congrFun (hQc g).eq (i, k)) (j, l)
      change ((ρ g ⊗ₖ (1 : Op X)) * Q) (i, k) (j, l) =
        (Q * (ρ g ⊗ₖ (1 : Op X))) (i, k) (j, l) at hc
      simpa only [hL, hR] using hc
    have hc : (T ⊗ₖ (1 : Op X)) * Q = Q * (T ⊗ₖ (1 : Op X)) := by
      ext ⟨i, k⟩ ⟨j, l⟩
      rw [hL, hR, hT _ (hb k l)]
    have h1 : v (1 : Op X) ∈ W :=
      ⟨1, Submodule.subset_span ⟨1, map_one ρ⟩, rfl⟩
    have hf : Q *ᵥ v T = v T := by
      calc
        _ = Q *ᵥ ((T ⊗ₖ (1 : Op X)) *ᵥ v (1 : Op X)) := by rw [hv, Matrix.mul_one]
        _ = (T ⊗ₖ (1 : Op X)) *ᵥ (Q *ᵥ v (1 : Op X)) := by
          rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec]
        _ = v T := by rw [hQf _ h1, hv, Matrix.mul_one]
    obtain ⟨A, hA, he⟩ := hf ▸ hQm (v T)
    have he' : A = T := by ext i j; exact congrFun he (i, j)
    exact he' ▸ hA
  · rw [Submodule.span_le]
    rintro A ⟨g, rfl⟩ M hM
    exact (hM _ ⟨g, rfl⟩).symm

end Quantum.Symmetry
