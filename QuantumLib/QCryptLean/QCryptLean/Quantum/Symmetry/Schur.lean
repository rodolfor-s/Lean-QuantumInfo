import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.FiniteGroup

/-! # Schur -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

/-- Native finite-group averaging identity on registers. -/
lemma groupTwirlProjectorPair_trace {G : Type*} [Fintype G] {X Y : Type*} [Fintype X] [Fintype Y]
    (π₁ : G → Op X) (π₂ : G → Op Y) :
    (groupTwirlProjectorPair π₁ π₂).trace =
      ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, (π₁ g).trace * (entryConj (π₂ g)).trace := by
  rw [groupTwirlProjectorPair, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  -- `rw` cannot rewrite under the `Finset.sum` binder; `simp only` can (`Matrix.trace_kronecker`).
  simp only [Matrix.kronecker, Matrix.trace_kronecker]


/-- Native finite-group averaging identity on registers. -/
lemma entryConj_trace {X : Type*} [Fintype X] (A : Op X) :
    (entryConj A).trace = star A.trace := by
  simp only [entryConj, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, star_sum]


/-- Native finite-group averaging identity on registers. -/
theorem schurOrthogonal_entry {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X]
    (π : G → Op X) (hπ : IsUnitaryRep π) (hirr : IsIrreducibleRep π) (j i k l : X) :
    ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, π g k j * star (π g l i)
      = (if j = i then (1 / (Fintype.card X : ℂ)) else 0) * (if k = l then (1 : ℂ) else 0) := by
  have hc0 : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hd0 : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := X)
  -- The twirled matrix unit `E_{ji}` and its group average `S`
  set E : Op X := Matrix.single j i (1 : ℂ) with hE
  set S : Op X := ∑ g : G, π g * E * (π g)ᴴ with hS
  -- Invariance `π h · S · (π h)ᴴ = S`: each summand is conjugated into the summand at `h · g`
  have hterm : ∀ h g : G, π h * (π g * E * (π g)ᴴ) * (π h)ᴴ
      = π (h * g) * E * (π (h * g))ᴴ := by
    intro h g
    -- Unfold `π (h · g)`, use that `ᴴ` reverses products, then reassociate
    rw [hπ.1 h g, Matrix.conjTranspose_mul]
    simp only [← mul_assoc]
  have hinv : ∀ h : G, π h * S * (π h)ᴴ = S := by
    intro h
    rw [hS, Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hterm h g]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun y => π y * E * (π y)ᴴ)
  -- Hence `S` commutes with every `π h` (multiply the invariance by `π h` on the right)
  have hcomm : ∀ h : G, π h * S = S * π h := by
    intro h
    have h1 : (π h * S * (π h)ᴴ) * π h = S * π h := by rw [hinv h]
    rw [mul_assoc, hπ.2 h, mul_one] at h1
    exact h1
  -- Schur: `S` is a scalar operator
  obtain ⟨c, hc⟩ := hirr S hcomm
  -- The scalar is `δ_{ji} · |G| / d`: trace `S` two ways
  have htrE : E.trace = (if j = i then (1 : ℂ) else 0) := by
    simp only [hE, Matrix.trace, Matrix.diag_apply, Matrix.single_apply]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right hij]
      exact Finset.sum_eq_zero fun a _ => by
        have hna : ¬ (j = a ∧ i = a) := fun h => hij (h.1.trans h.2.symm)
        simp [hna]
  have htrS : S.trace = (if j = i then ((Fintype.card G : ℕ) : ℂ) else 0) := by
    rw [hS, Matrix.trace_sum]
    -- Each summand has trace `Tr E` (cyclic trace + unitarity)
    have h1 : ∀ g : G, (π g * E * (π g)ᴴ).trace = E.trace := fun g =>
      by rw [Matrix.trace_mul_cycle, hπ.2 g, one_mul]
    by_cases hij : j = i
    · rw [ite_eq_left hij, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => h1 g, htrE,
        ite_eq_left hij, Finset.sum_const, Finset.card_univ, nsmul_eq_mul', one_mul]
    · rw [ite_eq_right hij, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => h1 g, htrE,
        ite_eq_right hij]
      exact Finset.sum_const_zero
  have hcval : c * (Fintype.card X : ℂ) = (if j = i then ((Fintype.card G : ℕ) : ℂ) else 0) := by
    rw [← htrS, hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  -- So `c / |G| = δ_{ji} / d`
  have hscale : ((Fintype.card G : ℕ) : ℂ)⁻¹ * c =
      if j = i then (1 / (Fintype.card X : ℂ)) else 0 := by
    by_cases hij : j = i
    · rw [ite_eq_left hij]
      -- hcval : c · d = |G|; goal: |G|⁻¹ · c = 1/d
      have hc2 : c = ((Fintype.card G : ℕ) : ℂ) / (Fintype.card X : ℂ) := by
        rw [eq_div_iff hd0]
        rw [ite_eq_left hij] at hcval
        exact hcval
      rw [hc2, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, one_div]
    · have hc0' : c = 0 := by
        rw [ite_eq_right hij] at hcval
        exact (mul_eq_zero.1 hcval).resolve_right hd0
      rw [ite_eq_right hij, hc0', mul_zero]
  -- Read off the `(k, l)` entry of `S = c • 1`
  have hentry : ∀ g : G, (π g * E * (π g)ᴴ) k l = π g k j * star (π g l i) := by
    intro g
    rw [hE, Matrix.mul_apply]
    -- Only the `x = i` summand survives: `(π g · E_{ji}) k x = 0` unless `x = i`
    rw [Finset.sum_eq_single i]
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply, mul_one]
    · intro x _ hx
      simp [hx]
    · intro hc
      exact (hc (Finset.mem_univ i)).elim
  have hsum : S k l = ∑ g : G, π g k j * star (π g l i) := by
    rw [hS, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun g _ => hentry g
  by_cases hkl : k = l
  · rw [← hsum, hc, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_eq_left hkl,
      mul_one, mul_one, hscale]
  · rw [← hsum, hc, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_eq_right hkl,
      mul_zero, mul_zero, mul_zero]


/-- Native finite-group averaging identity on registers. -/
theorem groupTwirlProjectorPair_trace_self_irreducible {G : Type*} [Group G] [Fintype G]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (π : G → Op X) (hπ : IsUnitaryRep π) (hirr : IsIrreducibleRep π) :
    (groupTwirlProjectorPair π π).trace = 1 := by
  have hd0 : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := X)
  -- Trace of a matrix as the sum of its diagonal entries
  have hexp : ∀ A : Op X, A.trace = ∑ i, A i i := fun A => by
    simp only [Matrix.trace, Matrix.diag_apply]
  -- Each summand trace is the double sum of the products of diagonal entries
  have hterm : ∀ g : G, (π g).trace * (entryConj (π g)).trace
      = ∑ j : X, ∑ l : X, π g j j * star (π g l l) := by
    intro g
    rw [hexp, entryConj_trace, hexp, star_sum]
    simp only [Finset.sum_mul_sum]
  -- Entry-wise Schur orthogonality on the diagonal, specialised to `(j, i, k, l) = (j, l, j, l)`
  have key : ∀ j l : X, ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G,
      π g j j * star (π g l l) = if j = l then (1 / (Fintype.card X : ℂ)) else 0 := by
    intro j l
    rw [schurOrthogonal_entry π hπ hirr j l j l]
    by_cases hjeql : j = l
    · rw [ite_eq_left hjeql, ite_eq_left hjeql, mul_one]
    · rw [ite_eq_right hjeql, ite_eq_right hjeql, mul_zero]
  -- Move the group sum inward (below the two index sums)
  have hreorder : ∑ g : G, ∑ j : X, ∑ l : X, π g j j * star (π g l l)
      = ∑ j : X, ∑ l : X, ∑ g : G, π g j j * star (π g l l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _j _ => Finset.sum_comm
  -- Push the prefactor `1/|G|` next to the group sum
  have hpush : ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ j : X, ∑ l : X, ∑ g : G,
      π g j j * star (π g l l)
      = ∑ j : X, ∑ l : X, ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G,
        π g j j * star (π g l l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _j _ => by rw [Finset.mul_sum]
  -- Each index `j` contributes `1/d` exactly once (at `l = j`), so the total is `d · 1/d = 1`
  have hinner : ∀ j : X, ∑ l : X, (if j = l then (1 / (Fintype.card X : ℂ)) else 0) =
      1 / (Fintype.card X : ℂ) := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl]
    · intro l _ hl
      rw [ite_eq_right (Ne.symm hl)]
    · intro hc
      exact absurd (Finset.mem_univ j) hc
  have hsum2 : ∑ j : X, ∑ l : X, (if j = l then (1 / (Fintype.card X : ℂ)) else 0) = 1 := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hinner j,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul',
      one_div, inv_mul_cancel₀ hd0]
  rw [groupTwirlProjectorPair_trace π π]
  simp only [hterm, hreorder, hpush, key, hsum2]


end Quantum.Symmetry
