import Mathlib.Data.Nat.Choose.Bounds
import QCryptLean.Math.Combinatorics.PermutationAction

/-!
# De Finetti postselection prefactor `g_{n,x}` (G1)

The de Finetti reductions of Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024
(arXiv:2403.11851, "Postselection technique for optical Quantum Key Distribution
with improved de Finetti reductions") are all quoted with the *exact* penalty

  `g_{n,x} = dim (Sym^n (ℂ^x)) = C(n + x - 1, x - 1)`   (Table I, `\cost` row, main.tex:219;
  the `\cost`-domination bound and `g_{n,x} = \dimSym{x} = \binom{n+x-1}{n}` gloss,
  main.tex:231–234).

This file introduces `Math.Combinatorics.deFinettiPrefactor` as that exact binomial
coefficient, together with the identifications with the cardinality of the symmetric
power `Sym (Fin x) n` (hence with `dim Sym^n(ℂ^x)`) that make the "exact dimension"
reconciliation explicit.

This is a general de-Finetti/symmetric-subspace primitive (no QKD-protocol content).

The generic CKR reduction proved elsewhere in the library only delivers the *bound*
`(n + 1)^{x - 1} ≥ g_{n,x}`. The corollaries 3.1/3.2/3.3/4.1 all state the
exact `g_{n,x}`, so the shared layer records the exact value here rather than the
looser power.

## Main definitions
- `Math.Combinatorics.deFinettiPrefactor x n` : the exact symmetric-subspace dimension
  `C(n + x - 1, x - 1)`, Nahar et al. 2024's `g_{n,x}`.

## Main statements
- `Math.Combinatorics.deFinettiPrefactor_eq_card_sym` :
  `deFinettiPrefactor x n = Fintype.card (Sym (Fin x) n)`.
- `Math.Combinatorics.deFinettiPrefactor_eq_card_occupation` :
  `deFinettiPrefactor x n = Nat.card {f : Fin x → ℕ // ∑ i, f i = n}`
  (the number of occupation vectors = `dim Sym^n(ℂ^x)`).
- `Math.Combinatorics.deFinettiPrefactor_pos` :
  `0 < deFinettiPrefactor x n` for every natural `x`.
- `Math.Combinatorics.deFinettiPrefactor_le_pow` :
  `deFinettiPrefactor x n ≤ (n + 1) ^ (x - 1)` (the CKR bound dominates the exact value).
-/

open Math.RepresentationTheory

namespace Math.Combinatorics

/-- **De Finetti postselection prefactor** `g_{n,x} = dim (Sym^n (ℂ^x)) = C(n + x - 1, x - 1)`.

    This is the *exact* symmetric-subspace dimension appearing in Nahar et al. 2024
    (arXiv:2403.11851, Table I `\cost` row at main.tex:219, the `\cost`-domination bound / the
    `g_{n,x}` gloss at
    main.tex:231–234), not the looser CKR bound
    `(n + 1)^{x - 1}`. In the Nahar et al. corollaries the overall security bound carries a
    prefactor `g_{n,x}` (or `2 g_{n,x}`) rather than the power `(n+1)^{x-1}`,
    making the exact value load-bearing. -/
def deFinettiPrefactor (x n : ℕ) : ℕ := Nat.choose (n + x - 1) (x - 1)

/-- `g_{n,x}` is the cardinality of the symmetric power `Sym (Fin x) n`, i.e. the
    number of degree-`n` monomials in `x` variables, i.e. `dim Sym^n(ℂ^x)`. -/
theorem deFinettiPrefactor_eq_card_sym (x n : ℕ) [NeZero x] :
    deFinettiPrefactor x n = Fintype.card (Sym (Fin x) n) := by
  rw [deFinettiPrefactor, card_sym_fin_eq_choose]

/-- `g_{n,x}` counts the occupation vectors `(n₁, …, n_x)` with `∑ᵢ nᵢ = n`.
    This is `dim Sym^n(ℂ^x)` via `symmetricSubspace_dimension`. -/
theorem deFinettiPrefactor_eq_card_occupation (x n : ℕ) [NeZero x] :
    deFinettiPrefactor x n = Nat.card {f : Fin x → ℕ // ∑ i, f i = n} := by
  rw [deFinettiPrefactor]
  exact symmetricSubspace_dimension x n

/-- The prefactor is positive, including at `x = 0` with truncated natural subtraction. -/
theorem deFinettiPrefactor_pos (x n : ℕ) : 0 < deFinettiPrefactor x n := by
  unfold deFinettiPrefactor
  exact Nat.choose_pos (by omega)

/-- A one-dimensional single-copy space has unit postselection prefactor. -/
@[simp] theorem deFinettiPrefactor_one (n : ℕ) : deFinettiPrefactor 1 n = 1 := by
  simp [deFinettiPrefactor]

/-- The CKR power bound dominates the exact de Finetti prefactor:
    `g_{n,x} = C(n + x - 1, x - 1) ≤ (n + 1)^{x - 1}`.

    This makes explicit that the exact `g_{n,x}` recorded here is never larger
    than the generic CKR reduction's `(n + 1)^{x - 1}` bound. -/
theorem deFinettiPrefactor_le_pow (x n : ℕ) : deFinettiPrefactor x n ≤ (n + 1) ^ (x - 1) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp [deFinettiPrefactor]
  · have heq : deFinettiPrefactor x n = Nat.choose (n + (x - 1)) (x - 1) := by
      rw [deFinettiPrefactor]; congr 1; omega
    rw [heq]
    exact Nat.choose_add_le_add_one_pow n (x - 1)

/-- The Bell-symmetric prefactor is `C(n + 3, 3)`, the factor of the Bell–Rényi security theorem. -/
theorem deFinettiPrefactor_four (n : ℕ) : deFinettiPrefactor 4 n = Nat.choose (n + 3) 3 := rfl

end Math.Combinatorics
