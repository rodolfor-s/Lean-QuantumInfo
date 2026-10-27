import QCryptLean.Math.SpectralTheory.LogMajorization
import QCryptLean.Math.SpectralTheory.SingularValues

/-!
# Trace power inequalities

Singular-value product bounds and weak log-majorization give trace power inequalities
for a matrix and its adjoint; cyclicity compares powers of matrix products.

## Main declarations

Main results include `trace_pow_mul_conjTranspose_pow_le`, `trace_pow_mul_comm`.

## References

Bhatia, *Matrix Analysis*, §IX.2; Araki, *Lett. Math. Phys.* 19 (1990).
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory


/-- **Squared singular-value power-sum bound** for the easy half: the squared
singular values of `Bᵐ` are out-summed by the `2m`-th powers of the singular
values of `B`:
`Σᵢ sᵢ(Bᵐ)² ≤ Σᵢ sᵢ(B)²ᵐ`.

Combines Weyl's product inequality `∏_{i<k} sᵢ(Bᵐ) ≤ ∏_{i<k} sᵢ(B)ᵐ`
(`singularValue_prod_pow_le_pow_singularValue`, the weak-log-majorization data)
with the Karamata sum bound `prod_le_to_sum_pow_le_of_antitone` applied to the
nonneg non-increasing families `sᵢ(Bᵐ)` and `sᵢ(B)ᵐ`. The right sum collapses to
`Σᵢ sᵢ(B)²ᵐ` since `(sᵢ(B)ᵐ)² = sᵢ(B)²ᵐ`. Reference: Bhatia, *Matrix Analysis*,
IX.2 + III. -/
lemma singularValue_pow_two_sum_pow_le {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    ∑ i : Fin N, (sortedSingularValues (B ^ m) (i : ℕ)) ^ 2
      ≤ ∑ i : Fin N, (sortedSingularValues B (i : ℕ)) ^ (2 * m) := by
  -- `b i := sᵢ(B)ᵐ` is nonneg and antitone (monotone power of a nonneg antitone family).
  have hbA : Antitone (fun i => (sortedSingularValues B i) ^ m) := by
    intro i j hij
    exact pow_le_pow_left₀ (sortedSingularValues_nonneg B j)
      (sortedSingularValues_antitone B i j hij) m
  have hkey := prod_le_to_sum_pow_le_of_antitone (N := N)
    (fun i => sortedSingularValues (B ^ m) i)
    (fun i => (sortedSingularValues B i) ^ m)
    (fun i => sortedSingularValues_nonneg (B ^ m) i)
    (fun i => pow_nonneg (sortedSingularValues_nonneg B i) m)
    (sortedSingularValues_antitone (B ^ m)) hbA
    (singularValue_prod_pow_le_pow_singularValue B m)
  refine hkey.trans_eq ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_mul, Nat.mul_comm m 2]

/-- **Schur trace bound** for the easy half: the real part of the (non-PSD)
product trace `tr(Bᵐ·(Bᴴ)ᵐ)` is dominated by the singular-value power sum:
`tr(Bᵐ·(Bᴴ)ᵐ).re ≤ Σᵢ sᵢ(B)²ᵐ`.

`tr(Bᵐ·(Bᴴ)ᵐ) = tr(Bᵐ·(Bᵐ)ᴴ) = ‖Bᵐ‖²_F = Σᵢ sᵢ(Bᵐ)²` is real and nonneg
(paired-symmetric support `σ(Bᵐ(Bᵐ)ᴴ) = σ((Bᵐ)ᴴBᵐ)`), and the singular-value
power sum is a Schur-convex functional ordered by the Weyl product inequality
`sₖ(Bᵐ) ≤ sₖ(B)ᵐ` (`singularValue_prod_pow_le_pow_singularValue`), giving
`Σᵢ sᵢ(Bᵐ)² ≤ Σᵢ (sᵢ(B)ᵐ)² = Σᵢ sᵢ(B)²ᵐ`.

Reference: Bhatia, *Matrix Analysis*, IX.2 (`tr|Bᵐ|` via Weyl majorization). -/
lemma trace_pow_mul_conjTranspose_pow_re_le_singularValue_sum {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    (B ^ m * (Bᴴ) ^ m).trace.re ≤ ∑ i : Fin N, (sortedSingularValues B (i : ℕ)) ^ (2 * m) := by
  rw [trace_pow_mul_conjTranspose_pow_eq_singularValue_pow_two_sum B m]
  exact singularValue_pow_two_sum_pow_le B m

/-- Monoid "swap-and-collapse" identity: `b · (c · b)^p · c = (b · c)^{p+1}`.

For `b = B`, `c = Bᴴ` this is the algebraic backbone of the Araki easy-half
descent induction: it turns one sandwiched factor `(B·Bᴴ)^{p+1}` into the form
`B · (Bᴴ·B)^p · Bᴴ`, moving one `B`/`Bᴴ` from the inner power out to the
conjugating sleeves. Pure monoid statement, proved by induction on `p`. -/
lemma mul_swap_pow_mul {M : Type*} [Monoid M] (b c : M) :
    ∀ p : ℕ, b * (c * b) ^ p * c = (b * c) ^ (p + 1) := by
  intro p
  induction p with
  | zero => simp
  | succ n ih =>
    calc b * (c * b) ^ (n + 1) * c
        = (b * (c * b) ^ n * c) * (b * c) := by rw [pow_succ]; noncomm_ring
      _ = (b * c) ^ (n + 1) * (b * c) := by rw [ih]
      _ = (b * c) ^ (n + 1 + 1) := (pow_succ (b * c) (n + 1)).symm

/-- Araki's trace inequality (integer "easy half"), general matrix form.

For an arbitrary square matrix `B` over `ℂ` and any exponent `m`:
`tr(Bᵐ · (Bᴴ)ᵐ).re ≤ tr((Bᴴ · B)ᵐ).re`.

This is the matrix-analytic core of the dyadic Araki-Lieb-Thirring induction. Its
content is the log-majorization `λ(B·Bᴴ) ≺_log λ(Bᴴ·B)` lifted through the
power-sum `t ↦ tᵐ`: the eigenvalues of the (PSD) matrices `B·Bᴴ` and `Bᴴ·B`
agree, but `tr(Bᵐ·(Bᴴ)ᵐ)` is the trace of a *non-PSD* product whose real part
is controlled by Araki's antisymmetric-tensor-power (Weyl product) inequalities.

This statement is **reduced** here to the singular-value (Bhatia IX.2) argument,
bottoming out at two compound-matrix (`⋀ᵏ`) spectral leaves:
`tr(Bᵐ·(Bᴴ)ᵐ).re ≤ Σᵢ sᵢ(B)²ᵐ`
(`trace_pow_mul_conjTranspose_pow_re_le_singularValue_sum`, the Weyl/Schur trace
bound) and the closing identity `Σᵢ sᵢ(B)²ᵐ = tr((Bᴴ·B)ᵐ).re`
(`singularValue_pow_sum_eq_trace`, proved). The Weyl trace bound is in turn the
sum form of `singularValue_prod_pow_le_pow_singularValue` (`sₖ(Bᵐ) ≤ sₖ(B)ᵐ`).
The remaining spectral content (Araki's antisymmetric-tensor-power /
log-majorization inequality) lives entirely in those two singular-value leaves.

The monoid descent identity `mul_swap_pow_mul` records the same descent step in isolation
and is retained as reusable matrix-power algebra.

Reference: Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. 19
(1990), 167-170; Bhatia, *Matrix Analysis*, IX.2. Consumed by the dyadic
doubling kernel `InfoTheory.RelativeEntropy.re_trace_mul_pow_mul_pow_le_re_trace_sq_mul_sq_pow` of
the
Golden-Thompson chain in Nahar, Tupkary, Zhao, Lütkenhaus, Tan arXiv:2403.11851. -/
lemma trace_pow_mul_conjTranspose_pow_le {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    (B ^ m * (Bᴴ) ^ m).trace.re ≤ ((Bᴴ * B) ^ m).trace.re := by
  calc (B ^ m * (Bᴴ) ^ m).trace.re
      ≤ ∑ i : Fin N, (sortedSingularValues B (i : ℕ)) ^ (2 * m) :=
        trace_pow_mul_conjTranspose_pow_re_le_singularValue_sum B m
    _ = ((Bᴴ * B) ^ m).trace.re := singularValue_pow_sum_eq_trace B m

/-! ## Trace cyclicity for powers -/

/-- `(a · b) ^ k · a = a · (b · a) ^ k` in any monoid; the algebraic step behind trace
cyclicity for powers. -/
private lemma mul_pow_mul_aux {M : Type*} [Monoid M] (a b : M) :
    ∀ k : ℕ, (a * b) ^ k * a = a * (b * a) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc (a * b) ^ (k + 1) * a = (a * b) ^ k * a * (b * a) := by rw [pow_succ]; noncomm_ring
      _ = a * (b * a) ^ k * (b * a) := by rw [ih]
      _ = a * (b * a) ^ (k + 1) := by rw [mul_assoc, ← pow_succ]

/-- **Trace cyclicity for powers**: `Tr ((A · B) ^ k) = Tr ((B · A) ^ k)`.

The `k = 1` case is `Matrix.trace_mul_comm`; for higher powers one factor is carried
around the product by `mul_pow_mul_aux`. This is the reduction used to pass between the
product form `(P · Q) ^ k` and the sandwich form `(√P · Q · √P) ^ k` of the
Araki–Lieb–Thirring inequality. -/
theorem trace_pow_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (k : ℕ) :
    ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => simp
  | succ k =>
    calc ((A * B) ^ (k + 1)).trace = ((A * B) ^ k * A * B).trace := by
          rw [pow_succ, Matrix.mul_assoc]
      _ = (B * ((A * B) ^ k * A)).trace := Matrix.trace_mul_comm _ _
      _ = (B * (A * (B * A) ^ k)).trace := by rw [mul_pow_mul_aux]
      _ = ((B * A) ^ (k + 1)).trace := by rw [← Matrix.mul_assoc, ← pow_succ']


end Math.SpectralTheory
