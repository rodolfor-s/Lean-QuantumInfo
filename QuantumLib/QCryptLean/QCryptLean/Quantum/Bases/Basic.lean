import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-!
# Finite ket combinations and mutually unbiased families

Basis labels and quantum-register indices have independent finite types.
Flatness uses the cardinality of the quantum register, including the usual real
inverse convention at cardinality zero.
-/

namespace Quantum.Bases

open Matrix Quantum.Operators

variable {X I J : Type*}

/-- A finite linear combination of kets, formed in the actual register coordinates. -/
def ketCombination (s : Finset I) (a : I → ℂ) (b : I → Ket X) : Ket X :=
  ⟨fun x => ∑ i ∈ s, a i * (b i).vec x⟩

/-- Mutual unbiasedness of two labelled families on the same finite register. -/
def IsMutuallyUnbiased [Fintype X] (a : I → Ket X) (b : J → Ket X) : Prop :=
  ∀ i j, Complex.normSq ((a i).dag * b j : ℂ) = 1 / (Fintype.card X : ℝ)

/-- Pairing with a finite ket combination distributes over the coefficients. -/
theorem bra_mul_ketCombination [Fintype X] (v : Bra X) (s : Finset I)
    (a : I → ℂ) (b : I → Ket X) :
    (v * ketCombination s a b : ℂ) = ∑ i ∈ s, a i * (v * b i : ℂ) := by
  change (∑ x, v.vec x * ∑ i ∈ s, a i * (b i).vec x) =
    ∑ i ∈ s, a i * ∑ x, v.vec x * (b i).vec x
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

/-- Reversing a ket inner product conjugates its scalar value. -/
theorem ket_inner_conj [Fintype X] (v w : Ket X) :
    (v.dag * w : ℂ) = star (w.dag * v : ℂ) := by
  change (∑ i, star (v.vec i) * w.vec i) = star (∑ i, star (w.vec i) * v.vec i)
  simp only [star_sum, star_mul, star_star]

/-- Parseval on a finite orthonormal support, without normalization assumptions. -/
theorem ketCombination_inner_self_of_orthonormalOn [Fintype X] [DecidableEq I]
    (s : Finset I) (a : I → ℂ) (b : I → Ket X)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ((b i).dag * b j : ℂ) = if i = j then 1 else 0) :
    ((ketCombination s a b).dag * ketCombination s a b : ℂ) =
      ((∑ i ∈ s, Complex.normSq (a i) : ℝ) : ℂ) := by
  have hcoeff : ∀ j ∈ s, ((ketCombination s a b).dag * b j : ℂ) = star (a j) := by
    intro j hj
    rw [ket_inner_conj, bra_mul_ketCombination,
      Finset.sum_congr rfl fun i hi => by rw [horth j hj i hi]]
    simp [Finset.sum_ite_eq, hj]
  rw [bra_mul_ketCombination, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i hi => by
    rw [hcoeff i hi, Complex.star_def, Complex.mul_conj]

/-- A family resolving the identity satisfies Parseval for every ket. -/
theorem sum_normSq_bra_mul_of_complete [Fintype X] [DecidableEq X]
    {W : Type*} [Fintype W] (a : W → Ket X)
    (hcomplete : (∑ w, (a w).projector) = (1 : Op X)) (ψ : Ket X) :
    ((∑ w, Complex.normSq ((a w).dag * ψ) : ℝ) : ℂ) = (ψ.dag * ψ : ℂ) := by
  have hterm : ∀ w : W, ((Complex.normSq ((a w).dag * ψ) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (ψ.vec i) * (a w).projector i j * ψ.vec j := by
    intro w
    rw [← Complex.mul_conj]
    change (∑ j, star ((a w).vec j) * ψ.vec j) *
      star (∑ i, star ((a w).vec i) * ψ.vec i) = _
    rw [star_sum]
    simp only [star_mul, star_star]
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ = star (ψ.vec i) * ((a w).vec i * star ((a w).vec j)) * ψ.vec j
    ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_comm]
  change _ = ∑ i, star (ψ.vec i) * ψ.vec i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.sum_apply, hcomplete]
  simp [Matrix.one_apply]

end Quantum.Bases
