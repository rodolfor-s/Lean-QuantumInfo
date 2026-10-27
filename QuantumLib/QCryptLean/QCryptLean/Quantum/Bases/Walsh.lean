import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import QCryptLean.Quantum.Bases.Basic
import QCryptLean.Quantum.Bases.WalshHadamard
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet

/-!
# Walsh kets on Boolean function registers

The scalar Walsh characters from `Quantum.Bases.WalshHadamard` define an
orthonormal basis on Boolean function registers.
-/

noncomputable section

namespace Quantum.Bases

open Matrix Quantum.Operators
open scoped ComplexConjugate

variable {n : ℕ}

/-- **The Walsh–Hadamard basis ket** `|e⟩_H = 2^{-n/2} ∑_w (-1)^{⟨w,e⟩} |w⟩` of `ℂ^{2ⁿ}`,
indexed by the bit string `e`.  Physically this is the `n`-qubit BB84 `X`-basis state. -/
def walshKet (e : Fin n → Bool) : Ket (Fin n → Bool) :=
  ⟨fun w => walshSign w e / ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)⟩

@[simp] lemma walshKet_vec (e : Fin n → Bool) (w : Fin n → Bool) :
    (walshKet e).vec w = walshSign w e / ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) := rfl

/-- Walsh kets are orthonormal directly on the Boolean function register. -/
theorem walshKet_orthonormal (e f : Fin n → Bool) :
    ((walshKet e).dag * walshKet f : ℂ) = if e = f then 1 else 0 := by
  classical
  have ht (w : Fin n → Bool) :
      star ((walshKet e).vec w) * (walshKet f).vec w =
        walshSign e w * walshSign f w * ((2 : ℂ) ^ n)⁻¹ := by
    simp only [walshKet_vec, Complex.star_def]
    rw [map_div₀, conj_walshSign, Complex.conj_ofReal, div_mul_div_comm,
      walsh_sqrt_mul_self, div_eq_mul_inv]
    rw [walshSign_comm w e, walshSign_comm w f]
  change (∑ w, star ((walshKet e).vec w) * (walshKet f).vec w) = _
  simp_rw [ht]
  rw [← Finset.sum_mul, sum_walshSign_mul]
  split_ifs <;> simp

/-- Walsh projectors resolve the identity on the Boolean function register. -/
theorem walshKet_complete :
    (∑ e : Fin n → Bool, (walshKet e).projector) = (1 : Op (Fin n → Bool)) := by
  classical
  ext x y
  rw [Matrix.sum_apply]
  have ht (e : Fin n → Bool) : (walshKet e).projector x y =
      walshSign x e * walshSign y e * ((2 : ℂ) ^ n)⁻¹ := by
    change (walshKet e).vec x * star ((walshKet e).vec y) = _
    simp only [walshKet_vec, Complex.star_def]
    rw [map_div₀, conj_walshSign, Complex.conj_ofReal, div_mul_div_comm,
      walsh_sqrt_mul_self, div_eq_mul_inv]
  simp_rw [ht]
  rw [← Finset.sum_mul, sum_walshSign_mul, Matrix.one_apply]
  split_ifs <;> simp

/-- Computational and Walsh families are mutually unbiased. -/
theorem stdKet_walshKet_mutuallyUnbiased (n : ℕ) :
    IsMutuallyUnbiased stdKet (walshKet (n := n)) := by
  classical
  intro w e
  change Complex.normSq (∑ x, star (stdKet w).vec x * (walshKet e).vec x) = _
  simp only [stdKet, Pi.star_apply, Pi.single_apply, apply_ite, star_one, star_zero,
    ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [walshKet_vec, Complex.normSq_div, normSq_walshSign, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by positivity)]
  simp

end Quantum.Bases
