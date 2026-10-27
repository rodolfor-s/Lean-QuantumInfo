import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Bell

/-! # Elementary gates on Boolean quantum registers -/

noncomputable section

namespace Quantum.Gates

open Matrix Quantum.Operators Quantum.Symmetry

/-- The Hadamard matrix in the Boolean computational basis. -/
def hadamard : Op Bool := fun i j => (Real.sqrt 2 : ℂ)⁻¹ * if i && j then -1 else 1

/-- The diagonal quarter-turn phase gate. -/
def phaseS : Op Bool := diagonal (fun i => if i then Complex.I else 1)

/-- The diagonal eighth-turn phase gate. -/
def phaseT : Op Bool :=
  diagonal (fun i => if i then Complex.exp (Complex.I * (Real.pi / 4)) else 1)

/-- The identity gate. -/
def gateI : Op Bool := 1

/-- Controlled NOT, with the first component controlling the second. -/
def cnot : Op (Bool × Bool) := fun i j => if i = (j.1, xor j.1 j.2) then 1 else 0

/-- Exchange the two Boolean registers. -/
def swap : Op (Bool × Bool) := fun i j => if i = (j.2, j.1) then 1 else 0

/-- Apply a minus sign precisely on the `true,true` basis vector. -/
def cz : Op (Bool × Bool) := diagonal (fun i => if i.1 && i.2 then -1 else 1)

/-- The Hadamard matrix is Hermitian. -/
theorem isHermitian_hadamard : hadamard.IsHermitian := by
  ext i j
  cases i <;> cases j <;> simp [hadamard, conjTranspose_apply]

/-- Applying Hadamard twice is the identity. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j
  cases i <;> cases j <;>
    norm_num [hadamard, Matrix.mul_apply, Fintype.sum_bool, one_apply] <;>
    field_simp <;> linear_combination -hs

/-- Hadamard is a unitary on the Boolean register. -/
theorem hadamard_unitary : hadamardᴴ * hadamard = 1 := by
  rw [isHermitian_hadamard, hadamard_sq]

/-- Hadamard exchanges the X and Z Paulis and negates the Y Pauli. -/
theorem hadamard_conj_pauli (a : Fin 4) :
    hadamard * pauli a * hadamard =
      (if a = 2 then (-1 : ℂ) else 1) • pauli (![0, 3, 2, 1] a) := by
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv]
    have h : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [h]
    norm_num
  rw [← sq] at hs
  ext i j
  fin_cases a <;> cases i <;> cases j <;>
    norm_num [hadamard, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fintype.sum_bool, mul_add, add_mul] <;> ring_nf <;> simp [hs] <;> ring

end Quantum.Gates
