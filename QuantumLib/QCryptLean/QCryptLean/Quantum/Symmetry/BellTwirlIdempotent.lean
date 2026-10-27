import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination

/-! # Bell Twirl Idempotent -/



noncomputable section

open scoped BigOperators

namespace Quantum.Symmetry

/-- **The Klein-four (`ℤ₂×ℤ₂`) addition table on `Fin 4`** (the index XOR). -/
def kleinFourAdd : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- **The single-qubit Pauli cocycle** `ω(a,b) ∈ {1, i, -i}` with `P a · P b = ω(a,b) · P(a⊕b)`. -/
def bellPauliCocycle : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I], ![1, -Complex.I, 1, Complex.I],
    ![1, Complex.I, -Complex.I, 1]]

/-- **The bilateral-Pauli `±1` cocycle** `ω²` with `G a · G b = bellSignCocycle(a,b) · G(a⊕b)`. -/
def bellSignCocycle (a b : Fin 4) : ℂ := bellPauliCocycle a b * bellPauliCocycle a b

/-- The Bell cocycle `bellSignCocycle` is a unit:
`bellSignCocycle(a,b) · conj(bellSignCocycle(a,b)) = 1`. -/
private theorem bellPh_unit (a b : Fin 4) :
    bellSignCocycle a b * (starRingEnd ℂ) (bellSignCocycle a b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [bellSignCocycle, bellPauliCocycle]

/-- `kleinFourAdd x ·` is an involution (`ℤ₂×ℤ₂` translation). -/
private theorem kleinAdd_klein (x y : Fin 4) : kleinFourAdd x (kleinFourAdd x y) = y := by
  fin_cases x <;> fin_cases y <;> rfl

end Quantum.Symmetry

end -- noncomputable section
