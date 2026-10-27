import QCryptLean.Math.LinearAlgebra.MatrixUnits
import QCryptLean.Math.LinearAlgebra.PermutationMatrix
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RoundKernel
import QCryptLean.QKD.BB84.Registers

/-!
# The unit phases in Bell outcome relabelling

The common matrix-unit lemmas describe signed monomial actions. Here the action is the
pointwise Bell permutation of the protocol's signal functions. The generic phased Kraus
intertwining law lives in `Quantum.Channels.KrausAlgebra`.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators QKD.BB84.Measurement
open scoped ComplexConjugate

/-- The unit phase of the Bell action at an outcome string. -/
def bellTwirlSign (n : ℕ) (g : Fin n → Fin 4) (ω : Signals n) : ℂ :=
  signalBellUnitary g ω (bellOutcomePerm n g ω)

/-- The Bell phase has unit squared modulus. -/
theorem bellTwirlSign_unit (n : ℕ) (g : Fin n → Fin 4) (ω : Signals n) :
    bellTwirlSign n g ω * star (bellTwirlSign n g ω) = 1 := by
  have h := mul_star_eq_one_of_conj_single (signalBellUnitary g) (bellOutcomePerm n g)
    (bellTwirlUnitary_conj_single n g) (bellOutcomePerm n g ω)
  simpa only [bellOutcomePerm_involutive n g ω, bellTwirlSign] using h

/-- Right multiplication by the Bell action relabels a Kraus column and adds its unit phase. -/
theorem single_mul_bellTwirlUnitary {Y : Type*} [DecidableEq Y] {n : ℕ}
    (a : Y) (g : Fin n → Fin 4) (ω : Signals n) :
    (single a ω 1 : Matrix Y (Signals n) ℂ) * signalBellUnitary g =
      bellTwirlSign n g ω • single a (bellOutcomePerm n g ω) 1 := by
  have h := single_mul_of_conj_single (signalBellUnitary g) (bellOutcomePerm n g)
    (bellTwirlUnitary_conj_single n g) a ω
  simpa only [bellOutcomePerm_symm, bellTwirlSign] using h

end QKD.BB84.FiniteKey
