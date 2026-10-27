import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.MatrixUnits
import QCryptLean.QKD.BB84.Model.BellPostMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Bell

/-!
# Bell conjugation and computational measurement on natural signal registers

The common Boolean Bell action is relabelled componentwise onto the protocol's pair of bits.
The repeated action uses a function register. Its computational projectors are permuted, so
computational measurement commutes with that action, including an arbitrary retained reference.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Matrix Quantum.Operators Quantum.Channels
open Quantum.Symmetry QKD.BB84.Measurement
open scoped Kronecker ComplexConjugate

/-- The common bilateral Pauli action in the protocol's two-bit basis. -/
def signalBilateralPauli (g : Fin 4) : Op Signal :=
  reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm) (bilateralPauli g)

/-- The independent bilateral Pauli action on a function of signal pairs. -/
def signalBellUnitary {n : ℕ} (g : Fin n → Fin 4) : Op (Signals n) :=
  piTensorProduct (fun i => signalBilateralPauli (g i))

/-- The signal Bell action is unitary on every number of rounds, including zero. -/
theorem signalBellUnitary_unitary {n : ℕ} (g : Fin n → Fin 4) :
    (signalBellUnitary g)ᴴ * signalBellUnitary g = 1 := by
  have h (a : Fin 4) : (signalBilateralPauli a)ᴴ * signalBilateralPauli a = 1 := by
    simpa only [signalBilateralPauli, reindex_apply, conjTranspose_submatrix,
      submatrix_mul_equiv, submatrix_one_equiv] using
      congrArg (reindex (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)
        (finTwoEquiv.symm.prodCongr finTwoEquiv.symm)) (bilateralPauli_unitary a)
  rw [signalBellUnitary, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [h, piTensorProduct_one]

/-- The bilateral Paulis either retain both bits or flip both bits. -/
def bellKeyOutcomePerm (g : Fin 4) (ω : Signal) : Signal :=
  ![ω, (Fin.rev ω.1, Fin.rev ω.2), (Fin.rev ω.1, Fin.rev ω.2), ω] g

private def bellKeyOutcomeSign (g : Fin 4) (ω : Signal) : ℂ :=
  ![1, 1, if ω.1 = ω.2 then -1 else 1, if ω.1 = ω.2 then 1 else -1] g

private theorem signalBilateralPauli_apply (g : Fin 4) (i ω : Signal) :
    signalBilateralPauli g i ω =
      if i = bellKeyOutcomePerm g ω then bellKeyOutcomeSign g ω else 0 := by
  rcases i with ⟨a, b⟩
  rcases ω with ⟨c, d⟩
  fin_cases g <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [signalBilateralPauli, reindex_apply, submatrix_apply, bilateralPauli,
      pauli, pauliX, pauliY, pauliZ, kroneckerMap_apply, diagonal_apply,
      one_apply, finTwoEquiv, bellKeyOutcomePerm, bellKeyOutcomeSign, Fin.rev]

/-- A bilateral Pauli conjugates each computational projector to its relabelled projector. -/
theorem bellSinglePair_conj_compProjector (g : Fin 4) (ω : Signal) :
    signalBilateralPauli g * single ω ω 1 * (signalBilateralPauli g)ᴴ =
      single (bellKeyOutcomePerm g ω) (bellKeyOutcomePerm g ω) 1 := by
  have hcol : signalBilateralPauli g * single ω ω 1 =
      single (bellKeyOutcomePerm g ω) ω (bellKeyOutcomeSign g ω) := by
    ext i j
    by_cases hj : j = ω
    · subst j
      rw [mul_single_apply_same, mul_one, signalBilateralPauli_apply]
      simp only [single_apply, and_true]
      simp only [eq_comm]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hj]
      simp [Ne.symm hj]
  rw [conj_single_of_mul_single _ _ _ _ hcol]
  congr 1
  rcases ω with ⟨a, b⟩
  fin_cases g <;> fin_cases a <;> fin_cases b <;> norm_num [bellKeyOutcomeSign]

/-- The simultaneous bit flip is an involution. -/
theorem bellKeyOutcomePerm_involutive (g : Fin 4) :
    Function.Involutive (bellKeyOutcomePerm g) := by
  intro ⟨a, b⟩
  fin_cases g <;> simp [bellKeyOutcomePerm]

/-- The single-round Bell outcome action as an equivalence of signal pairs. -/
def bellKeyOutcomePermEquiv (g : Fin 4) : Equiv.Perm Signal :=
  (bellKeyOutcomePerm_involutive g).toPerm

/-- The independent Bell outcome action on the protocol's signal function. -/
def bellOutcomePerm (n : ℕ) (g : Fin n → Fin 4) : Equiv.Perm (Signals n) :=
  Equiv.piCongrRight (fun i => bellKeyOutcomePermEquiv (g i))

/-- The outcome action evaluates separately at each round. -/
theorem bellOutcomePerm_apply (n : ℕ) (g : Fin n → Fin 4) (ω : Signals n) :
    bellOutcomePerm n g ω = fun i => bellKeyOutcomePerm (g i) (ω i) := rfl

/-- Each repeated Bell outcome action is an involution. -/
theorem bellOutcomePerm_involutive (n : ℕ) (g : Fin n → Fin 4) :
    Function.Involutive (bellOutcomePerm n g) := by
  intro ω
  funext i
  exact bellKeyOutcomePerm_involutive (g i) (ω i)

/-- The inverse Bell outcome action is the same action. -/
theorem bellOutcomePerm_symm (n : ℕ) (g : Fin n → Fin 4) :
    (bellOutcomePerm n g).symm = bellOutcomePerm n g := by
  apply Equiv.ext
  intro ω
  rw [Equiv.symm_apply_eq]
  exact (bellOutcomePerm_involutive n g ω).symm

/-- Repeated Bell conjugation permutes computational projectors pointwise. -/
theorem bellTwirlUnitary_conj_single (n : ℕ) (g : Fin n → Fin 4) (ω : Signals n) :
    signalBellUnitary g * single ω ω 1 * (signalBellUnitary g)ᴴ =
      single (bellOutcomePerm n g ω) (bellOutcomePerm n g ω) 1 := by
  rw [← piTensorProduct_single_one ω ω, signalBellUnitary,
    conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
  simp only [bellSinglePair_conj_compProjector, piTensorProduct_single_one]
  rfl

/-- Computational measurement commutes with Bell conjugation with any retained register. -/
theorem measurementChannel_bellTwirl_outcomeRelabel {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E] (g : Fin n → Fin 4)
    (M : Op (Signals n × E)) :
    mapTensorId (classicalMap (id : Signals n → Signals n)) E
        ((signalBellUnitary g ⊗ₖ (1 : Op E)) * M * (signalBellUnitary g ⊗ₖ (1 : Op E))ᴴ) =
      (signalBellUnitary g ⊗ₖ (1 : Op E)) *
        mapTensorId (classicalMap (id : Signals n → Signals n)) E M *
          (signalBellUnitary g ⊗ₖ (1 : Op E))ᴴ := by
  classical
  let π := bellOutcomePerm n g
  have hπ := bellTwirlUnitary_conj_single n g
  have h : (classicalMap (id : Signals n → Signals n)).comp
      (Matrix.conjLinearMap (signalBellUnitary g)) =
      (Matrix.conjLinearMap (signalBellUnitary g)).comp (classicalMap id) := by
    apply LinearMap.ext
    intro A
    exact classicalMap_id_conj_of_permutes_single (signalBellUnitary g) π
      (signalBellUnitary_unitary g) hπ A
  have he := congrArg (fun Φ : Operation (Signals n) (Signals n) => mapTensorId Φ E M) h
  simpa only [mapTensorId_comp, LinearMap.comp_apply, mapTensorId_conjLinearMap,
    Matrix.conjLinearMap_apply] using he

end QKD.BB84.FiniteKey
