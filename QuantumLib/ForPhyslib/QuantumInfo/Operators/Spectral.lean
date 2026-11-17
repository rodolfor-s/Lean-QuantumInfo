import QuantumLib.ForMathlib.Analysis.Matrix.SpectralTheory.Eigenvalues
import QuantumLib.ForMathlib.Analysis.Matrix.SpectralTheory.TensorSpectrum
import QuantumLib.ForMathlib.Analysis.Matrix.SpectralTheory.Matrix
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Spectrum

/-! # Spectral -/


namespace Quantum.Operators

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- Product-indexed spectral data agree with the product of the spectral multisets. -/
theorem hermitianEigenvaluesProd_reindex {Y : Type*} [Fintype Y] [DecidableEq Y] {m : ℕ}
    (e : X ≃ Fin n) (f : Y ≃ Fin m) (A : Op (X × Y)) (h : A.IsHermitian) :
    Math.SpectralTheory.hermitianEigenvaluesProd
        (Matrix.reindex (e.prodCongr f) (e.prodCongr f) A) (h.reindex (e.prodCongr f)) =
      h.eigenvalueMultiset := h.eigenvalueMultiset_reindex (e.prodCongr f)

end Quantum.Operators
