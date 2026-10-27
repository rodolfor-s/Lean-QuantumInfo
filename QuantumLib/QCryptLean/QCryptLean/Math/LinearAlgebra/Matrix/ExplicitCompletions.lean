import QCryptLean.Math.LinearAlgebra.Matrix.GramPolarCompletion
import QCryptLean.Math.LinearAlgebra.Matrix.HermitianPinv
import QCryptLean.Math.LinearAlgebra.Matrix.KernelCompletion

/-!
# Explicit spectral completions of matrices

Aggregator for the three spectral constructions that turn the library's existential
isometry/pseudoinverse statements into named functions of their input.  It contains no
declarations of its own.

* `HermitianPinv.lean` — `Matrix.hermitianPinv M = cfc (·⁻¹) M`, the Moore–Penrose pseudoinverse
  of a Hermitian matrix, with the four Moore–Penrose identities.  Strengthens the existential
  `Quantum.Channels.exists_moorePenrose_pinv_of_posSemidef` (Hermitian rather than positive
  semidefinite,
  and with a witness).
* `GramPolarCompletion.lean` — `Matrix.gramPolarCompletion A B`, a spectral-gauge co-isometry with
  `A Y = B` for `A Aᴴ = B B` and `B` positive semidefinite: the Uhlmann/polar gauge, fixed
  spectrally.
* `KernelCompletion.lean` — `Matrix.kerComplIso`, the explicit orthonormal basis of the kernel of
  a Hermitian matrix, and `Matrix.partialIsometryExtend`, the resulting explicit isometric
  extension of a partial isometry.  Realizes
  `Matrix.exists_isometric_extension_of_partialIsometry`.

These are named noncomputable formulas built from continuous functional calculus and spectral
data. The completion matrices use Mathlib's chosen orthonormal eigenbases and are not
basis-choice-independent. The existing existential statements remain available unchanged.
-/
