import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Continuity of real matrix powers, and positive definite regularisation

A positive semidefinite matrix is the limit of the positive definite matrices `A + ε`, and
`A ↦ A ^ t` is continuous on the positive semidefinite cone for `0 ≤ t`. Together these
transport an inequality between positive definite matrices to arbitrary positive semidefinite
ones — including singular ones — which is how the fractional Araki–Lieb–Thirring inequality
of `QCryptLean.Math.SpectralTheory.ArakiLiebThirring` reaches singular arguments.

## The continuous functional calculus and the matrix topology

`Matrix n n ℂ` carries `Matrix.IsHermitian.instContinuousFunctionalCalculus`, a continuous
functional calculus built from the spectral theorem with no norm at all, and the product
topology. Mathlib's continuity theorem for the functional calculus in the *matrix* variable
(`Filter.Tendsto.cfc_nnreal`) is stated for an algebra with an
`IsometricContinuousFunctionalCalculus`, which needs a norm.

The two meet: the operator norm of `Matrix.Norms.L2Operator` makes `Matrix n n ℂ` a
C⋆-algebra, and its metric is installed by `Matrix.instL2OpMetricSpace` through
`replaceTopology`/`replaceUniformity`, so the resulting topology *is* the product topology of
`Matrix n n ℂ`, not merely a homeomorphic copy. `ContinuousFunctionalCalculus` is a `Prop`,
so the calculus obtained from the C⋆-structure and the matrix calculus are the same term by
proof irrelevance, and the two calculi agree on the nose. The scoped instances are therefore
used only inside the proof below; every statement in this module is about the ordinary matrix
topology and the ordinary `CFC.rpow`.

## Main statements

- `Math.SpectralTheory.posDef_add_smul_one` : `A + ε` is positive definite for `0 < ε` and
  positive semidefinite `A`.
- `Math.SpectralTheory.tendsto_add_smul_one` : and it converges to `A` as `ε → 0`.
- `Math.SpectralTheory.tendsto_rpow_of_posSemidef` : `A x ^ t → A₀ ^ t` for `0 ≤ t` along any
  filter on which the matrices are positive semidefinite, including the zero-dimensional case.
- `Math.SpectralTheory.continuousOn_rpow_posSemidef`,
  `Math.SpectralTheory.continuousOn_sqrt_posSemidef` : the same facts as continuity on the
  positive semidefinite cone.
- `Math.SpectralTheory.continuousOn_rpow_nonneg`,
  `Math.SpectralTheory.continuousOn_sqrt_nonneg` : the same two statements with the cone
  written in the Löwner order of `MatrixOrder`, which is the form the continuous functional
  calculus states its own continuity in.

The Löwner and positive-semidefinite descriptions of the cone agree by
`Matrix.nonneg_iff_posSemidef`. The standard Frobenius and L² operator norm structures are
installed over the product uniformity, so both induce the ordinary product topology on matrices;
the two named `rfl` facts at the end of this file record these exact instances. The statements
below themselves use the ordinary matrix topology.

## References

- Mathlib `Analysis/CStarAlgebra/Matrix.lean` (the L² operator norm of a matrix algebra) and
  `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean` (continuity of the
  functional calculus in the algebra variable).
-/

open scoped Matrix ComplexOrder MatrixOrder NNReal

noncomputable section

namespace Math.SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Positive definite regularisation -/

omit [Fintype n] in
/-- Adding a positive multiple of the identity to a positive semidefinite matrix gives a
positive definite matrix. -/
theorem posDef_add_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ((ε : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
  have h1 : (((ε : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by simpa using hε)
  simpa [add_comm] using h1.add_posSemidef hA

omit [Fintype n] in
/-- The regularisation `A + ε` converges to `A` as `ε → 0`. -/
theorem tendsto_add_smul_one {X : Type*} {l : Filter X} (A : Matrix n n ℂ) {ε : X → ℝ}
    (hε : Filter.Tendsto ε l (nhds 0)) :
    Filter.Tendsto (fun x => A + ((ε x : ℝ) : ℂ) • (1 : Matrix n n ℂ)) l (nhds A) := by
  conv_rhs => rw [show A = A + 0 from (add_zero A).symm]
  refine Filter.Tendsto.const_add A ?_
  have h : Filter.Tendsto (fun x => ((ε x : ℝ) : ℂ)) l (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hε
  simpa using h.smul_const (1 : Matrix n n ℂ)

/-! ### Continuity of the real power -/

section OperatorNorm

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-- The nonempty-index case of `tendsto_rpow_of_posSemidef`, where the matrix algebra is a
nontrivial C⋆-algebra under the L² operator norm and Mathlib's functional-calculus continuity
applies verbatim. The spectra are collected in the compact interval `[0, ‖A₀‖ + 1]`. -/
private theorem tendsto_rpow_aux [Nonempty n] {X : Type*} {l : Filter X} {A : X → Matrix n n ℂ}
    {A₀ : Matrix n n ℂ} (hA : ∀ᶠ x in l, (A x).PosSemidef) (hA₀ : A₀.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (h : Filter.Tendsto A l (nhds A₀)) :
    Filter.Tendsto (fun x => A x ^ t) l (nhds (A₀ ^ t)) := by
  let : CStarAlgebra (Matrix n n ℂ) := {}
  simp_rw [CFC.rpow_def]
  refine h.cfc_nnreal (s := Set.Icc 0 (‖A₀‖₊ + 1)) isCompact_Icc (· ^ t) ?_ ?_ ?_ ?_ ?_
  · have hev : ∀ᶠ x in l, ‖A x‖₊ ≤ ‖A₀‖₊ + 1 :=
      h.nnnorm.eventually (Iic_mem_nhds (lt_add_one _))
    filter_upwards [hev] with x hx y hy
    exact ⟨zero_le, (spectrum.le_nnnorm_of_mem hy).trans hx⟩
  · filter_upwards [hA] with x hx using hx.nonneg
  · exact fun y hy => ⟨zero_le, (spectrum.le_nnnorm_of_mem hy).trans (le_add_right le_rfl)⟩
  · exact hA₀.nonneg
  · exact (NNReal.continuous_rpow_const ht).continuousOn

end OperatorNorm

/-- **Continuity of the real matrix power on the positive semidefinite cone**, filter form:
if `A x → A₀` with all matrices positive semidefinite and `0 ≤ t`, then `A x ^ t → A₀ ^ t`.

Nonnegativity of the exponent is what the proof uses: it makes `x ↦ x ^ t` continuous on
the compact spectral interval `[0, ‖A₀‖ + 1]`, which is the hypothesis of the
functional-calculus continuity theorem. For a negative exponent that function is unbounded
near `0`, so the argument says nothing at a singular limit. No nonemptiness hypothesis is
needed; over an empty index type every matrix statement is trivially true. -/
theorem tendsto_rpow_of_posSemidef {X : Type*} {l : Filter X} {A : X → Matrix n n ℂ}
    {A₀ : Matrix n n ℂ} (hA : ∀ᶠ x in l, (A x).PosSemidef) (hA₀ : A₀.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (h : Filter.Tendsto A l (nhds A₀)) :
    Filter.Tendsto (fun x => A x ^ t) l (nhds (A₀ ^ t)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hconst : (fun x => A x ^ t) = fun _ => A₀ ^ t := by
      funext x
      ext i
      exact (hn.false i).elim
    rw [hconst]
    exact tendsto_const_nhds
  · exact tendsto_rpow_aux hA hA₀ ht h

/-- **Continuity of the real matrix power on the positive semidefinite cone**: `A ↦ A ^ t` is
continuous on `{A | A.PosSemidef}` for every `0 ≤ t`. -/
theorem continuousOn_rpow_posSemidef {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun A : Matrix n n ℂ => A ^ t) {A | A.PosSemidef} := fun A hA =>
  tendsto_rpow_of_posSemidef (l := nhdsWithin A {A | A.PosSemidef})
    self_mem_nhdsWithin hA ht nhdsWithin_le_nhds

open scoped Classical in
/-- The continuous functional calculus square root is continuous on the positive semidefinite
cone: it is the real power at exponent `1 / 2`. -/
theorem continuousOn_sqrt_posSemidef {n : Type*} [Fintype n] :
    ContinuousOn (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ) {A | A.PosSemidef} := by
  classical
  exact
    (continuousOn_rpow_posSemidef (n := n) (t := 1 / 2) (by norm_num)).congr
      fun _ _ => CFC.sqrt_eq_rpow

omit [Fintype n] [DecidableEq n] in
/-- The positive semidefinite matrices are exactly the nonnegative ones for the Löwner order
of `MatrixOrder`. -/
theorem setOf_nonneg_eq_setOf_posSemidef :
    ({A | 0 ≤ A} : Set (Matrix n n ℂ)) = {A | A.PosSemidef} := by
  ext A
  exact Matrix.nonneg_iff_posSemidef

/-- `continuousOn_rpow_posSemidef` with the cone written in the Löwner order. -/
theorem continuousOn_rpow_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun A : Matrix n n ℂ => A ^ t) {A | 0 ≤ A} := by
  rw [setOf_nonneg_eq_setOf_posSemidef]
  exact continuousOn_rpow_posSemidef ht

open scoped Classical in
/-- `continuousOn_sqrt_posSemidef` with the cone written in the Löwner order. This is the
matrix instance of `CFC.continuousOn_sqrt`, which is stated on `{a | 0 ≤ a}` in a C⋆-algebra
with an isometric continuous functional calculus. -/
theorem continuousOn_sqrt_nonneg {n : Type*} [Fintype n] :
    ContinuousOn (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ) {A | 0 ≤ A} := by
  classical
  rw [setOf_nonneg_eq_setOf_posSemidef]
  exact continuousOn_sqrt_posSemidef

/-! ### The standard matrix norms carry the ordinary matrix topology -/

omit [DecidableEq n] in
/-- The standard Frobenius norm structure on matrices induces the ordinary product topology. -/
theorem frobenius_topologicalSpace_eq_pi :
    (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n)
        (α := ℂ)).toMetricSpace.toUniformSpace.toTopologicalSpace
      = Pi.topologicalSpace := rfl

section L2OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The standard L² operator norm structure on matrices induces the ordinary product topology. -/
theorem l2Operator_topologicalSpace_eq_pi :
    (inferInstance :
        NormedAddCommGroup (Matrix n n ℂ)).toMetricSpace.toUniformSpace.toTopologicalSpace
      = Pi.topologicalSpace := rfl

end L2OperatorNorm

end Math.SpectralTheory

end
