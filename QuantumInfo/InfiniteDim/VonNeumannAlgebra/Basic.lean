/-
Copyright (c) 2026 Rodolfo R. Soldati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rodolfo R. Soldati
-/
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Topology.Algebra.Module.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence

/-
Based on Hiai's Lectures on Selected Topics in von Neumann Algebras:
- https://arxiv.org/abs/2004.02383, and its published version
- https://doi.org/10.4171/elm/32
-/

#check VonNeumannAlgebra
-- Defined concretly through `[InnerProduct Space ℂ H] [CompleteSpace H]`
-- Is of `Type u`

#check WStarAlgebra
-- Defined through `[CStarAlgebra M]`
-- Is of `Prop`

/- DOING: Import
1. ✓ Strong operator topology (SOT)
  - PointwiseConvergence
  - Imported now
2. ✓ Weak operator topology (WOT)
  - WOT is imported now
  - "type copy" of `E →SL[σ] F` with WOT: `E →WOT[𝕜] F`
  - see also `E →SWOT[σ] F`
  - `σ` is probably something like 'complex conjugate' is for `𝕜`
3. ⊘ Ultraweak (σ-weak) operator topology
-/

/-
1. TODO: Define algebraic states,
2. TODO: Define normal states
-/

/- Hiai vNAlgebra: unital subalgebra of some B(H) closed under adjoint
(`NonUnitalStarSubalgebra`), and closed under SOT (WOT? See Hiai) closure -/

/-! # Guided exercises -/

/-! ## Exercise 1: an API comparing the SOT and the WOT

**Math.** On `B(H)`, if `Aᵢ → A` strongly (`Aᵢ x → A x` for all `x`),
then `Aᵢ → A` weakly (`⟪y, Aᵢ x⟫ → ⟪y, A x⟫` for all `x, y`).
So the identity `(B(H), SOT) → (B(H), WOT)` is continuous,
and every WOT-closed set is SOT-closed.

**Reference.** Hiai §1.1 (p. 1): norm, strong and weak operator topologies,
"weaker in this order". Hiai §1.2 (p. 2): a von Neumann algebra is a
*-subalgebra containing `1` that is *weakly* closed; the double commutant
theorem says weakly closed ⇔ strongly closed ⇔ `M'' = M`.

**Who might use this? (proposals, to be decided together)**
* *QuantumInfo, infinite-dimensional states.* Hiai §1.3 defines normal
  states through the σ-weak topology, which agrees with the WOT on bounded
  sets. Comparing SOT and WOT now could be a stepping stone towards normal
  states (and towards reviving `QuantumInfo/InfiniteDim/QState.lean`).
* *A bridge to `QuantumInfo/Finite`.* On `B(ℂ^d)` all these topologies
  coincide. One possible sanity target: `MState d` should be exactly the
  normal states on `⊤ : VonNeumannAlgebra (EuclideanSpace ℂ d)`.
* *Physlib.* Algebraic QM / QFT (nets of von Neumann algebras) and
  equilibrium states in statistical mechanics (KMS states, Hiai §2.2) are
  stated with these topologies. Whether Physlib wants them is to be checked.
* *Mathlib (secondary).* `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean`
  lists the double commutant theorem as a TODO, and SOT ↔ WOT is one of its
  ingredients.

**The exercise: design and build a small API.** The `sorry` below is a
deliberately naive *first draft*. Your job is to turn it into a small
API that other files in this library would want to import.
1. *Critique the draft.* Which of these would you change, and why?
   * Its name: Mathlib says "pointwise convergence", not "SOT".
   * Its generality: `ℂ` and `H`, versus `𝕜`, `E`, `F`, or semilinear `σ`.
   * Its form: an unbundled `Continuous` statement versus a bundled `→L`.
   * Its location: this file, `QuantumInfo/ForMathlib/`, or a namespace.
2. *Decide how to say "S ⊆ B(H) is WOT-closed".* Some options:
   `IsClosed (toWOT '' S)`, a preimage, or a new predicate such as
   `IsWOTClosed S`. Test each option by writing (with `sorry`) the statement
   "every `VonNeumannAlgebra H` is WOT-closed", and keep the one that reads
   best for the users listed above.
3. *Build it.* Two to four declarations: the comparison map, the
   "WOT-closed → SOT-closed" lemma, and anything step 2 asked for.
4. *Record your decisions* in a short *Design notes* block, so the
  next exercise (and the next contributor) can build on them.

**Hints** (open one at a time).
1. *Design precedent.* Read how Mathlib compares the *norm* topology with
   each of the two: `ContinuousLinearMap.continuous_toWOT` and
   `ContinuousLinearMap.toWOTCLM` (end of
   `Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean`), and
   `ContinuousLinearMap.toPointwiseConvergenceCLM` (in
   `Mathlib/Topology/Algebra/Module/PointwiseConvergence.lean`). Your API
   fills the missing third side of that triangle; matching their shape
   makes it feel native.
2. *Generality.* Look at which instances the proof actually uses. If
   `[CompleteSpace H]` or the inner product are never used, the honest
   statement is about topological vector spaces, and `ℂ`/`H` can become an
   `example` or a specialization.
3. *Proof.* `ContinuousLinearMapWOT.continuous_of_dual_apply_continuous`
   reduces continuity into the WOT to continuity of `A ↦ y (A x)`, which is
   `y.cont.comp (continuous_eval_const x)`. (`fun_prop` fails on this goal
   in the current Mathlib.)
4. *Closed sets.* `IsClosed.preimage`. If an image is awkward, note that
   `ContinuousLinearMap.toWOT` is a `LinearEquiv`, so images and preimages
   of its inverse coincide (`Equiv.image_eq_preimage_symm`, via `.toEquiv`).

**Lean skills practiced.** Reading a Mathlib file for its API shape;
naming and generality conventions; type copies (`→Lₚₜ`, `→WOT`);
bundled versus unbundled maps; writing `sorry`-ed statements as
design tests.
-/

section Exercise1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- First draft (critique and replace me): the identity map from `B(H)` with
the SOT to `B(H)` with the WOT is continuous. -/
theorem continuous_SOT_to_WOT :
    Continuous (fun A : H →Lₚₜ[ℂ] H => ContinuousLinearMap.toWOT (RingHom.id ℂ) H H A) := by
  sorry

-- Your API here.

end Exercise1
