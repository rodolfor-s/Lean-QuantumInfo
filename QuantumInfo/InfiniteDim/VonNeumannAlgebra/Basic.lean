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
  - Not in Mathlib.
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
- *QuantumInfo, infinite-dimensional states.* Hiai §1.3 defines normal
  states through the σ-weak topology, which agrees with the WOT on bounded
  sets. Comparing SOT and WOT now could be a stepping stone towards normal
  states (and towards reviving `QuantumInfo/InfiniteDim/QState.lean`).
- *A bridge to `QuantumInfo/Finite`.* On `B(ℂ^d)` all these topologies
  coincide. One possible sanity target: `MState d` should be exactly the
  normal states on `⊤ : VonNeumannAlgebra (EuclideanSpace ℂ d)`.
- *Physlib.* Algebraic QM / QFT (nets of von Neumann algebras) and
  equilibrium states in statistical mechanics (KMS states, Hiai §2.2) are
  stated with these topologies. Whether Physlib wants them is to be checked.
- *Mathlib (secondary).* `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean`
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

/- How does Mathlib handle pointwise convergence topology?
- PointwiseConvergence topology is the name Mathlib claims to give to the Strong
  Operator Topology. Since the topological space in question is of operators,
  they have underlying function types, and corresponding coercions.
  - Say, `A : E → F` is the underlying function type.
- So an alias is created for that function type, and an instance of
  TopologicalSpace is given for that alias. See
  `UniformConvergenceTopology.lean`

How does the construction work?
- The codomain `F` is given as a topological space, and the topology of the
  domain `E` is the induced one by `A`: `(E →[withTop] F).induced A`.
  - The `induced` function is of type
    `(X → Y) → TopologicalSpace Y → TopologicalSpace X`
  - The way `induced` is invoked is as a pullback
- This construction is invoked for `E →SL[σ] F`, to bring the topology from
  `E →ᵤ[𝔖] F`, where the latter is a type alias with uniform topology.
-/

/-- Claude: the identity map from `B(H)` with
the SOT to `B(H)` with the WOT is continuous. -/
theorem continuous_SOT_to_WOT :
    Continuous (fun A : H →Lₚₜ[ℂ] H => ContinuousLinearMap.toWOT (RingHom.id ℂ) H H A) := by
  sorry

/-
1. Classification of factors
  - Factors through Murray-von Neumann projection theory
  - TODO: Define projections, and MvN equivalence, and MvN order
  - TODO: Define factors
2. Approximate finite-dimensionality
3. Uniqueness of purifications
    - Topological order:
      - Transportability: line-defect unitary that introduces a state from a reference, only depends on endpoints.
      - Detectability: a loop enclosing one endpoint, a projection based on that loop detects the...
    - Equivalence with Haag duality
      - From this equivalence, we can show that tomographic completeness can hold without Haag duality holding

- TODO: Define Haag duality. For factors M_A and M_B ⊆ B(H), M_A = M_B'
  - For M_B' the commutant of M_B
-/

-- def HaagDuality : A = B' := sorry

-- theorem UniqOfPure (Ψ Φ : Hilb) (h : ψ_A = φ_A) : ∀ ε > 0, ∃ u_B, ‖Ψ - u_B Φ‖ < ε := by sorry

-- theorem (A B : vNAlgebra(H)) (h : [A, B] = 0) : UniqOfPure ↔ A = B' := by sorry

end Exercise1

/-! ## Exercise 2: the network around the double commutant theorem

**Nothing in this exercise is to be proved.** The deliverable is the
*infrastructure and the network*: definitions, and theorem statements that
stay `sorry` (the file compiles with `sorry` warnings, and that is the
expected end state). Judge your work by whether someone else could later pick
any one `sorry` and prove it without redesigning anything.

**Math.** Let `M ⊆ B(H)` be a *-subalgebra with `1 ∈ M`. The commutant of
`S ⊆ B(H)` is `S' = {a | ∀ b ∈ S, a b = b a}` and `S'' = (S')'`.
The double commutant (von Neumann density) theorem says the following are
equivalent: (i) `M` is weakly closed; (ii) `M` is strongly closed;
(iii) `M'' = M`.

**Reference.** Hiai §1.2 (p. 2) states exactly this. The Kaplansky density
theorem (same page) is the natural next node of the network. Mathlib's
`VonNeumannAlgebra` takes (iii) as its *definition*
(`centralizer_centralizer'`) and lists (i)/(ii) ⇔ (iii) as an open TODO, so
the theorem is precisely the missing bridge between Mathlib and Hiai.

**Who might use this? (proposals, to be decided together)**
* *Finite-dimensional bridge.* `⊤ : VonNeumannAlgebra (EuclideanSpace ℂ d)`
  and its subalgebras: every unital *-subalgebra of `B(ℂ^d)` is closed in
  all topologies, so it satisfies (i)-(iii). This is a test target for the
  network.
* *Constructing von Neumann algebras.* Generated algebras, commutants and
  fixed points of a symmetry are most naturally shown to be von Neumann
  algebras via (i) or (ii), not (iii).
* *Haag duality and the notes above.* Every statement of the form `A = B'`
  lives on top of the commutant vocabulary chosen here.
* *Mathlib (secondary).* Closing the TODO in
  `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean`.

**The exercise: design the network.**
1. *Vocabulary.* Decide what objects the statements are about (a `Set`, a
   `StarSubalgebra`, a Mathlib `VonNeumannAlgebra`?), how to name (i)-(iii)
   (predicates? `IsClosed` on a topology type copy?), and whether to reuse
   `Set.centralizer` or introduce a commutant notation. Record the choice.
2. *The main statement.* State the theorem in the form you think users
   want. Try at least two packagings (e.g. three implications versus one
   equivalence) and keep the one that is easier to *use*.
3. *Decompose the hard implication.* The proof of (ii) ⇒ (iii) is not a
   single step. Without proving anything, write the intermediate
   statements it would need as separate declarations (each ending in
   `sorry`), and say which earlier declaration each one uses. Aim for pieces
   that are useful on their own, not just lemmas of one proof.
4. *Connect to what exists.* Add the statements linking the new notions
   to Mathlib's `VonNeumannAlgebra`, to Exercise 1, and to the
   finite-dimensional test target.
5. *Dependency map.* Put a short comment block above your declarations
   listing, for each, the declarations it depends on. Mark which `sorry`s
   look easy, medium or hard, and which would be a Mathlib-level project.
6. *Design notes.* Record the decisions of steps 1-4, and anything you
   would do differently if you had to redo the vocabulary.

**Hints** (open one at a time; these are about design, not proofs).
1. *Precedent.* `Set.centralizer`, `VonNeumannAlgebra.commutant` and
   `VonNeumannAlgebra.mem_commutant_iff` already exist; read how Mathlib
   states `centralizer_centralizer` for a structure before inventing
   notation. `List.TFAE` is Mathlib's standard packaging for "the following
   are equivalent".
2. *Where is the difficulty?* The math has two different mechanisms:
   an *elementary* one (commutants are weakly closed) and a *cyclic-subspace*
   one (the projection onto the closure of `M x` lies in `M'`). The second
   has to pass from one vector to finitely many through the amplification
   `H ⊕ ⋯ ⊕ H`. Ask which of these deserve their own named objects, and
   where they should live.
3. *What a strong neighbourhood is.*
   `PointwiseConvergenceCLM.hasBasis_nhds_zero` describes neighbourhoods by
   finite sets of vectors; "closure in the SOT" can be stated with it as an
   approximation criterion on finitely many vectors. Whether that criterion
   is a lemma or a definition is a design decision.
4. *Orthogonal projections.* `Submodule.starProjection` and
   `IsStarProjection` give the projection onto a closed subspace; note that
   it needs completeness of the subspace, hence a hypothesis on `H`.

**Lean skills practiced.** Choosing between predicate/structure/type-class
vocabularies; `List.TFAE`; writing statements as interface contracts;
tracking dependencies between declarations; leaving `sorry`s deliberately.
-/

section Exercise2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Your vocabulary and network here.

end Exercise2
