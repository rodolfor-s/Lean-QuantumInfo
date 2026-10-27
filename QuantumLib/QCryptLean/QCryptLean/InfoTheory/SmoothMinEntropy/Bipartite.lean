import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-!
# Guarded bipartite min- and max-entropies

The min-side reference supremum keeps its feasibility guard; the max-side
supremum ranges over normalized references with strictly positive fidelity.
All logarithms are base two. The definitions use explicit real quadratic-form
comparison and fidelity, without changing ambient matrix norm or order instances.
-/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Metrics
open scoped Kronecker ComplexOrder

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Feasibility for the max-relative-entropy scale of arbitrary operators. -/
def IsDmaxFeasible (ρ σ : Op A) (t : ℝ) : Prop := 0 ≤ t ∧ OpLe ρ ((t : ℂ) • σ)

/-- The real infimum of the feasible domination scales. -/
def dmaxScale (ρ σ : Op A) : ℝ := sInf (Set.ofPred (IsDmaxFeasible ρ σ))

/-- Existence of a finite domination scale, retained as a reference-domain guard. -/
def HasDmaxScale (ρ σ : Op A) : Prop := ∃ t, IsDmaxFeasible ρ σ t

/-- The feasible scale set is bounded below. -/
theorem bddBelow_setOf_isDmaxFeasible (ρ σ : Op A) :
    BddBelow (Set.ofPred (IsDmaxFeasible ρ σ)) := ⟨0, fun _ ht => ht.1⟩

/-- Every feasible scale bounds the real optimum. -/
theorem dmaxScale_le_of_isDmaxFeasible (ρ σ : Op A) {t : ℝ}
    (ht : IsDmaxFeasible ρ σ t) : dmaxScale ρ σ ≤ t :=
  csInf_le (bddBelow_setOf_isDmaxFeasible ρ σ) ht

/-- Bipartite fixed-reference min-entropy in bits, with its real zero sentinel. -/
def bipartiteMinEntropyReal [DecidableEq A]
    (ρ : SubDensityOp (A × B)) (σ : SubDensityOp B) : ℝ :=
  -Real.log (dmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp)) / Real.log 2

/-- The bipartite min-side supremum excludes infeasible reference operators. -/
def bipartiteMinEntropyOptReal [DecidableEq A] (ρ : SubDensityOp (A × B)) : ℝ :=
  sSup {h | ∃ σ : SubDensityOp B,
    HasDmaxScale ρ.toOp ((1 : Op A) ⊗ₖ σ.toOp) ∧ h = bipartiteMinEntropyReal ρ σ}

/-- The identity on the first register tensored with a normalized reference. -/
def bipartiteMaxReferenceOp [DecidableEq A] (σ : DensityOp B) : PosSemidefOp (A × B) :=
  ⟨(1 : Op A) ⊗ₖ σ.toOp, Matrix.PosSemidef.one.kronecker σ.posSemidef⟩

/-- Fixed-reference max-entropy in bits, restricted to positive fidelity. -/
def bipartiteMaxEntropyReal [DecidableEq A] (ρ : SubDensityOp (A × B)) (σ : DensityOp B)
    (_hF : 0 < fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp σ)) : ℝ :=
  Real.log (fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp σ) ^ 2) / Real.log 2

/-- Max-entropy of a nonzero state optimized over normalized, positive-overlap references. -/
def bipartiteMaxEntropyOptReal [DecidableEq A] (ρ : SubDensityOp (A × B))
    (_hρ : ρ.toOp ≠ 0) : ℝ :=
  sSup {h | ∃ (σ : DensityOp B)
    (hF : 0 < fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp σ)),
    h = bipartiteMaxEntropyReal ρ σ hF}

/-- Smooth guarded bipartite min-entropy optimizes over the complete state ball. -/
def IsInSmoothBipartiteMinSet [DecidableEq A]
    (ε : ℝ) (ρ : SubDensityOp (A × B)) (h : ℝ) : Prop :=
  ∃ τ : SubDensityOp (A × B), purifiedDistance ρ τ ≤ ε ∧ h = bipartiteMinEntropyOptReal τ

/-- The real supremum of guarded optimized bipartite entropies over the purified-distance ball. -/
def smoothBipartiteMinEntropyOptReal [DecidableEq A]
    (ε : ℝ) (ρ : SubDensityOp (A × B)) : ℝ :=
  sSup (Set.ofPred (IsInSmoothBipartiteMinSet ε ρ))

/-- The center witnesses nonemptiness for every nonnegative smoothing radius. -/
theorem smoothBipartiteMinSet_nonempty [DecidableEq A] {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : SubDensityOp (A × B)) : (Set.ofPred (IsInSmoothBipartiteMinSet ε ρ)).Nonempty :=
  ⟨bipartiteMinEntropyOptReal ρ, ρ, by simpa only [purifiedDistance_self] using hε, rfl⟩

/-- A ball member bounds the smooth supremum when the real domain is bounded above. -/
theorem le_smoothBipartiteMinEntropyOptReal_of_mem_ball [DecidableEq A]
    (ε : ℝ) (ρ τ : SubDensityOp (A × B))
    (hbdd : BddAbove (Set.ofPred (IsInSmoothBipartiteMinSet ε ρ)))
    (hτ : purifiedDistance ρ τ ≤ ε) :
    bipartiteMinEntropyOptReal τ ≤ smoothBipartiteMinEntropyOptReal ε ρ :=
  le_csSup hbdd ⟨τ, hτ, rfl⟩

/-- Radius monotonicity retains the boundedness condition needed for real suprema. -/
theorem smoothBipartiteMinEntropyOptReal_mono_eps [DecidableEq A]
    {ε δ : ℝ} (hε : 0 ≤ ε) (h : ε ≤ δ) (ρ : SubDensityOp (A × B))
    (hbdd : BddAbove (Set.ofPred (IsInSmoothBipartiteMinSet δ ρ))) :
    smoothBipartiteMinEntropyOptReal ε ρ ≤ smoothBipartiteMinEntropyOptReal δ ρ := by
  apply csSup_le_csSup hbdd (smoothBipartiteMinSet_nonempty hε ρ)
  rintro v ⟨τ, ht, hv⟩
  exact ⟨τ, ht.trans h, hv⟩

end InfoTheory.SmoothMinEntropy
