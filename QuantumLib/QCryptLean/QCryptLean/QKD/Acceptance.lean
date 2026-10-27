import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.ExitWeight
import QCryptLean.QKD.OutputLayout
import QCryptLean.QKD.Protocol
import QCryptLean.Quantum.Operators.Basic

/-! # Acceptance -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace BoundaryKeyLayout

variable {B : Boundary P} (L : BoundaryKeyLayout B)

/-- The diagonal mass of an output operator on the accepting complete exits. -/
def acceptWeight (M : Op B.space) : ℝ :=
  B.exitWeight (fun e => L.disposition e ≠ .abort) M

/-- The diagonal mass of an output operator on the aborting complete exits. -/
def abortWeight (M : Op B.space) : ℝ :=
  B.exitWeight (fun e => L.disposition e = .abort) M

/-- **Accepting and aborting exits partition the output trace.** -/
theorem acceptWeight_add_abortWeight (M : Op B.space) :
    L.acceptWeight M + L.abortWeight M = (Matrix.trace M).re := by
  rw [add_comm, acceptWeight, abortWeight]
  exact B.exitWeight_add_exitWeight_not _ M

/-- A positive semidefinite output has nonnegative acceptance weight. -/
theorem acceptWeight_nonneg {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ L.acceptWeight M :=
  B.exitWeight_nonneg _ hM

/-- A positive semidefinite output has nonnegative abort weight. -/
theorem abortWeight_nonneg {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ L.abortWeight M :=
  B.exitWeight_nonneg _ hM

/-- A layout that aborts at every exit has zero acceptance weight. -/
theorem acceptWeight_eq_zero_of_forall_abort (h : ∀ e, L.disposition e = .abort)
    (M : Op B.space) : L.acceptWeight M = 0 := by
  rw [acceptWeight, B.exitWeight_congr (E' := fun _ => False) (fun e => by simp [h e]) M,
    B.exitWeight_false M]

end BoundaryKeyLayout

end LOCC

namespace QKD

open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Protocol

variable [SystemPresentation P]

variable (A : Protocol P)

/-- **The acceptance probability of a protocol on an input state**: the diagonal mass of its real
output on the accepting complete public exits. -/
def acceptProbability (ρ : Op A.start.total) : ℝ :=
  A.layout.toBoundaryKeyLayout.acceptWeight (A.real ρ)

/-- **The abort probability of a protocol on an input state**: the diagonal mass of its real output
on the aborting complete public exits.  On the honest noisy channel this is the robustness of
Portmann--Renner, arXiv:2102.00021, `qkd.tex:845`--`:850`. -/
def abortProbability (ρ : Op A.start.total) : ℝ :=
  A.layout.toBoundaryKeyLayout.abortWeight (A.real ρ)

/-- **Every run either accepts or aborts.**  The two probabilities add up to the trace of the input;
for a state they add up to one. -/
theorem acceptProbability_add_abortProbability (ρ : Op A.start.total) :
    A.acceptProbability ρ + A.abortProbability ρ = (Matrix.trace ρ).re := by
  rw [acceptProbability, abortProbability, BoundaryKeyLayout.acceptWeight_add_abortWeight, real,
    Program.trace_denote]

/-- On a unit-trace input the abort probability is one minus the acceptance probability. -/
theorem abortProbability_eq_one_sub (ρ : Op A.start.total) (hρ : Matrix.trace ρ = 1) :
    A.abortProbability ρ = 1 - A.acceptProbability ρ := by
  have h := A.acceptProbability_add_abortProbability ρ
  rw [hρ, Complex.one_re] at h
  linarith

/-- The acceptance probability of a positive semidefinite input is nonnegative. -/
theorem acceptProbability_nonneg {ρ : Op A.start.total} (hρ : ρ.PosSemidef) :
    0 ≤ A.acceptProbability ρ :=
  BoundaryKeyLayout.acceptWeight_nonneg _ (A.program.posSemidef_denote hρ)

/-- The abort probability of a positive semidefinite input is nonnegative. -/
theorem abortProbability_nonneg {ρ : Op A.start.total} (hρ : ρ.PosSemidef) :
    0 ≤ A.abortProbability ρ :=
  BoundaryKeyLayout.abortWeight_nonneg _ (A.program.posSemidef_denote hρ)

end Protocol

end QKD
