import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.MultipartiteSystem

/-! # Direct Sum -/


open scoped Matrix BigOperators

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

variable {Y : Type} [DecidableEq Y]

namespace Boundary


/-- The output space of a terminal boundary is canonically its terminal quantum register.

This equivalence removes the unique trivial public-exit coordinate of a completed finite-round
LOCC branch as represented in Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section II. -/
def leafSpaceEquiv (R : MultipartiteSystem P) : (Boundary.leaf R).space ≃ R.total where
  toFun x := x.2
  invFun x := ⟨(), x⟩
  left_inv x := by
    rcases x with ⟨⟨⟩, x⟩
    rfl
  right_inv _ := rfl

/-- Transporting a terminal output transports its joint-register coordinate. -/
@[simp] theorem cast_leafSpaceEquiv_symm {R S : MultipartiteSystem P} (h : R = S)
    (q : R.total) :
    cast (congrArg (fun T => (Boundary.leaf T).space) h) ((leafSpaceEquiv R).symm q) =
      (leafSpaceEquiv S).symm (cast (congrArg MultipartiteSystem.total h) q) := by
  cases h
  rfl

/-- Reading the register of a transported terminal output commutes with transport. -/
@[simp] theorem leafSpaceEquiv_cast {R S : MultipartiteSystem P} (h : R = S)
    (q : (Boundary.leaf R).space) :
    leafSpaceEquiv S (cast (congrArg (fun T => (Boundary.leaf T).space) h) q) =
      cast (congrArg MultipartiteSystem.total h) (leafSpaceEquiv R q) := by
  cases h
  rfl

/-- The output space of an announced boundary is canonically the sigma of the output spaces of
its continuations.

This is the coordinate form of the outcome-indexed continuation after a public instrument in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
def publicSpaceEquiv [Fintype Y]
    (next : Y → Boundary P) :
    (Boundary.announce Y next).space ≃ Σ y : Y, (next y).space :=
  Equiv.sigmaAssoc fun y e => ((next y).system e).total

/-- `publicSpaceEquiv` only reassociates the public outcome, continuation exit, and quantum
coordinate. -/
@[simp] theorem publicSpaceEquiv_apply [Fintype Y]
    (next : Y → Boundary P) (x : (Boundary.announce Y next).space) :
    publicSpaceEquiv next x = ⟨x.1.1, ⟨x.1.2, x.2⟩⟩ :=
  rfl

end Boundary


/-- The canonical Kraus matrix including the fibre `F y` into the sigma-indexed ambient space.

Its only nonzero entry in column `q` is the coordinate `⟨y, q⟩`. These inclusions implement the
classical blocks selected by public outcomes in the finite-round LOCC tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
def sigmaInclKraus
    (F : Y → Type) [∀ y, DecidableEq (F y)] (y : Y) :
    Matrix (Σ z : Y, F z) (F y) ℂ :=
  Matrix.of fun p q => if p = ⟨y, q⟩ then 1 else 0

/-- Coordinate formula for the inclusion of a sigma fibre. -/
@[simp] theorem sigmaInclKraus_apply
    (F : Y → Type) [∀ y, DecidableEq (F y)]
    (y : Y) (p : Σ z : Y, F z) (q : F y) :
    sigmaInclKraus F y p q = if p = ⟨y, q⟩ then 1 else 0 :=
  rfl

/-- Exact support of a column of the sigma-fibre inclusion. -/
theorem sigmaInclKraus_apply_ne_zero_iff
    (F : Y → Type) [∀ y, DecidableEq (F y)]
    (y : Y) (p : Σ z : Y, F z) (q : F y) :
    sigmaInclKraus F y p q ≠ 0 ↔ p = ⟨y, q⟩ := by
  simp [sigmaInclKraus]

/-- A row outside the selected public fibre is zero. -/
theorem sigmaInclKraus_apply_eq_zero_of_fst_ne
    (F : Y → Type) [∀ y, DecidableEq (F y)]
    {y : Y} {p : Σ z : Y, F z} (h : p.1 ≠ y) (q : F y) :
    sigmaInclKraus F y p q = 0 := by
  simp only [sigmaInclKraus_apply, ite_eq_right_iff]
  intro hp
  exact (h (congrArg Sigma.fst hp)).elim

/-- Each sigma-fibre inclusion is an isometry.

This is the Gram-matrix identity for the classical block inclusion associated to an announced
outcome in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
@[simp] theorem sigmaInclKraus_conjTranspose_mul_self
    [Fintype Y]
    (F : Y → Type) [∀ y, Fintype (F y)] [∀ y, DecidableEq (F y)] (y : Y) :
    (sigmaInclKraus F y)ᴴ * sigmaInclKraus F y = 1 := by
  ext q r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (⟨y, q⟩ : Σ z : Y, F z)]
  · simp [sigmaInclKraus, Matrix.one_apply]
  · intro p _ hp
    simp [sigmaInclKraus, hp]
  · simp

/-- Inclusions of distinct sigma fibres have zero mixed Gram matrix.

The rectangular zero matrix is the type-correct orthogonality statement when the two fibres have
different index types. -/
theorem sigmaInclKraus_conjTranspose_mul_of_ne
    [Fintype Y]
    (F : Y → Type) [∀ y, Fintype (F y)] [∀ y, DecidableEq (F y)]
    {y z : Y} (h : y ≠ z) :
    (sigmaInclKraus F y)ᴴ * sigmaInclKraus F z = 0 := by
  ext q r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p = ⟨y, q⟩
  · subst p
    simp [sigmaInclKraus, h]
  · simp [sigmaInclKraus, hp]

/-- The inclusions of all sigma fibres resolve the identity on the ambient sigma type. -/
@[simp] theorem sum_sigmaInclKraus_mul_conjTranspose
    [Fintype Y]
    (F : Y → Type) [∀ y, Fintype (F y)] [∀ y, DecidableEq (F y)] :
    ∑ y : Y, sigmaInclKraus F y * (sigmaInclKraus F y)ᴴ = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · simp [sigmaInclKraus, Matrix.one_apply, eq_comm]
    · intro r _ hr
      have hp : p ≠ ⟨p.1, r⟩ := by
        intro hp
        apply hr
        exact eq_of_heq (Sigma.mk.inj_iff.mp ((Sigma.eta p).trans hp)).2.symm
      rw [sigmaInclKraus_apply, ite_eq_right hp, zero_mul]
    · simp
  · intro y _ hy
    apply Finset.sum_eq_zero
    intro r _
    have hp : p ≠ ⟨y, r⟩ := by
      intro hp
      exact hy (congrArg Sigma.fst hp).symm
    rw [sigmaInclKraus_apply, ite_eq_right hp, zero_mul]
  · simp

namespace Boundary

variable [Fintype Y]


/-- The inclusion of one public continuation space into the output space of an announced
boundary. -/
noncomputable def publicInclKraus
    (next : Y → Boundary P) (y : Y) :
    Matrix (Boundary.announce Y next).space (next y).space ℂ :=
  (sigmaInclKraus (fun z => (next z).space) y).submatrix (publicSpaceEquiv next) id

/-- Coordinate formula for the public-continuation inclusion. -/
@[simp] theorem publicInclKraus_apply
    (next : Y → Boundary P) (y : Y)
    (p : (Boundary.announce Y next).space) (q : (next y).space) :
    publicInclKraus next y p q =
      if publicSpaceEquiv next p = ⟨y, q⟩ then 1 else 0 :=
  rfl

/-- Exact support of a column of a public-continuation inclusion. -/
theorem publicInclKraus_apply_ne_zero_iff
    (next : Y → Boundary P) (y : Y)
    (p : (Boundary.announce Y next).space) (q : (next y).space) :
    publicInclKraus next y p q ≠ 0 ↔ publicSpaceEquiv next p = ⟨y, q⟩ := by
  simp [publicInclKraus]

/-- Every row outside the selected public-continuation block is zero. -/
theorem publicInclKraus_apply_eq_zero_of_fst_ne
    (next : Y → Boundary P) {y : Y} {p : (Boundary.announce Y next).space}
    (h : (publicSpaceEquiv next p).1 ≠ y) (q : (next y).space) :
    publicInclKraus next y p q = 0 := by
  apply sigmaInclKraus_apply_eq_zero_of_fst_ne (fun z => (next z).space) h q

/-- A public-continuation inclusion is an isometry. -/
@[simp] theorem publicInclKraus_conjTranspose_mul_self
    (next : Y → Boundary P) (y : Y) :
    (publicInclKraus next y)ᴴ * publicInclKraus next y = 1 := by
  rw [publicInclKraus, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, sigmaInclKraus_conjTranspose_mul_self]
  rfl

/-- Distinct public-continuation inclusions have zero mixed Gram matrix. -/
theorem publicInclKraus_conjTranspose_mul_of_ne
    (next : Y → Boundary P) {y z : Y} (h : y ≠ z) :
    (publicInclKraus next y)ᴴ * publicInclKraus next z = 0 := by
  rw [publicInclKraus, publicInclKraus, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, sigmaInclKraus_conjTranspose_mul_of_ne _ h]
  rfl

/-- The public-continuation inclusions resolve the identity on an announced boundary's output
space.

This is the outer public-outcome block resolution for a finite-round LOCC instrument tree in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
@[simp] theorem sum_publicInclKraus_mul_conjTranspose
    (next : Y → Boundary P) :
    ∑ y : Y, publicInclKraus next y * (publicInclKraus next y)ᴴ = 1 := by
  have hmul (y : Y) :
      publicInclKraus next y * (publicInclKraus next y)ᴴ =
        (sigmaInclKraus (fun z => (next z).space) y *
          (sigmaInclKraus (fun z => (next z).space) y)ᴴ).submatrix
            (publicSpaceEquiv next) (publicSpaceEquiv next) := by
    ext p q
    simp [publicInclKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]
  ext p q
  simp_rw [hmul]
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  change (∑ y : Y,
      (sigmaInclKraus (fun z => (next z).space) y *
        (sigmaInclKraus (fun z => (next z).space) y)ᴴ)
          (publicSpaceEquiv next p) (publicSpaceEquiv next q)) = _
  rw [← Matrix.sum_apply, sum_sigmaInclKraus_mul_conjTranspose]
  by_cases hpq : p = q
  · subst q
    rw [Matrix.one_apply, Matrix.one_apply, ite_eq_left rfl, ite_eq_left rfl]
  · have heq : publicSpaceEquiv next p ≠ publicSpaceEquiv next q :=
      fun h => hpq ((publicSpaceEquiv next).injective h)
    rw [Matrix.one_apply, Matrix.one_apply, ite_eq_right heq, ite_eq_right hpq]


/-- The Kraus matrix including the quantum register at one complete exit into the boundary's
classical-quantum output space.

The exit fixes the complete string of public outcomes in the finite-round LOCC tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II; this matrix includes the
corresponding final quantum register as that single classical block. -/
noncomputable def exitKraus (B : Boundary P) (e : B.Exit) :
    Matrix B.space (B.system e).total ℂ :=
  sigmaInclKraus (fun x => (B.system x).total) e

/-- Coordinate formula for a complete-exit inclusion. -/
@[simp] theorem exitKraus_apply (B : Boundary P) (e : B.Exit)
    (p : B.space) (q : (B.system e).total) :
    exitKraus B e p q = if p = ⟨e, q⟩ then 1 else 0 :=
  rfl

/-- Exact support of a column of a complete-exit inclusion. -/
theorem exitKraus_apply_ne_zero_iff (B : Boundary P) (e : B.Exit)
    (p : B.space) (q : (B.system e).total) :
    exitKraus B e p q ≠ 0 ↔ p = ⟨e, q⟩ := by
  simp [exitKraus]

/-- The inclusion of a complete public exit is an isometry. -/
@[simp] theorem exitKraus_conjTranspose_mul_self (B : Boundary P) (e : B.Exit) :
    (exitKraus B e)ᴴ * exitKraus B e = 1 := by
  exact sigmaInclKraus_conjTranspose_mul_self (fun x => (B.system x).total) e

/-- The complete-exit inclusions resolve the identity on the boundary output space.

This is the finite classical-block resolution associated to the complete public histories of the
LOCC tree in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
@[simp] theorem sum_exitKraus_mul_conjTranspose (B : Boundary P) :
    ∑ e : B.Exit, exitKraus B e * (exitKraus B e)ᴴ = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · simp [exitKraus, sigmaInclKraus, Matrix.one_apply, eq_comm]
    · intro r _ hr
      have hp : p ≠ ⟨p.1, r⟩ := by
        intro hp
        apply hr
        exact eq_of_heq (Sigma.mk.inj_iff.mp ((Sigma.eta p).trans hp)).2.symm
      rw [exitKraus_apply, ite_eq_right hp, zero_mul]
    · simp
  · intro e _ he
    apply Finset.sum_eq_zero
    intro r _
    have hp : p ≠ ⟨e, r⟩ := by
      intro hp
      exact he (congrArg Sigma.fst hp).symm
    rw [exitKraus_apply, ite_eq_right hp, zero_mul]
  · simp

/-- At an announced boundary, inclusion of a complete exit factors through the public-outcome
block and then through the selected continuation's exit block.

This is the matrix form of outcome-indexed continuation in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. -/
theorem exitKraus_announce
    (next : Y → Boundary P) (y : Y) (e : (next y).Exit) :
    exitKraus (Boundary.announce Y next) ⟨y, e⟩ =
      publicInclKraus next y * exitKraus (next y) e := by
  apply Matrix.ext
  intro (p : (Boundary.announce Y next).space) (q : ((next y).system e).total)
  change exitKraus (Boundary.announce Y next) ⟨y, e⟩ p q =
    ∑ r : (next y).space, publicInclKraus next y p r * exitKraus (next y) e r q
  rw [Finset.sum_eq_single (⟨e, q⟩ : (next y).space)]
  · change (if p = ⟨⟨y, e⟩, q⟩ then (1 : ℂ) else 0) = _
    simp only [exitKraus_apply, publicInclKraus_apply, ite_eq_left, mul_one]
    exact if_congr (publicSpaceEquiv next).injective.eq_iff.symm rfl rfl
  · intro r _ hr
    simp [exitKraus, publicInclKraus, sigmaInclKraus, hr]
  · simp

/-- Extracting an announced boundary's selected public block and then its selected complete exit
is the continuation's complete-exit extraction. -/
@[simp] theorem exitKraus_announce_conjTranspose_mul_publicInclKraus
    (next : Y → Boundary P) (y : Y) (e : (next y).Exit) :
    (exitKraus (Boundary.announce Y next) ⟨y, e⟩)ᴴ * publicInclKraus next y =
      (exitKraus (next y) e)ᴴ := by
  rw [exitKraus_announce]
  change (publicInclKraus next y * exitKraus (next y) e)ᴴ * publicInclKraus next y = _
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    publicInclKraus_conjTranspose_mul_self, Matrix.mul_one]

/-- Extracting a complete exit through a distinct outer public block gives the rectangular zero
matrix. -/
theorem exitKraus_announce_conjTranspose_mul_publicInclKraus_of_ne
    (next : Y → Boundary P) {y z : Y} (e : (next y).Exit) (h : y ≠ z) :
    (exitKraus (Boundary.announce Y next) ⟨y, e⟩)ᴴ * publicInclKraus next z = 0 := by
  rw [exitKraus_announce]
  change (publicInclKraus next y * exitKraus (next y) e)ᴴ * publicInclKraus next z = _
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    publicInclKraus_conjTranspose_mul_of_ne next h, Matrix.mul_zero]
  rfl

end Boundary
end LOCC
