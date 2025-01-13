import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution
import QuantumInfo.Finite.Braket

import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `MEnsemble` and `PEnsemble`: Ensemble of mixed and pure states, respectively
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

/-- A mixed state as a PSD matrix with trace 1.-/
structure MState (d : Type*) [Fintype d] where
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

namespace MState

variable {d d₁ d₂ d₃ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

@[ext]
theorem ext {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rwa [MState.mk.injEq]

/-- The map from mixed states to their matrices is injective -/
theorem toMat_inj : (MState.m (d := d)).Injective :=
  fun _ _ ↦ ext

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex : Convex ℝ (Set.range (MState.m (d := d))) := by
  simp only [Convex, Set.mem_range, StarConvex,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro x y a b ha hb hab
  replace ha : 0 ≤ (a : ℂ) := by norm_cast
  replace hb : 0 ≤ (b : ℂ) := by norm_cast
  replace hab : a + b = (1 : ℂ) := by norm_cast
  exact ⟨⟨_, x.pos.convex_cone y.pos ha hb, by simpa [x.tr, y.tr] using hab⟩, rfl⟩

instance instMixable : Mixable (Matrix d d ℂ) (MState d) where
  to_U := MState.m
  to_U_inj := ext
  mkT := fun h ↦ ⟨⟨_,
    Exists.casesOn h fun t ht => ht ▸ t.pos,
    Exists.casesOn h fun t ht => ht ▸ t.tr⟩, rfl⟩
  convex := convex d

--An MState is a witness that d is nonempty.
instance nonempty (ρ : MState d) : Nonempty d := by
  by_contra h
  simpa [not_nonempty_iff.mp h] using ρ.tr

theorem PosSemidef_outer_self_conj (v : d → ℂ) : Matrix.PosSemidef (Matrix.vecMulVec v (conj v)) := by
  constructor
  · ext
    simp [Matrix.vecMulVec_apply, mul_comm]
  · intro x
    simp_rw [Matrix.dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.dotProduct,
      Matrix.vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : d, (starRingEnd ℂ) (x i) * v i) * ∑ i : d, (starRingEnd ℂ) (v i) * x i
    have : (∑ i : d, (starRingEnd ℂ) (x i) * v i) =
        (∑ i : d, (starRingEnd ℂ) ((starRingEnd ℂ) (v i) * x i)) := by
          simp only [mul_comm ((starRingEnd ℂ) (x _)) (v _), map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [this, ← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.zero_le_real, ← Complex.sq_abs]
    exact sq_nonneg _

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  m := Matrix.vecMulVec ψ (ψ : Bra d)
  pos := PosSemidef_outer_self_conj ψ
  tr := by
    have h₁ : ∀x, ψ x * conj (ψ x) = Complex.normSq (ψ x) := fun x ↦ by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Bra.eq_conj, h₁]
    have h₂ := congrArg Complex.ofReal ψ.normalized
    simpa using h₂

@[simp]
theorem pure_of (ψ : Ket d) : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always between zero and one. -/
def purity (ρ : MState d) : Prob :=
  ⟨RCLike.re (ρ.m * ρ.m).trace, ⟨by
    suffices 0 ≤ Matrix.trace (ρ.m * ρ.m) by
      exact (RCLike.nonneg_iff.mp this).1
    nth_rewrite 1 [← ρ.pos.1]
    exact ρ.m.posSemidef_conjTranspose_mul_self.trace_nonneg,
      by
    nth_rewrite 1 [← ρ.pos.1]
    convert ρ.pos.inner_le_mul_trace ρ.pos using 1
    simp [ρ.tr]
    ⟩⟩

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : Distribution d :=
  Distribution.mk'
    (fun i ↦ ρ.Hermitian.eigenvalues i) --The values are the eigenvalues
    (fun i ↦ ρ.pos.eigenvalues_nonneg i) --The values are all nonnegative
    (by --The values sum to 1
      have h := congrArg Complex.re (ρ.Hermitian.sum_eigenvalues_eq_trace)
      simp only [ρ.tr, RCLike.ofReal_sum, Complex.re_sum, Complex.one_re] at h
      rw [← h]
      rfl)

/-- The specturm of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant (ψ : Ket d) :
    ∃ i, (pure ψ).spectrum = Distribution.constant i := by
  let ρ := pure ψ
  let ρ_linMap := Matrix.toEuclideanLin ρ.m
  -- Prove 1 is in the spectrum of pure ψ by exhibiting an eigenvector with value 1.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    simp [spectrum, Distribution.mk']
    have hEig : ∃i, (pure ψ).Hermitian.eigenvalues i = 1 := by
      -- Prove ψ is an eigenvector of ρ = pure ψ
      have hv : ρ.m *ᵥ ψ = ψ := by
        ext
        simp_rw [ρ, pure, Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct, Bra.apply',
        Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
      let U : Matrix.unitaryGroup d ℂ := star ρ.Hermitian.eigenvectorUnitary -- Diagonalizing unitary of ρ
      let w : d → ℂ := U *ᵥ ψ
      -- Prove w = U ψ is an eigenvector of the diagonalized matrix of ρ = pure ψ
      have hDiag : Matrix.diagonal (RCLike.ofReal ∘ ρ.Hermitian.eigenvalues) *ᵥ w = w := by
        simp_rw [←Matrix.IsHermitian.star_mul_self_mul_eq_diagonal, eq_comm,
        ←Matrix.mulVec_mulVec, w, U, Matrix.mulVec_mulVec] -- Uses spectral theorem
        simp_all
        rw [←Matrix.mulVec_mulVec, hv]
      -- Prove w = U ψ is nonzero by contradiction
      have hwNonZero : ∃j, w j ≠ 0 := by
        by_contra hwZero
        simp at hwZero
        rw [←funext_iff] at hwZero
        -- If w is zero, then ψ is zero, since U is invertible
        have hψZero : ∀x, ψ x = 0 := by
          apply congr_fun
          -- Prove U is invertible
          have hUdetNonZero : (U : Matrix d d ℂ).det ≠ 0 := by
            by_contra hDetZero
            obtain ⟨u, huUni⟩ := U
            have h0uni: 0 ∈ unitary ℂ := by
              rw [←hDetZero]
              simp
              exact Matrix.det_of_mem_unitary huUni
            rw [unitary.mem_iff] at h0uni
            simp_all
          exact Matrix.eq_zero_of_mulVec_eq_zero hUdetNonZero hwZero
        -- Reach an contradiction that ψ has norm 0
        have hψn := Ket.normalized ψ
        have hnormZero : ∀ x : d, Complex.normSq (ψ x) = 0 := fun x => by
          rw [hψZero x, Complex.normSq_zero]
        have hsumZero : ∑ x : d, Complex.normSq (ψ x) = 0 := by
          apply Finset.sum_eq_zero
          intros x _
          exact hnormZero x
        simp_all
      obtain ⟨j, hwNonZero'⟩ := hwNonZero
      have hDiagj := congr_fun hDiag j
      rw [Matrix.mulVec_diagonal, mul_eq_right₀ hwNonZero'] at hDiagj
      use j
      simp_all
    obtain ⟨i, hEig'⟩ := hEig
    use i
    ext
    exact hEig'
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact Distribution.constant_of_exists_one hi

/-- If the specturm of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (ρ : MState d) (h : ∃ i, ρ.spectrum = Distribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.Hermitian.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simp [spectrum, Distribution.constant, Distribution.mk'] at h'
    rw [Subtype.mk.injEq] at h'
    have h'x := congr_fun h' x
    rw [if_congr (Eq.comm) (Eq.refl 1) (Eq.refl 0)]
    rw [Prob.eq_iff, Prob.toReal_mk] at h'x
    rw [h'x]
    split_ifs
    case pos => rfl
    case neg => rfl
  -- Choose the eigenvector v of ρ with eigenvalue 1 to make ψ
  let ⟨u, huUni⟩ := ρ.Hermitian.eigenvectorUnitary -- Diagonalizing unitary of ρ
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ ρ.Hermitian.eigenvalues) -- Diagonal matrix of ρ
  let v : EuclideanSpace ℂ d := ρ.Hermitian.eigenvectorBasis i
  -- Prove v is normalized
  have hUvNorm : ∑ x, ‖v x‖^2 = 1 := by
    have hinnerv : inner v v = (1:ℂ) := by
      have := OrthonormalBasis.orthonormal ρ.Hermitian.eigenvectorBasis
      rw [orthonormal_iff_ite] at this
      specialize this i i
      simp only [if_true] at this
      exact this
    simp_all [Complex.conj_mul']
    rw [←Fintype.sum_equiv (Equiv.refl d) _ (fun x => (Complex.ofReal (Complex.abs (v x))) ^ 2) (fun x => Complex.ofReal_pow (Complex.abs (v x)) 2)] at hinnerv
    rw [←Complex.ofReal_sum Finset.univ (fun x => (Complex.abs (v x)) ^ 2), Complex.ofReal_eq_one] at hinnerv
    exact hinnerv
  let ψ : Ket d := ⟨v, hUvNorm⟩ -- Construct ψ
  use ψ
  ext j k
  simp
  -- Use spectral theorem to prove that ρ = pure ψ
  rw [Matrix.IsHermitian.spectral_theorem ρ.Hermitian, Matrix.mul_apply]
  simp [ψ, Ket.apply, v, hEig]
  have hsum : ∀ x ∈ Finset.univ, x ∉ ({i} : Finset d) → (ρ.Hermitian.eigenvectorBasis x j) * (↑(if x = i then 1 else 0) : ℝ) * (starRingEnd ℂ) (ρ.Hermitian.eigenvectorBasis x k) = 0 := by
    intros x hx hxnoti
    rw [Finset.mem_singleton] at hxnoti
    rw [eq_false hxnoti, if_false, Complex.ofReal_zero]
    ring
  simp_rw [←Finset.sum_subset (Finset.subset_univ {i}) hsum, Finset.sum_singleton, reduceIte, Complex.ofReal_one, mul_one]

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = Distribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

theorem pure_iff_purity_one (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --disttibution is constant iff pure
  sorry

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  m := ρ₁.m ⊗ₖ ρ₂.m
  pos := ρ₁.pos.PosSemidef_kronecker ρ₂.pos
  tr := by simpa [ρ₁.tr, ρ₂.tr] using Matrix.trace_kronecker ρ₁.m ρ₂.m

notation ρL "⊗" ρR => prod ρL ρR

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ ψ₂) = (pure ψ₁) ⊗ (pure ψ₂) := by
  ext
  simp only [pure, Ket.prod, Ket.apply, Matrix.vecMulVec_apply, Bra.eq_conj, map_mul, prod,
    Matrix.kroneckerMap_apply]
  ring

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : Distribution d) : MState d where
  m := Matrix.diagonal (fun x ↦ dist x)
  pos := by simp [Matrix.posSemidef_diagonal_iff]
  tr := by
    simp [Matrix.trace_diagonal]
    have h₃ := dist.2
    norm_cast

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d := ofClassical Distribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ instNonemptyOfInhabited
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ instNonemptyOfInhabited : MState d).tr
    simp [Matrix.trace, Unique.eq_default] at h₁ h₂ ⊢
    exact h₁.trans h₂.symm

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

section ensemble

/-- A mixed-state ensemble is a random variable valued in `MState d`. That is,
a collection of mixed states `var : α → MState d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev MEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := Distribution.RandVar α (MState d)

/-- A pure-state ensemble is a random variable valued in `Ket d`. That is,
a collection of pure states `var : α → Ket d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev PEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := Distribution.RandVar α (Ket d)

variable {α β: Type*} [Fintype α] [Fintype β]

/-- Alias for `Distribution.var` for mixed-state ensembles. -/
abbrev MEnsemble.states [Fintype α] : MEnsemble d α → (α → MState d) := Distribution.RandVar.var

/-- Alias for `Distribution.var` for pure-state ensembles. -/
abbrev PEnsemble.states [Fintype α] : PEnsemble d α → (α → Ket d) := Distribution.RandVar.var

namespace Ensemble

/-- A pure-state ensemble is a mixed-state ensemble if all kets are interpreted as mixed states. -/
@[coe] def toMEnsemble : PEnsemble d α → MEnsemble d α := Functor.map pure

instance : Coe (PEnsemble d α) (MEnsemble d α) := ⟨toMEnsemble⟩

@[simp]
theorem toMEnsemble_mk : (toMEnsemble ⟨ps, distr⟩ : MEnsemble d α) = ⟨pure ∘ ps, distr⟩ :=
  rfl

/-- A mixed-state ensemble comes from a pure-state ensemble if and only if all states are pure. -/
theorem coe_PEnsemble_iff_pure_states (me : MEnsemble d α): (∃ pe : PEnsemble d α, ↑pe = me) ↔ (∃ ψ : α → Ket d, me.states = pure ∘ ψ) := by
  constructor
  · intro ⟨pe, hpe⟩
    use pe.states
    ext1 i
    subst hpe
    rfl
  · intro ⟨ψ, hψ⟩
    use ⟨ψ, me.distr⟩
    simp only [toMEnsemble_mk]
    congr
    exact hψ.symm

/-- The resulting mixed state after mixing the states in an ensemble with their
respective probability weights. Note that, generically, a single mixed state has infinitely many
ensembles that mixes into it. -/
def mix (e : MEnsemble d α) : MState d := Distribution.exp_val e

@[simp]
theorem mix_of (e : MEnsemble d α) : (mix e).m = ∑ i, Prob.toReal (e.distr i) • (e.states i).m := by
  rfl

/-- Two mixed-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrMEnsemble (σ : α ≃ β) : MEnsemble d α ≃ MEnsemble d β := Distribution.congrRandVar σ

/-- Two pure-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrPEnsemble (σ : α ≃ β) : PEnsemble d α ≃ PEnsemble d β := Distribution.congrRandVar σ

/-- Equivalence of mixed-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrMEnsemble_eq_mix (σ : α ≃ β) (e : MEnsemble d α) : mix (congrMEnsemble σ e) = mix e :=
  Distribution.exp_val_congr_eq_exp_val σ e

/-- Equivalence of pure-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrPEnsemble_eq_mix (σ : α ≃ β) (e : PEnsemble d α) : mix ↑(congrPEnsemble σ e) = mix (↑e : MEnsemble d α) := by
  unfold toMEnsemble congrPEnsemble mix
  rw [Distribution.map_congr_eq_congr_map pure σ e]
  exact Distribution.exp_val_congr_eq_exp_val σ (pure <$> e)

/-- The average of a function `f : MState d → T`, where `T` is of `Mixable U T` instance, on a mixed-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (e : MEnsemble d α) : T :=
  Distribution.exp_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : MState d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def average_NNReal {d : Type _} [Fintype d] (f : MState d → NNReal) (e : MEnsemble d α) : NNReal :=
  ⟨average (NNReal.toReal ∘ f) e,
    Distribution.zero_le_exp_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of a function `f : Ket d → T`, where `T` is of `Mixable U T` instance, on a pure-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def pure_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (e : PEnsemble d α) : T :=
  Distribution.exp_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : Ket d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def pure_average_NNReal {d : Type _} [Fintype d] (f : Ket d → NNReal) (e : PEnsemble d α) : NNReal :=
  ⟨pure_average (NNReal.toReal ∘ f) e,
    Distribution.zero_le_exp_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of `f : MState d → T` on a coerced pure-state ensemble `↑e : MEnsemble d α`
is equal to averaging the restricted function over Kets `f ∘ pure : Ket d → T` on `e`. -/
theorem average_of_pure_ensemble {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T]
  (f : MState d → T) (e : PEnsemble d α) :
  average f (toMEnsemble e) = pure_average (f ∘ pure) e := by
  simp only [average, pure_average, toMEnsemble, comp_map]

/-- A pure-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal to `ψ`  -/
theorem mix_pEnsemble_pure_iff_pure {ψ : Ket d} {e : PEnsemble d α} :
  mix ↑e = pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = ψ := by
  sorry

/-- The average of `f : Ket d → T` on an ensemble that mixes to a pure state `ψ` is `f ψ` -/
theorem mix_pEnsemble_pure_average {ψ : Ket d} {e : PEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (hmix : mix ↑e = pure ψ) :
  pure_average f e = f ψ := by
  have hpure := mix_pEnsemble_pure_iff_pure.mp hmix
  simp only [pure_average, Functor.map, Distribution.exp_val]
  apply Mixable.to_U_inj
  rw [PEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply, smul_eq_mul, Mixable.mkT_instUniv]
  have h1 : ∀ i ∈ Finset.univ, (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.toReal_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = ψ := fun i hi hne0 ↦ by
    rw [←Prob.val_zero, ←Prob.toReal, Prob.ne_iff] at hne0
    exact hpure i hne0
  rw [←Finset.sum_smul, ←Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

/-- A mixed-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal to `pure ψ`  -/
theorem mix_mEnsemble_pure_iff_pure {ψ : Ket d} {e : MEnsemble d α} :
  mix e = pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = pure ψ := by
  sorry

/-- The average of `f : MState d → T` on an ensemble that mixes to a pure state `ψ` is `f (pure ψ)` -/
theorem mix_mEnsemble_pure_average {ψ : Ket d} {e : MEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (hmix : mix e = pure ψ) :
  average f e = f (pure ψ) := by
  have hpure := mix_mEnsemble_pure_iff_pure.mp hmix
  simp only [average, Functor.map, Distribution.exp_val]
  apply Mixable.to_U_inj
  rw [MEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply, smul_eq_mul, Mixable.mkT_instUniv]
  have h1 : ∀ i ∈ Finset.univ, (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = pure ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.toReal_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = pure ψ := fun i hi hne0 ↦ by
    rw [←Prob.val_zero, ←Prob.toReal, Prob.ne_iff] at hne0
    exact hpure i hne0
  rw [←Finset.sum_smul, ←Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

/-- The trivial mixed-state ensemble of `ρ` consists of copies of `rho`, with the `i`-th one having
probability 1. -/
def trivial_mEnsemble (ρ : MState d) (i : α) : MEnsemble d α := ⟨fun _ ↦ ρ, Distribution.constant i⟩

/-- The trivial mixed-state ensemble of `ρ` mixes to `ρ` -/
theorem trivial_mEnsemble_mix (ρ : MState d) : ∀ i : α, mix (trivial_mEnsemble ρ i) = ρ := fun i ↦by
  ext1
  simp only [trivial_mEnsemble, Distribution.constant, mix_of, DFunLike.coe, apply_ite,
    Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- The average of `f : MState d → T` on a trivial ensemble of `ρ` is `f ρ`-/
theorem trivial_mEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (ρ : MState d):
  ∀ i : α, average f (trivial_mEnsemble ρ i) = f ρ := fun i ↦ by
    simp only [average, Functor.map, Distribution.exp_val, trivial_mEnsemble]
    apply Mixable.to_U_inj
    simp only [Distribution.constant_eq, Function.comp_apply, Mixable.to_U_of_mkT, apply_ite,
      Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]

instance MEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (MEnsemble d α) where
  default := trivial_mEnsemble default default

/-- The trivial pure-state ensemble of `ψ` consists of copies of `ψ`, with the `i`-th one having
probability 1. -/
def trivial_pEnsemble (ψ : Ket d) (i : α) : PEnsemble d α := ⟨fun _ ↦ ψ, Distribution.constant i⟩

/-- The trivial pure-state ensemble of `ψ` mixes to `ψ` -/
theorem trivial_pEnsemble_mix (ψ : Ket d) : ∀ i : α, mix (trivial_pEnsemble ψ i) = pure ψ := fun i ↦ by
  ext1
  simp only [trivial_pEnsemble, Distribution.constant, toMEnsemble_mk, mix_of, DFunLike.coe,
    apply_ite, Prob.toReal_one, Prob.toReal_zero, MEnsemble.states, Function.comp_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The average of `f : Ket d → T` on a trivial ensemble of `ψ` is `f ψ`-/
theorem trivial_pEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (ψ : Ket d):
  ∀ i : α, pure_average f (trivial_pEnsemble ψ i) = f ψ := fun i ↦ by
    simp only [pure_average, Functor.map, Distribution.exp_val, trivial_pEnsemble]
    apply Mixable.to_U_inj
    simp only [Distribution.constant_eq, Function.comp_apply, Mixable.to_U_of_mkT, apply_ite,
      Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]

instance PEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (PEnsemble d α) where
  default := trivial_pEnsemble default default

/-- The spectral pure-state ensemble of `ρ`. The states are its eigenvectors, and the probabilities, eigenvalues. -/
def spectral_ensemble (ρ : MState d) : PEnsemble d d :=
  { var := fun i ↦
    { vec := ρ.Hermitian.eigenvectorBasis i
      normalized' := by
        rw [←one_pow 2, ←ρ.Hermitian.eigenvectorBasis.orthonormal.1 i]
        have hnonneg : 0 ≤ ∑ x : d, Complex.abs (ρ.Hermitian.eigenvectorBasis i x) ^ 2 := by
          apply Fintype.sum_nonneg
          intro i
          simp only [Pi.zero_apply, ←Complex.normSq_eq_abs, Complex.normSq_nonneg]
        simp only [Complex.norm_eq_abs, EuclideanSpace.norm_eq, Real.sq_sqrt hnonneg]
    }
    distr := ρ.spectrum}

/-- The spectral pure-state ensemble of `ρ` mixes to `ρ` -/
theorem spectral_ensemble_mix : mix (↑(spectral_ensemble ρ) : MEnsemble d d) = ρ := by
  ext i j
  sorry

end Ensemble
end ensemble

section ptrace

section mat_trace

variable [AddCommMonoid R]

def _root_.Matrix.traceLeft (m : Matrix (d × d₁) (d × d₂) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₁ j₁ ↦ ∑ i₂, m (i₂, i₁) (i₂, j₁)

def _root_.Matrix.traceRight (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)

@[simp]
theorem _root_.Matrix.trace_of_traceLeft (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceLeft.trace = A.trace := by
  convert (Fintype.sum_prod_type_right _).symm
  rfl

@[simp]
theorem _root_.Matrix.trace_of_traceRight (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceRight.trace = A.trace := by
  convert (Fintype.sum_prod_type _).symm
  rfl

variable [RCLike R] {A : Matrix (d₁ × d₂) (d₁ × d₂) R}

theorem _root_.Matrix.PosSemidef.traceLeft (hA : A.PosSemidef) : A.traceLeft.PosSemidef :=
  sorry

theorem _root_.Matrix.PosSemidef.traceRight (hA : A.PosSemidef) : A.traceRight.PosSemidef :=
  sorry

end mat_trace

-- TODO:
-- * Partial trace of direct product is the original state

/-- Partial tracing out the left half of a system. -/
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ where
  m := ρ.m.traceLeft
  pos := ρ.pos.traceLeft
  tr := ρ.tr ▸ ρ.m.trace_of_traceLeft

/-- Partial tracing out the right half of a system. -/
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  m := ρ.m.traceRight
  pos := ρ.pos.traceRight
  tr := ρ.tr ▸ ρ.m.trace_of_traceRight

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceLeft (ρ₁ ⊗ ρ₂) = ρ₂ := by
  ext
  simp_rw [traceLeft, Matrix.traceLeft, prod]
  dsimp
  have h : (∑ i : d₁, ρ₁.m i i) = 1 := ρ₁.tr
  rw [← Finset.sum_mul, h, one_mul]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceRight (ρ₁ ⊗ ρ₂) = ρ₁ := by
  ext
  simp_rw [traceRight, Matrix.traceRight, prod]
  dsimp
  have h : (∑ i : d₂, ρ₂.m i i) = 1 := ρ₂.tr
  rw [← Finset.mul_sum, h, mul_one]

end ptrace

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, MState.spectrum (ρ₁ ⊗ ρ₂) (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  sorry

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : Distribution ρLRs, --Distribution over those pairs, an ensemble
      ρ.m = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).m ⊗ₖ (Prod.snd ρLR.val).m

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, Distribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp only [prod, Finset.univ_unique, Unique.eq_default, Distribution.constant_eq, ite_true,
    Prob.toReal_one, Finset.default_singleton, one_smul, Finset.sum_const, Finset.card_singleton]

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  sorry

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  sorry

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.pos.eigenvalues_nonneg i
    simp [mul_pow, Real.sq_sqrt, h₁, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀x, ∑ i : d, Complex.abs ((Matrix.IsHermitian.eigenvectorBasis ρ.Hermitian) x i) ^ 2 = 1 :=
      sorry
    apply @RCLike.ofReal_injective (Complex)
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, Matrix.traceRight]
  simp only [pure_of, Matrix.of_apply, Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  sorry

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ where
  m := ρ.m.submatrix e e
  pos := (Matrix.posSemidef_submatrix_equiv e).mpr ρ.pos
  tr := ρ.tr ▸ Fintype.sum_equiv _ _ _ (congrFun rfl)

--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

-- @[simp] --This theorem statement doesn't typecheck because spectrum reuses indices.
-- theorem spectrum_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.spectrum = ρ.spectrum :=
--   sorry

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  rfl

@[simp]
theorem traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight :=
  rfl

@[simp]
theorem traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft :=
  rfl

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  rfl

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  rfl

@[simp]
theorem traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  simpa [assoc, relabel, Matrix.traceLeft, traceLeft, Matrix.traceRight, traceRight]
    using Finset.sum_comm

@[simp]
theorem traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
theorem traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  ext
  simp [assoc, relabel, Matrix.traceRight, traceRight, Fintype.sum_prod_type]

@[simp]
theorem traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  convert ρ.SWAP.assoc.SWAP.traceRight_assoc
  simp

@[simp]
theorem traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  ext
  simpa [assoc, relabel, traceLeft, Matrix.traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
    using Finset.sum_comm

@[simp]
theorem traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

@[simp]
theorem traceNorm_eq_1 (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.pos.traceNorm_PSD_eq_trace
    _ = 1 := ρ.tr
  Complex.ofReal_eq_one.mp this

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance instTopoMState : TopologicalSpace (MState d) :=
  TopologicalSpace.induced (MState.m) instTopologicalSpaceMatrix

/-- The projection from mixed states to their matrices is an embedding -/
theorem toMat_IsEmbedding : Topology.IsEmbedding (MState.m (d := d)) where
  eq_induced := rfl
  injective := toMat_inj

instance instT5MState : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

end topology

end MState
