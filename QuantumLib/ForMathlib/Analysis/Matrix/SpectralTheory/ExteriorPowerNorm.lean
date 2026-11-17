import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Exterior Power Norm -/


open scoped Matrix
open Matrix

noncomputable section

namespace Math.SpectralTheory

variable {N : ℕ} {k m : ℕ}

/-- The standard orthonormal basis of `EuclideanSpace ℂ (Fin N)`, packaged as a
`Module.Basis` indexed by `Fin N` (which carries its standard `LinearOrder`, the
order required to form the exterior power basis). -/
abbrev euclBasis (N : ℕ) : Module.Basis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toBasis

/-- The coordinate isomorphism from the `k`-th exterior power of
`EuclideanSpace ℂ (Fin N)` to the Euclidean space on the index set of the
exterior power basis (the `k`-subsets of `Fin N`).

Composition of `Module.Basis.exteriorPower`'s `equivFun` (coordinates in the
wedge-of-standard-basis basis) with the `WithLp` identification of plain
functions with `EuclideanSpace`. Transporting the Euclidean inner product back
along this isomorphism makes the wedge basis orthonormal, which is exactly the
induced inner product of Bhatia IX.2. -/
def wedgeEquiv (N k : ℕ) : (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) ≃ₗ[ℂ]
    EuclideanSpace ℂ (Set.powersetCard (Fin N) k) :=
  ((euclBasis N).exteriorPower k).equivFun ≪≫ₗ (WithLp.linearEquiv 2 ℂ _).symm

/-- The induced normed-group structure on `⋀ᵏ(EuclideanSpace ℂ (Fin N))`, the
norm of the canonical inner product making the wedge basis orthonormal (pulled
back from `EuclideanSpace ℂ (powersetCard (Fin N) k)` along `wedgeEquiv`).
Reference: Bhatia, *Matrix Analysis*, IX.2. -/
noncomputable instance wedgeNormedAddCommGroup (N k : ℕ) :
    NormedAddCommGroup (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) :=
  letI : InnerProductSpace.Core ℂ (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) :=
  { inner x y := inner ℂ (wedgeEquiv N k x) (wedgeEquiv N k y)
    conj_inner_symm x y := inner_conj_symm _ _
    re_inner_nonneg x := inner_self_nonneg
    add_left x y z := by rw [(wedgeEquiv N k).map_add, inner_add_left]
    smul_left x y r := by rw [(wedgeEquiv N k).map_smul, inner_smul_left]
    definite x hx := by
      have h0 : wedgeEquiv N k x = 0 := by rwa [inner_self_eq_zero] at hx
      exact (wedgeEquiv N k).map_eq_zero_iff.mp h0 }
  this.toNormedAddCommGroup

/-- The canonical inner product space structure on `⋀ᵏ(EuclideanSpace ℂ (Fin N))`
making the wedge of the standard orthonormal basis orthonormal. Reference:
Bhatia, *Matrix Analysis*, IX.2. -/
noncomputable instance wedgeInnerProductSpace (N k : ℕ) :
    InnerProductSpace ℂ (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) := .ofCore _

/-- **Compound-matrix multiplicativity / functoriality of the exterior power**:
the `k`-th exterior power of a matrix power equals the matrix power of the
`k`-th exterior power, as endomorphisms of `⋀ᵏ(EuclideanSpace ℂ (Fin N))`:
`⋀ᵏ(Bᵐ) = (⋀ᵏB)ᵐ`.

Here `exteriorPower.map k (toEuclideanLin B)` is the induced endomorphism `⋀ᵏB`
on the exterior power. The statement is pure algebra: `toEuclideanLin` is a ring
homomorphism (composition of linear maps), `exteriorPower.map` is functorial
(`exteriorPower.map_comp`, `exteriorPower.map_id`), so the compound map of a
product is the product of compound maps; the power case follows by induction on
`m`.

Reference: Horn-Johnson, *Topics in Matrix Analysis*, Thm 3.3.2 (compound matrix
multiplicativity `⋀ᵏ(XY) = ⋀ᵏX · ⋀ᵏY`). -/
lemma exteriorPower_map_pow (B : Matrix (Fin N) (Fin N) ℂ) (k m : ℕ) :
    exteriorPower.map k (Matrix.toEuclideanLin (B ^ m))
      = (exteriorPower.map k (Matrix.toEuclideanLin B)) ^ m := by
  have hmul : ∀ (P Q : Matrix (Fin N) (Fin N) ℂ),
      Matrix.toEuclideanLin (P * Q)
        = (Matrix.toEuclideanLin P) ∘ₗ (Matrix.toEuclideanLin Q) := by
    intro P Q
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
    rw [Matrix.mulVec_mulVec]
  have hone : Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) = LinearMap.id := by
    ext v
    simp
  induction m with
  | zero =>
    simp only [pow_zero, hone, exteriorPower.map_id, Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, hmul, exteriorPower.map_comp, Module.End.mul_eq_comp]

/-- Continuous-linear-map form of compound-matrix functoriality: the continuous
`k`-th exterior power of `Bᵐ` equals the `m`-th power (in the normed ring of
continuous endomorphisms of `⋀ᵏ(EuclideanSpace ℂ (Fin N))`) of the continuous
`k`-th exterior power of `B`.

This is `exteriorPower_map_pow` transported through `LinearMap.toContinuousLinearMap`
(an isomorphism onto the continuous endomorphisms, since the exterior power of a
finite-dimensional space is finite-dimensional), so that the operator-norm
submultiplicativity `‖fᵐ‖ ≤ ‖f‖ᵐ` of the normed ring applies. Reference:
Horn-Johnson, *Topics in Matrix Analysis*, 3.3.2. -/
lemma exteriorPower_toCLM_pow (B : Matrix (Fin N) (Fin N) ℂ) (k m : ℕ) :
    LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin (B ^ m)))
      = (LinearMap.toContinuousLinearMap (exteriorPower.map k (Matrix.toEuclideanLin B))) ^ m := by
  -- Descend to the underlying *function* on `⋀ᵏ` (`coeFn_injective`): there both sides are the
  -- `m`-fold iterate of `⇑(exteriorPower.map k (toEuclideanLin B))`, and
  -- `⇑(toContinuousLinearMap ·) = ⇑·` holds definitionally. Comparing functions only, the two
  -- `Monoid` structures on `⋀ᵏ →L ⋀ᵏ` (from the linear structure and from the wedge norm) never
  -- have to be identified, as a direct `map_pow` along `Module.End.toContinuousLinearMap` would.
  refine ContinuousLinearMap.coeFn_injective ?_
  -- right side: `⇑(Tᵐ) = (⇑T)^[m]` for the continuous map `T`
  refine Eq.trans ?_ (FunLike.coe_pow_eq_iterate _ m).symm
  -- left side: compound-matrix functoriality, then `⇑(fᵐ) = (⇑f)^[m]` for the linear map `f`.
  simp only [exteriorPower_map_pow]
  exact Module.End.coe_pow (exteriorPower.map k (Matrix.toEuclideanLin B)) m

/-- **`wedgeEquiv` is a linear isometry**: the coordinate isomorphism preserves
the induced wedge norm. By construction (`wedgeNormedAddCommGroup`) the wedge
inner product is the pullback `⟨x,y⟩ = ⟨wedgeEquiv x, wedgeEquiv y⟩`, so the norms
agree: `‖wedgeEquiv N k x‖ = ‖x‖`. Both norms are `√(re⟨·,·⟩)`
(`norm_eq_sqrt_re_inner`), and the inner products coincide definitionally.
Reference: Bhatia, *Matrix Analysis*, IX.2 (the wedge basis is orthonormal in the
induced inner product). -/
lemma wedgeEquiv_norm {N k : ℕ} (x : ⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) :
    ‖wedgeEquiv N k x‖ = ‖x‖ := by
  simp only [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rfl


/-- The `k`-subset of `Fin N`, as a member of the `ιMulti_family` index set
`↑(Set.powersetCard (Fin N) k)`, attached to a `{S // S.card = k}` value. -/
abbrev toPowersetCard {N k : ℕ} (S : {S : Finset (Fin N) // S.card = k}) :
    ↑(Set.powersetCard (Fin N) k) :=
  ⟨S.1, (Set.powersetCard.mem_iff).mpr S.2⟩

/-- The `k`-subset index type `{S // S.card = k}` of `Fin N` has cardinality
`N.choose k`, matching `Module.finrank ℂ (⋀ᵏ(EuclideanSpace ℂ (Fin N)))`
(`exteriorPower.finrank_eq`). So an orthonormal `ιMulti_family` indexed by it has
exactly the size of an orthonormal basis of the wedge space. -/
lemma card_powersetCard_subtype_eq_finrank_wedge {N k : ℕ} :
    Fintype.card {S : Finset (Fin N) // S.card = k}
      = Module.finrank ℂ (⋀[ℂ]^k (EuclideanSpace ℂ (Fin N))) := by
  rw [exteriorPower.finrank_eq, Fintype.card_finset_len, finrank_euclideanSpace, Fintype.card_fin]


section CauchyBinet

variable {R : Type*} [CommRing R]

/-- Expansion of `det (A * B)` for a `(Fin k) × J` and `J × (Fin k)` pair, as a double sum over
functions `q : Fin k → J` and permutations. The first step of the standard `Matrix.det_mul`
argument, kept rectangular (`J` need not be `Fin k`). -/
private lemma det_mul_expand {k : ℕ} {J : Type*} [Fintype J]
    (A : Matrix (Fin k) J R) (B : Matrix J (Fin k) R) :
    (A * B).det = ∑ q : Fin k → J, ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (q i) * B (q i) i := by
  classical
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ]
  rw [Finset.sum_comm]

/-- Non-injective `q` contribute zero to the expansion (the alternating-sign sum over
permutations vanishes when two columns coincide). -/
private lemma det_mul_aux_rect {k : ℕ} {J : Type*}
    {A : Matrix (Fin k) J R} {B : Matrix J (Fin k) R} {q : Fin k → J}
    (H : ¬ Function.Injective q) :
    (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ x, A (σ x) (q x) * B (q x) x)
      = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, q i = q j ∧ i ≠ j := by
    rw [Function.Injective] at H
    push Not at H
    exact H
  exact
    Finset.sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, A (σ x) (q x)) = ∏ x, A ((σ * Equiv.swap i j) x) (q x) :=
          Fintype.prod_equiv (Equiv.swap i j) _ _ (by simp [Equiv.apply_swap_eq_self hpij])
        simp [this, Equiv.Perm.sign_swap hij, -Equiv.Perm.sign_swap', Finset.prod_mul_distrib])
      (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij) (fun _ _ => Finset.mem_univ _)
      fun σ _ => Equiv.mul_swap_involutive i j σ

/-- Reindexing of a sum of a `Fin k → Fin N`-indexed family that vanishes on non-injective
arguments: each injective tuple factors uniquely as an increasing enumeration of a `k`-subset `U`
composed with a permutation of `Fin k`. -/
private lemma sum_eq_sum_powersetCard_perm {k N : ℕ} (g : (Fin k → Fin N) → R)
    (hg0 : ∀ q : Fin k → Fin N, ¬ Function.Injective q → g q = 0) :
    (∑ q : Fin k → Fin N, g q)
      = ∑ U : ↑(Set.powersetCard (Fin N) k), ∑ q : Fin k → Fin k,
          g (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) (q i)) := by
  classical
  have hUf_inj : ∀ U : ↑(Set.powersetCard (Fin N) k),
      Function.Injective (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) i : Fin k → Fin N) :=
    fun U => (Set.powersetCard.ofFinEmbEquiv.symm U).injective
  -- range of the order embedding is the underlying finset
  have hrange : ∀ U : ↑(Set.powersetCard (Fin N) k),
      Finset.image (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) i) Finset.univ
        = (U : Finset (Fin N)) := by
    intro U
    ext a
    rw [Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    rw [Set.powersetCard.mem_coe_iff, ← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem,
      Set.mem_range]
  -- image of `Uf ∘ q` for surjective `q` is the underlying finset
  have himg_comp : ∀ (U : ↑(Set.powersetCard (Fin N) k)) (q : Fin k → Fin k),
      Function.Surjective q →
      Finset.image (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) (q i)) Finset.univ
        = (U : Finset (Fin N)) := by
    intro U q hq
    have hcomp : (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) (q i))
        = (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) i) ∘ q := rfl
    rw [hcomp, ← Finset.image_image, Finset.image_univ_of_surjective hq, hrange]
  -- LHS: drop non-injective summands
  rw [← Finset.sum_filter_of_ne (s := Finset.univ) (f := g) (p := Function.Injective)
    (fun q _ hgq => not_not.mp (fun h => hgq (hg0 q h)))]
  -- RHS: drop non-injective inner summands
  rw [Finset.sum_congr rfl (fun U _ =>
    (Finset.sum_filter_of_ne (s := Finset.univ)
      (f := fun q : Fin k → Fin k => g (fun i => (Set.powersetCard.ofFinEmbEquiv.symm U) (q i)))
      (p := Function.Injective)
      (fun q _ hgq => not_not.mp (fun h => hgq
        (hg0 _ (mt Function.Injective.of_comp h))))).symm)]
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij
    (fun (x : Σ _U : ↑(Set.powersetCard (Fin N) k), Fin k → Fin k) _ =>
      (fun i => (Set.powersetCard.ofFinEmbEquiv.symm x.1) (x.2 i)))
    ?_ ?_ ?_ (fun _ _ => rfl)).symm
  · -- maps into the injective filter
    intro x hx
    rw [Finset.mem_sigma, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hUf_inj x.1).comp hx.2.2⟩
  · -- injectivity of the reindexing
    rintro ⟨U₁, q₁⟩ hx₁ ⟨U₂, q₂⟩ hx₂ hij
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    have e1 := himg_comp U₁ q₁ (Finite.injective_iff_surjective.mp hx₁)
    have e2 := himg_comp U₂ q₂ (Finite.injective_iff_surjective.mp hx₂)
    have hU : (U₁ : Finset (Fin N)) = (U₂ : Finset (Fin N)) := by
      rw [← e1, ← e2]; exact congrArg (fun f => Finset.image f Finset.univ) hij
    have hU1 : U₁ = U₂ := Subtype.ext hU
    subst hU1
    have hq : q₁ = q₂ := by
      funext i
      apply hUf_inj U₁
      exact congrFun hij i
    subst hq
    rfl
  · -- surjectivity of the reindexing
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hpinj⟩ := hp
    set s : Finset (Fin N) := Finset.image p Finset.univ with hs_def
    have hs : s.card = k := by
      rw [hs_def, Finset.card_image_of_injective _ hpinj, Finset.card_univ, Fintype.card_fin]
    refine ⟨⟨⟨s, (Set.powersetCard.mem_iff).mpr hs⟩,
      fun i => (s.orderIsoOfFin hs).symm ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩⟩,
      ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
      intro a b hab
      apply hpinj
      exact Subtype.ext_iff.mp ((s.orderIsoOfFin hs).symm.injective hab)
    · funext i
      dsimp only
      have h := Finset.coe_orderIsoOfFin_apply s hs
        ((s.orderIsoOfFin hs).symm ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩)
      rw [OrderIso.apply_symm_apply] at h
      exact h.symm

/-- **Cauchy–Binet formula**: the determinant of a product of a `(Fin k) × (Fin N)` matrix and a
`(Fin N) × (Fin k)` matrix is the sum, over the `k`-subsets `U` of `Fin N`, of the products of the
corresponding `k × k` minors (columns of `P` / rows of `Q` indexed by `U`). -/
private lemma cauchy_binet {k N : ℕ} (P : Matrix (Fin k) (Fin N) R)
    (Q : Matrix (Fin N) (Fin k) R) :
    (P * Q).det = ∑ U : ↑(Set.powersetCard (Fin N) k),
      (P.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm U)).det *
        (Q.submatrix (Set.powersetCard.ofFinEmbEquiv.symm U) id).det := by
  have hA2 : ∀ U : ↑(Set.powersetCard (Fin N) k),
      (P.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm U)).det *
        (Q.submatrix (Set.powersetCard.ofFinEmbEquiv.symm U) id).det
        = ∑ q : Fin k → Fin k, ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ i, P (σ i) ((Set.powersetCard.ofFinEmbEquiv.symm U) (q i)) *
                  Q ((Set.powersetCard.ofFinEmbEquiv.symm U) (q i)) i := by
    intro U
    rw [← Matrix.det_mul, det_mul_expand]
    simp only [Matrix.submatrix_apply, id_eq]
  rw [det_mul_expand P Q, Finset.sum_congr rfl (fun U _ => hA2 U)]
  exact sum_eq_sum_powersetCard_perm
    (fun q => ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) *
      ∏ i, P (σ i) (q i) * Q (q i) i)
    (fun q hq => det_mul_aux_rect hq)

end CauchyBinet

/-- **Gram-determinant pairing of basis wedges** (the defining property of the
induced inner product on `⋀ᵏ`, Bhatia IX.2 / Cauchy–Binet). For two families
`v w : Fin N → EuclideanSpace ℂ (Fin N)` and two `k`-subsets `S T` of `Fin N`,
the wedge inner product of `⋀_{i∈S} vᵢ` and `⋀_{j∈T} wⱼ` (the `ιMulti_family`
basis wedges) equals the determinant of the cross-Gram matrix
`(a,b) ↦ ⟨v_{S a}, w_{T b}⟩`, where `S a`, `T b` enumerate `S`, `T` in increasing
order (`Finset.orderEmbOfFin`).

This is *the* defining relation of the antisymmetric-tensor inner product. It
cannot be read off Mathlib because the wedge inner product here is the bespoke
`wedgeInnerProductSpace`, transported via `wedgeEquiv` from the standard basis;
unfolding it, `⟨⋀v_S, ⋀w_T⟩ = Σ_U conj(ιMultiDual U (⋀v_S)) · ιMultiDual U (⋀w_T)`
(a sum over `k`-subsets `U` of products of `k×k` minors of `v`, `w` in the
standard basis), and the Cauchy–Binet formula collapses that sum of minor
products to the single Gram determinant. Reference: Bhatia, *Matrix Analysis*, IX.2
(the Gram/determinant pairing on antisymmetric tensors). -/
theorem wedge_inner_eq_gram_det {N k : ℕ}
    (v w : Fin N → EuclideanSpace ℂ (Fin N))
    (S T : {S : Finset (Fin N) // S.card = k}) :
    inner ℂ (exteriorPower.ιMulti_family ℂ k v (toPowersetCard S))
        (exteriorPower.ιMulti_family ℂ k w (toPowersetCard T))
      = (Matrix.of (fun a b : Fin k =>
          inner ℂ (v (S.1.orderEmbOfFin S.2 a)) (w (T.1.orderEmbOfFin T.2 b)))).det := by
  change inner ℂ (wedgeEquiv N k (exteriorPower.ιMulti_family ℂ k v (toPowersetCard S)))
      (wedgeEquiv N k (exteriorPower.ιMulti_family ℂ k w (toPowersetCard T))) = _
  rw [PiLp.inner_apply]
  have hofLp : ∀ (z : ⋀[ℂ]^k (EuclideanSpace ℂ (Fin N)))
      (i : ↑(Set.powersetCard (Fin N) k)),
      (wedgeEquiv N k z).ofLp i = ((euclBasis N).exteriorPower k).repr z i := fun _ _ => rfl
  simp only [hofLp]
  simp only [exteriorPower.basis_repr_apply, RCLike.inner_apply]
  have hcoord : ∀ (m : Fin N) (x : EuclideanSpace ℂ (Fin N)), (euclBasis N).coord m x = x m := by
    intro m x; simp [euclBasis, Module.Basis.coord]
  have hdual : ∀ (u : Fin N → EuclideanSpace ℂ (Fin N)) (P : {S : Finset (Fin N) // S.card = k})
      (U : ↑(Set.powersetCard (Fin N) k)),
      exteriorPower.ιMultiDual ℂ k (euclBasis N) U
          (exteriorPower.ιMulti_family ℂ k u (toPowersetCard P))
        = (Matrix.of fun i j : Fin k =>
            (u (P.1.orderEmbOfFin P.2 i)) ((Set.powersetCard.ofFinEmbEquiv.symm U) j)).det := by
    intro u P U
    rw [show exteriorPower.ιMulti_family ℂ k u (toPowersetCard P)
          = exteriorPower.ιMulti ℂ k (u ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm (toPowersetCard P)))
          from rfl,
      exteriorPower.ιMultiDual_apply_ιMulti]
    congr 1
  -- The cross-Gram matrix as a product of conjugate-coordinate matrices.
  have hinner : ∀ (x y : EuclideanSpace ℂ (Fin N)),
      inner ℂ x y = ∑ n, (starRingEnd ℂ) (x n) * y n := by
    intro x y
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun n _ => by rw [RCLike.inner_apply]; ring)
  set Pmat : Matrix (Fin k) (Fin N) ℂ :=
    Matrix.of (fun a n => (starRingEnd ℂ) ((v (S.1.orderEmbOfFin S.2 a)) n)) with hP
  set Qmat : Matrix (Fin N) (Fin k) ℂ :=
    Matrix.of (fun n b => (w (T.1.orderEmbOfFin T.2 b)) n) with hQ
  have hmateq : (Matrix.of (fun a b : Fin k =>
      inner ℂ (v (S.1.orderEmbOfFin S.2 a)) (w (T.1.orderEmbOfFin T.2 b)))) = Pmat * Qmat := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, hP, hQ]
    rw [hinner]
  rw [hmateq, cauchy_binet]
  apply Finset.sum_congr rfl
  intro U _
  -- The `Pmat` minor is the conjugate of the `v`-minor; the `Qmat` minor is the transpose of the
  -- `w`-minor.  Cauchy–Binet then matches the wedge-coordinate sum term by term.
  have hPm : (Pmat.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm U))
      = (starRingEnd ℂ).mapMatrix (Matrix.of fun i j : Fin k =>
          (v (S.1.orderEmbOfFin S.2 i)) ((Set.powersetCard.ofFinEmbEquiv.symm U) j)) := by
    ext a j
    simp only [Matrix.submatrix_apply, id_eq, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, hP]
  have hQt : (Qmat.submatrix (Set.powersetCard.ofFinEmbEquiv.symm U) id)
      = (Matrix.of fun i j : Fin k =>
          (w (T.1.orderEmbOfFin T.2 i)) ((Set.powersetCard.ofFinEmbEquiv.symm U) j))ᵀ := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Matrix.of_apply, hQ]
  rw [hdual w T U, hdual v S U, RingHom.map_det, ← hPm, hQt, Matrix.det_transpose, mul_comm]

/-- **Wedge of an orthonormal frame is orthonormal** (Bhatia IX.2). If
`v : Fin N → EuclideanSpace ℂ (Fin N)` is orthonormal, then the family of basis
wedges `S ↦ ⋀_{i∈S} vᵢ` (indexed by the `k`-subsets `{S // S.card = k}`) is
orthonormal in the induced wedge inner product.

Immediate corollary of `wedge_inner_eq_gram_det` with `w = v`: the diagonal Gram
`(a,b) ↦ ⟨v_{S a}, v_{S b}⟩` is the identity matrix (orderEmbOfFin is injective and
`v` is orthonormal), so its determinant is `1`; for `S ≠ T` (equal cardinality)
some `T`-index lies outside `S`, giving a zero column in the cross-Gram, so its
determinant is `0`. Reference: Bhatia, *Matrix Analysis*, IX.2. -/
theorem wedge_of_orthonormal_is_orthonormal {N k : ℕ}
    (v : Fin N → EuclideanSpace ℂ (Fin N)) (hv : Orthonormal ℂ v) :
    Orthonormal ℂ (fun S : {S : Finset (Fin N) // S.card = k} =>
      exteriorPower.ιMulti_family ℂ k v (toPowersetCard S)) := by
  classical
  rw [orthonormal_iff_ite]
  intro S T
  rw [wedge_inner_eq_gram_det v v S T]
  by_cases hST : S = T
  · -- Diagonal: the Gram is the identity (`orderEmbOfFin` injective, `v` orthonormal).
    subst hST
    rw [ite_eq_left rfl]
    rw [show (Matrix.of (fun a b : Fin k =>
        inner ℂ (v (S.1.orderEmbOfFin S.2 a)) (v (S.1.orderEmbOfFin S.2 b))))
          = (1 : Matrix (Fin k) (Fin k) ℂ) from ?_, Matrix.det_one]
    ext a b
    simp only [Matrix.of_apply, Matrix.one_apply]
    rw [(orthonormal_iff_ite.mp hv) _ _]
    by_cases hab : a = b
    · simp [hab]
    · rw [ite_eq_right hab, ite_eq_right (fun h => hab ((S.1.orderEmbOfFin S.2).injective h))]
  · -- Off-diagonal: `S ≠ T`, equal cardinality ⇒ a `T`-index lies outside `S` ⇒ zero column.
    rw [ite_eq_right hST]
    have hTnotsub : ¬ (T.1 ⊆ S.1) := by
      intro hsub
      exact hST (Subtype.ext (((Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2])).symm)))
    obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp hTnotsub
    -- `x = T.orderEmbOfFin b` for some `b`; column `b` of the cross-Gram is zero.
    obtain ⟨b, hb⟩ : ∃ b : Fin k, T.1.orderEmbOfFin T.2 b = x := by
      have : x ∈ Finset.map (T.1.orderEmbOfFin T.2).toEmbedding Finset.univ := by
        rw [Finset.map_orderEmbOfFin_univ T.1 T.2]; exact hxT
      simp only [Finset.mem_map, Finset.mem_univ, true_and] at this
      obtain ⟨b, hb⟩ := this; exact ⟨b, hb⟩
    apply Matrix.det_eq_zero_of_column_eq_zero b
    intro a
    simp only [Matrix.of_apply]
    rw [hb]
    apply hv.inner_eq_zero
    intro hcontra
    exact hxS (hcontra ▸ Finset.orderEmbOfFin_mem S.1 S.2 a)

end Math.SpectralTheory
