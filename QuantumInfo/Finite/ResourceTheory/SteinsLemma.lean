import QuantumInfo.Finite.ResourceTheory.FreeState

open ResourcePretheory
open FreeStateTheory
open NNReal
open ComplexOrder

section hypotesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : Matrix d d ℂ //
    ∃ h : m.PosSemidef ∧ m ≤ 1, MState.exp_val (Matrix.isHermitian_one.sub h.1.1) ρ ≤ ε},
  ⨆ σ ∈ S,
  ⟨MState.exp_val T.2.1.1.1 σ, MState.exp_val_prob T.2.1 σ⟩

private theorem Lemma3 (ρ : MState d) (ε : ℝ) (S : Set (MState d)) :
    ⨆ σ ∈ S, OptimalHypothesisRate ρ ε {σ} = OptimalHypothesisRate ρ ε S
  := by
  sorry

end hypotesting

variable {ι : Type*} [FreeStateTheory ι]
variable {i : ι}

-- This theorem should follow from "Fekete's subadditive lemma", which can be found in
-- Lemma A.1 of Hayashi's book "Quantum Information Theory - Mathematical Foundation".
--
-- Also, the sequence of states S^(n) mentioned in the paper is implicitly defined here as
-- IsFree (i := i⊗^[n]). It has all the properties we need plus some more (e.g., for this
-- lemma, we don't need convexity).
/-- Lemma 5 -/
theorem limit_rel_entropy_exists (ρ : MState (H i)) :
  ∃ d : ℝ, Filter.Tendsto (fun n ↦ (⨅ σ ∈ IsFree (i := i⊗^[n]), qRelativeEnt (ρ⊗^[n]) σ) / n)
  Filter.atTop (nhds (↑d : EReal)) := by
  sorry

variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Lemma 6 from the paper -/
private theorem Lemma6 (m : ℕ) (hm : 0 < m) (ρ σf : MState d) (σm : MState (Fin m → d)) (hσf : σf.m.PosDef) (ε : ℝ)
    (hε : 0 < ε) :
    let σn (n : ℕ) : (MState (Fin n → d)) :=
      let l : ℕ := n / m
      let q : ℕ := n % m
      let σl := σm ⊗^ l
      let σr := σf ⊗^ q
      let eqv : (Fin n → d) ≃ (Fin l → Fin m → d) × (Fin q → d) :=
        Equiv.piCongrLeft (fun _ ↦ d) ((finCongr (Eq.symm (Nat.div_add_mod' n m))).trans (finSumFinEquiv.symm))
          |>.trans <|
           (Equiv.sumArrowEquivProdArrow ..)
          |>.trans <|
           (Equiv.prodCongr (Equiv.piCongrLeft (fun _ ↦ d) finProdFinEquiv).symm (Equiv.refl _))
          |>.trans <|
          (Equiv.prodCongr (Equiv.curry ..) (Equiv.refl _))
      (σl.prod σr).relabel eqv
    Filter.atTop.limsup (fun n ↦ - Real.log (OptimalHypothesisRate (ρ ⊗^ n) ε {σn n}) / n : ℕ → ℝ) ≤
    (qRelativeEnt (ρ ⊗^ m) σm) / m
  := by
  sorry

/-- Theorem 4, which is _also_ called the Generalized Quantum Stein's Lemma in Hayashi & Yamasaki -/
theorem limit_hypotesting_eq_limit_rel_entropy (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ,
      Filter.Tendsto (fun n ↦ -Real.log (OptimalHypothesisRate (ρ⊗^[n]) ε IsFree) / n)
      Filter.atTop (nhds (d))
      ∧
      Filter.Tendsto (fun n ↦ ⨅ σ ∈ IsFree (i := i⊗^[n]), qRelativeEnt (ρ⊗^[n]) σ / n)
      Filter.atTop (nhds (d : EReal))
      := by
  sorry

/-- Lemma 7 from the paper -/
private theorem Lemma7 (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ+) → IsFree (i := i⊗^[n])) :
  -- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
  -- the monotonicity of log and Lemma 3.
  let R1 : ℝ :=
    Filter.liminf (fun n ↦ -Real.log (OptimalHypothesisRate (ρ⊗^[n]) ε IsFree) / n) Filter.atTop
  let R2 : EReal :=
    Filter.liminf (fun n ↦ qRelativeEnt (ρ⊗^[n]) (σ n) / n) Filter.atTop
  (R2 ≥ R1) →
  ∀ ε' : ℝ, 0 < ε' ∧ ε' < ε → -- ε' is written as \tilde{ε} in the paper.
  ∃ σ' : (n : ℕ+) → IsFree (i := i⊗^[n]),
  let R2' : EReal :=
    Filter.liminf (fun n ↦ qRelativeEnt (ρ⊗^[n]) (σ' n) / n) Filter.atTop
  R2' - R1 ≤ (1 - ε') * (R2 - R1)
  := by
  sorry

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦
      -Real.log (OptimalHypothesisRate (ρ⊗^[n]) ε IsFree) / n
    ) Filter.atTop (nhds (RegularizedRelativeEntResource ρ)) := by
  sorry
