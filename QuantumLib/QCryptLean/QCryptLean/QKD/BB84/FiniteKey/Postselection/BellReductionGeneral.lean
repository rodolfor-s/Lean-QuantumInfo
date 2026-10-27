import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReduction
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReference
import QCryptLean.QKD.BB84.FiniteKey.Postselection.PassBlockBellSymmetry
import QCryptLean.QKD.BB84.FiniteKey.Postselection.RegisterTrickGeneral
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Channels.Postselection

/-!
# The Bell-symmetric `C(n+3,3)` postselection reduction at a general `m`

`half_mul_diamondNorm_sub_le_correctness_add_bell` separates the
verification error: the differ block contributes `2^(-ℓEV)` directly, and only the agree
block's Bell-reference trace distance (half the trace norm) receives the factor `C(n+3,3)`.

## The de Finetti charge stays at the full `n`

`C(n+3,3) = bellSymmetricDim n` is the dimension of the symmetric subspace on **all `n`** registers
and is unchanged by `m`: `m` scopes the announced-PE register width only, and the postselection
reference `bellCKRDeFinettiPurification n` lives on the `4^n ⊗ 4^n` input side, which carries no
split point.  Re-scoping the charge to `n − m` would move a parameter in the condition without
moving the budget.

## Which Nahar et al. statement licenses `x = 4`

The de Finetti dimension for a symmetric reference is cited from
arXiv:2403.11851, `main.tex:354` `\label{lem:groupPurification}`, stated for a general
compact `G` and giving a purification on `Sym(⨁ᵢ ℂ^{mᵢ} ⊗ ℂ^{mᵢ})`, i.e. `x = ∑ᵢ mᵢ²`.  It is not
cited from `main.tex:362` `\label{cor:symmetryDeFinetti}` nor its lift `main.tex:521`, both of which
are stated only for a product group `G = G_A × G_B`, while the group used here,
`bilateralPauli = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]`, is the bilateral `ℤ₂×ℤ₂`.  The four Bell
operators give four one-dimensional irreps on `ℂ⁴`, so `∑ᵢ mᵢ² = 4` and the exponent is `x − 1 = 3`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, `main.tex:481`
`\label{thm:maintheorem}` and `main.tex:354` `\label{lem:groupPurification}` at `x = ∑ᵢ mᵢ² = 4`;
Christandl–König–Renner (2009), `arXiv:0809.3019`, `main.tex:268`–`:401` (\emph{Main Result}: the
Post-Selection Theorem `\label{thm:main}` :291–:301, the substate-extraction Lemma
`\label{lem:extractpart}` :319–:328); Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/

open Quantum.Operators Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace QKD.BB84.FiniteKey

open QKD.BB84.Model.Announced
open QKD.BB84.Model

/-! ## The general-`m` instances -/

/-- Correctness is charged directly, while Bell postselection lifts only the agree block.

The normalized diamond distance is bounded by `2^(-ℓEV)` plus `C(n+3,3)` times
the agree-block trace distance (half the trace norm) on the Bell de Finetti purification. -/
theorem half_mul_diamondNorm_sub_le_correctness_add_bell
    (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant) :
    (1 / 2) * diamondNorm
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      (2 : ℝ) ^ (-(ℓEV : ℝ)) +
        (Nat.choose (n + 3) 3 : ℝ) *
          ((1 / 2) * ckrTraceNorm
            (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
            (bellCKRDeFinettiPurification n)) := by
  have hagree := diamondNorm_le_bellDim_mul_ckrTraceNorm
    (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (permutationCovariant_symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (symPassBlockDelta_conjTranspose
      false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (fun dimR _ g M => traceNorm_passDelta_twirl
      false n m ℓ ℓEV Q δ peSel xSel leakEC ec hec dimR g M)
  rw [symReal_sub_symIdeal_eq_add_passBlocks]
  have hsum := add_le_add hagree
    (diamondNorm_symDiffer_le_two_mul_pow_neg n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  have h := (diamondNorm_add_le _ _).trans (hsum.trans_eq (add_comm _ _))
  linarith

end QKD.BB84.FiniteKey

end -- noncomputable section
