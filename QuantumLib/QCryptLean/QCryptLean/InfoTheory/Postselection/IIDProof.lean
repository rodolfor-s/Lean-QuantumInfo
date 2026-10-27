import QCryptLean.InfoTheory.QuantumLHL.HashingError

/-! # IIDProof -/


namespace InfoTheory.Postselection

/-- **Nahar et al. `\label{eq:condS}` (main.tex:457–:459)** (lines 505–508) for a chosen accepting
subset `S ⊆ S_σ̂`.

    `ε_AT ∈ [0,1]`, `S ⊆ S_σ̂`, and every fixed-marginal state outside `S` accepts with
    probability at most `ε_AT`:  `σ ∈ S_σ̂ \ S ⟹ Pr(Ω_acc)_σ ≤ ε_AT`.

    `Sσhat` is the fixed-marginal set `S_σ̂`; `pAcc σ = Pr(Ω_acc)_σ` is the accept
    probability on the IID input `σ^{⊗n}`. -/
def SatisfiesAcceptTestBound {ι : Type*} (Sσhat S : Set ι) (pAcc : ι → ℝ) (εAT : ℝ) : Prop :=
  εAT ∈ Set.Icc (0 : ℝ) 1 ∧ S ⊆ Sσhat ∧ ∀ σ ∈ Sσhat \ S, pAcc σ ≤ εAT

end InfoTheory.Postselection
