import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.PurifiedDistance

/-! # Mixture Floor -/


open Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy


/-- Sub-normalization generalized-fidelity correction for a finite `Fintype`-indexed
nonnegative convex combination, obtained from the `ℕ`-indexed
`InfoTheory.SmoothMinEntropy.weighted_mixture_fidelityGen_ge` by transporting along an embedding
`Z ↪ ℕ`. -/
private lemma le_sum_mul_add_sqrt_mul_of_forall_le
    {Z : Type*} [Fintype Z] [Nonempty Z]
    (w a u v : Z → ℝ) (c : ℝ)
    (hw : ∀ z, 0 ≤ w z) (ha : ∀ z, 0 ≤ a z) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hc1 : c ≤ 1) (hsum : ∑ z, w z = 1)
    (hcomp : ∀ z, c ≤ a z + Real.sqrt (u z * v z)) :
    c ≤ (∑ z, w z * a z) +
        Real.sqrt ((∑ z, w z * u z) * (∑ z, w z * v z)) := by
  classical
  set e : Z ↪ ℕ := (Fintype.equivFin Z).toEmbedding.trans Fin.valEmbedding with he
  have hinv : ∀ z, Function.invFun e (e z) = z := Function.leftInverse_invFun e.injective
  set wN : ℕ → ℝ := fun s => w (Function.invFun e s) with hwN
  set aN : ℕ → ℝ := fun s => a (Function.invFun e s) with haN
  set uN : ℕ → ℝ := fun s => u (Function.invFun e s) with huN
  set vN : ℕ → ℝ := fun s => v (Function.invFun e s) with hvN
  have hwNe : ∀ z, wN (e z) = w z := fun z => by simp only [hwN, hinv]
  have haNe : ∀ z, aN (e z) = a z := fun z => by simp only [haN, hinv]
  have huNe : ∀ z, uN (e z) = u z := fun z => by simp only [huN, hinv]
  have hvNe : ∀ z, vN (e z) = v z := fun z => by simp only [hvN, hinv]
  set S : Finset ℕ := Finset.univ.map e with hSdef
  have hsumN : ∀ (g : Z → ℝ) (gN : ℕ → ℝ), (∀ z, gN (e z) = g z) →
      ∑ s ∈ S, gN s = ∑ z, g z := by
    intro g gN hge
    rw [hSdef, Finset.sum_map]
    exact Finset.sum_congr rfl (fun z _ => hge z)
  have key := InfoTheory.SmoothMinEntropy.weighted_mixture_fidelityGen_ge S wN aN uN vN c 0
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [hwNe]; exact hw z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [haNe]; exact ha z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [huNe]; exact hu z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [hvNe]; exact hv z)
    le_rfl hc1
    (by rw [zero_add, hsumN w wN hwNe]; exact hsum)
    (fun s hs => by
      obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs
      rw [haNe, huNe, hvNe]; exact hcomp z)
  have e1 : ∑ s ∈ S, wN s * aN s = ∑ z, w z * a z :=
    hsumN (fun z => w z * a z) (fun s => wN s * aN s)
      (fun z => by rw [hwNe, haNe])
  have e2 : ∑ s ∈ S, wN s * uN s = ∑ z, w z * u z :=
    hsumN (fun z => w z * u z) (fun s => wN s * uN s)
      (fun z => by rw [hwNe, huNe])
  have e3 : ∑ s ∈ S, wN s * vN s = ∑ z, w z * v z :=
    hsumN (fun z => w z * v z) (fun s => wN s * vN s)
      (fun z => by rw [hwNe, hvNe])
  rw [e1, e2, e3] at key
  simpa only [zero_add] using key

end InfoTheory.SmoothMinEntropy
