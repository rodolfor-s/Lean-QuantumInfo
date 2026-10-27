import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Model.RealChannelEntrywise
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacement
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacementAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.RandomizedBlocking

/-! # The ideal model is key replacement after the real model

The identity holds on all input operators and arbitrary retained references.
Public extension commutes with the shared key-replacement resource, so the
identity also survives the announced permutation average.
-/

open Quantum.Operators Quantum.Channels Matrix
open QKD.BB84.Measurement QKD.BB84.FiniteKey
open Quantum.Symmetry

noncomputable section

namespace QKD.BB84.Model

/-- The ideal announcement is key replacement after the real announcement, with Eve retained. -/
theorem announcedIdeal_eq_keyReplace (E : Type*)
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (M : Op (Signals n × E)) :
    Announced.ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q M =
      mapTensorId (keyReplace ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)) E
        (Announced.real E n m ℓ ℓEV peSel xSel leakEC ec δ Q M) := by
  classical
  let : DecidableEq (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) := inferInstance
  let ST := KeyHashSeedPairEV n ℓ ℓEV peSel
  let Y := KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)
  let K : Operation Y Y := keyReplace ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)
  let f : ST → Signals n → Y := outIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q
  let g : Bits ℓ × ST → Signals n → Y := fun ks ω =>
    if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q ks.2.2 ω then
      Announced.idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec ks.1 ks.2 ω
    else Announced.failOutputIndex n m ℓ ℓEV peSel leakEC ec ks.2 ω
  have hsingle (st : ST) (ω : Signals n) (c : ℂ) :
      K (Matrix.single (f st ω) (f st ω) c) =
        ((2 : ℂ) ^ ℓ)⁻¹ • ∑ k : Bits ℓ,
          Matrix.single (g (k, st) ω) (g (k, st) ω) c := by
    dsimp only [K]
    rw [keyReplace_single ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC)]
    by_cases ht : siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
    all_goals simp [f, g, outIndex, ht,
      Announced.passOutputIndex, Announced.failOutputIndex, Announced.idealPassOutputIndex,
      Announced.pePassOutIndex, Announced.peFailOutIndex, Bits,
      ← Nat.cast_smul_eq_nsmul ℂ]
  let R : Operation (Signals n) Y := (Fintype.card ST : ℂ)⁻¹ • ∑ st, classicalMap (f st)
  let I : Operation (Signals n) Y :=
    (Fintype.card (Bits ℓ × ST) : ℂ)⁻¹ • ∑ ks, classicalMap (g ks)
  have hbare (A : Op (Signals n)) : I A = K (R A) := by
    simp only [I, R, LinearMap.smul_apply, LinearMap.sum_apply, classicalMap_apply,
      map_smul, map_sum, hsingle]
    have hc : (Fintype.card (Bits ℓ × ST) : ℂ)⁻¹ =
        (Fintype.card ST : ℂ)⁻¹ * ((2 : ℂ) ^ ℓ)⁻¹ := by
      simp [Bits, Fintype.card_prod, mul_comm]
    rw [hc, mul_smul]
    simp only [← Finset.smul_sum]
    congr 1
    congr 1
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have hR : Announced.real E n m ℓ ℓEV peSel xSel leakEC ec δ Q = mapTensorId R E :=
    congrArg₂ (fun (dx : DecidableEq (Signals n)) (dy : DecidableEq Y) =>
      mapTensorId ((Fintype.card ST : ℂ)⁻¹ • ∑ st : ST,
        @classicalMap (Signals n) Y _ dx dy (f st)) E)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hI : Announced.ideal E n m ℓ ℓEV peSel xSel leakEC ec δ Q = mapTensorId I E :=
    congrArg₂ (fun (dx : DecidableEq (Signals n)) (dy : DecidableEq Y) =>
      mapTensorId ((Fintype.card (Bits ℓ × ST) : ℂ)⁻¹ • ∑ ks : Bits ℓ × ST,
        @classicalMap (Signals n) Y _ dx dy (g ks)) E)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  rw [hR, hI]
  ext p q
  change I (M.submatrix (fun i => (i, p.2)) (fun i => (i, q.2))) p.1 q.1 =
    K (R (M.submatrix (fun i => (i, p.2)) (fun i => (i, q.2)))) p.1 q.1
  exact congrFun₂ (hbare _) p.1 q.1

open scoped Classical in
/-- The symmetrized ideal is key replacement after the symmetrized real map. -/
theorem symIdeal_eq_keyReplace_real (n m ℓ ℓEV : ℕ)
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (ρ : Op (Signals n)) :
    symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ =
      mapTensorId (keyReplace ℓ (SymPEAnnouncePublic n m ℓ ℓEV peSel leakEC)) Unit
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ) := by
  classical
  let D := PEAnnouncePublic n m ℓ ℓEV peSel leakEC
  let K := keyReplace ℓ D
  let K' := keyReplace ℓ (D × Equiv.Perm (Fin n))
  let L := siftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC
  have hcomm (π : Equiv.Perm (Fin n)) : K'.comp (L π) = (L π).comp K := by
    apply LinearMap.ext
    intro A
    dsimp only [K', K, L, siftedPEAnnounceLinear, LinearMap.comp_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    convert keyReplace_reindex_kronecker ℓ D (Equiv.Perm (Fin n)) A
      (permAnnounceProjector n π) using 1
    exact congrArg (fun de : DecidableEq (D × Equiv.Perm (Fin n)) =>
      @keyReplace ℓ _ _ de _) (Subsingleton.elim _ _)
  simp only [symIdeal, symReal, symIdealEveVisible, symRealEveVisible,
    LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  apply congrArg _
  apply Finset.sum_congr rfl
  intro π _
  let M := mapTensorId (classicalMap id) Unit
    (siftedConjAfterPre Unit (unitRegisterEmbed n) peSel xSel (permConjLin π ρ))
  change mapTensorId (L π) Unit (Announced.ideal Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q M) =
    mapTensorId K' Unit
      (mapTensorId (L π) Unit (Announced.real Unit n m ℓ ℓEV peSel xSel leakEC ec δ Q M))
  rw [announcedIdeal_eq_keyReplace]
  change mapTensorId ((L π).comp K) Unit _ = mapTensorId (K'.comp (L π)) Unit _
  rw [hcomm]

end QKD.BB84.Model
