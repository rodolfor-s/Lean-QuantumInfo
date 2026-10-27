import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor

/-! # Classical Coarsening -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.QuantumLHL

end InfoTheory.QuantumLHL

namespace InfoTheory.SmoothMinEntropy

end InfoTheory.SmoothMinEntropy

namespace InfoTheory.QuantumLHL

/-- Precompose the domain of a classical seeded hash family by a finite classical map. -/
def HashFamily.precomp {S X Y Z : Type*} (H : HashFamily S Y Z)
    (g : X → Y) : HashFamily S X Z where
  hash := fun s x => H.hash s (g x)
  seedFintype := H.seedFintype
  seedNonempty := H.seedNonempty
  outputFintype := H.outputFintype
  outputNonempty := H.outputNonempty

end InfoTheory.QuantumLHL

end -- noncomputable section
