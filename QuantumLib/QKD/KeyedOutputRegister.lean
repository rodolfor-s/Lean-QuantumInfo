import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

/-!
# Flagged two-key registers

The analytical output retains two full bit-string key registers, a Boolean acceptance
flag, and the public or residual register. The abort sector retains the entire key
space; compressing it to a single abort symbol is separate protocol postprocessing.
-/

namespace QKD

/-- Two keys, an acceptance flag, and a retained register. -/
abbrev KeyedOutput (ℓ : ℕ) (Public : Type*) :=
  ((Fin ℓ → Fin 2) × (Fin ℓ → Fin 2)) × (Bool × Public)

/-- Append a public factor by reassociating it past the keys and flag. -/
def KeyedOutput.prodEquiv (ℓ : ℕ) (D : Type*) (E : Type*) :
    KeyedOutput ℓ D × E ≃ KeyedOutput ℓ (D × E) :=
  (Equiv.prodAssoc _ _ _).trans ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _))

end QKD
