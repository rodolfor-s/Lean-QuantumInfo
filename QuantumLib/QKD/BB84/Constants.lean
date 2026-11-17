import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.NormNum

/-!
# BB84 protocol constants: signal dimension and error threshold

The two numeric constants fixed by the BB84 protocol itself (not by any particular security
analysis): the per-round Alice–Bob Hilbert-space dimension, and the conservative Shor–Preskill
security threshold. Both are protocol-level data, so they are homed here rather than in the
security-analysis `FiniteKey`.

## Main definitions
- `signalDim`: per-round Alice-Bob Hilbert-space dimension for BB84.
- `errorThreshold`: conservative lower bound on the BB84 security threshold (11% for symmetric
  errors).

## Main statements
- `signalDim_pow_neZero`: the `n`-fold BB84 signal dimension is nonzero.
- `errorThreshold_lt_half`: the security threshold is less than `1/2`.
-/

section

namespace QKD.BB84

/-- Per-round Alice-Bob Hilbert-space dimension for BB84. -/
abbrev signalDim : ℕ := 4

instance : NeZero signalDim := by
  dsimp [signalDim]
  infer_instance

/-- The n-fold BB84 signal dimension is nonzero. -/
lemma signalDim_pow_neZero (n : ℕ) : NeZero (signalDim ^ n) := by
  change NeZero (4 ^ n)
  infer_instance

/-- Conservative lower bound on the BB84 security threshold (11% for symmetric errors).

    This is a provable security threshold: for any error rate e < 0.11, the key
    rate `1 - 2H₂(e)` is strictly positive. The value 0.11 is NOT the exact
    Shor-Preskill root where `keyRate = 0`; the true zero lies slightly above 0.11.
    The proof `binaryEntropyBits_lt_half_of_lt_011` establishes H₂(0.11) < 1/2,
    which gives `keyRate(0.11) > 0`. -/
def errorThreshold : ℝ := 0.11

/-- The security threshold is less than 1/2 (required for the entropy bounds). -/
theorem errorThreshold_lt_half : errorThreshold < 1/2 := by
  unfold errorThreshold; norm_num

end QKD.BB84

end
