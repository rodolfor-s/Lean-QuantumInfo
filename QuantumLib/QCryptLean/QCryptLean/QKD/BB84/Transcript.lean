import QCryptLean.LOCC.Transcript
import QCryptLean.QKD.BB84.ClassicalData

/-!
# BB84 announcement order

The transcript word records each round’s two public bits in execution order.
-/

namespace QKD.BB84.PE
open LOCC

open LOCC.Transcript

/-- The transcript word of `r` parameter-estimation rounds followed by `T`. -/
def transcriptWord (r : ℕ) (T : TList) : TList :=
  match r with
  | 0 => T
  | r + 1 => .cons (Fin 2) (.cons (Fin 2) (transcriptWord r T))

end QKD.BB84.PE
