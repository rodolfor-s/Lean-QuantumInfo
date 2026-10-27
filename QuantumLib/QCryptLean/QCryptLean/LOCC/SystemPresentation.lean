import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty

/-! # System Presentation -/


open Quantum.Operators (Op)

namespace LOCC

/-- Produce a computational successor presentation without changing the register update. -/
class SystemPresentation (P : Type) [Fintype P] [DecidableEq P] where
  /-- The updated system supplied to the next program node. -/
  update (R : MultipartiteSystem P) (actor : P) (Output : Type)
    [Fintype Output] [DecidableEq Output] : MultipartiteSystem P
  /-- The presentation denotes the ordinary register update. -/
  update_eq_set (R : MultipartiteSystem P) (actor : P) (Output : Type)
    [Fintype Output] [DecidableEq Output] :
    update R actor Output = R.set actor Output

/-- General party types keep the ordinary register update. -/
instance (priority := low) instSystemPresentation (P : Type) [Fintype P] [DecidableEq P] :
    SystemPresentation P where
  update := MultipartiteSystem.set
  update_eq_set _ _ _ := rfl

/-- Two-party updates construct the natural system directly from the surviving registers. -/
instance TwoParty.instSystemPresentation : SystemPresentation TwoParty.Party where
  update R actor Output := match actor with
    | .alice => TwoParty.system Output (R.reg .bob)
    | .bob => TwoParty.system (R.reg .alice) Output
  update_eq_set R actor Output := by
    intro _ _
    cases actor <;> apply MultipartiteSystem.ext' <;> funext p <;> cases p <;> rfl

end LOCC
