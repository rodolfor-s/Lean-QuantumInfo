import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.Uniform
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Transcript
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic

/-! # Uniform -/


open scoped Matrix

open Quantum.Operators (Op)

namespace LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Program

variable [SystemPresentation P] {End : MultipartiteSystem P → Type 1}

/-- A complete uniform-output program supplies a transcript of its announcement word. -/
theorem nonempty_transcript {R S : MultipartiteSystem P} [Nonempty R.total] {T : TList}
    (p : Program R End) (h : p.boundary = Boundary.uniform S T) : Nonempty (Transcript T) :=
  p.nonempty_exit.map ((Equiv.cast (congrArg Boundary.Exit h)).trans
    (Boundary.uniformExitEquiv S T))

/-- Reindex the native denotation of a uniform-boundary program into final-register and transcript
coordinates.

This is only the coordinate presentation of the finite public measurement-history tree from
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2: every public history has the
same final multipartite system `S`, so `Boundary.uniformSpaceEquiv` identifies the native dependent
sum with `S.total × Transcript T`. -/
noncomputable def uniformDenote {R S : MultipartiteSystem P} {T : TList}
    (p : Program R End) (h : p.boundary = Boundary.uniform S T) :
    Op R.total →ₗ[ℂ] Op (S.total × Transcript T) :=
  ((Matrix.reindexLinearEquiv ℂ ℂ ((Equiv.cast (congrArg Boundary.space h)).trans
    (Boundary.uniformSpaceEquiv S T)) ((Equiv.cast (congrArg Boundary.space h)).trans
    (Boundary.uniformSpaceEquiv S T))).toLinearMap).comp p.denote

/-- Uniform-output relabelling preserves the program's channel certificate. -/
theorem isChannel_uniformDenote {R S : MultipartiteSystem P} {T : TList}
    (p : Program R End) (h : p.boundary = Boundary.uniform S T) :
    Quantum.Channels.IsChannel (p.uniformDenote h) :=
  (Quantum.Channels.isChannel_reindex _).comp p.isChannel_denote

end Program
end LOCC
