import QCryptLean.LOCC.Transcript
import QCryptLean.QKD.BB84.Transcript

/-!
# Raw decoding of the parameter-estimation and fused public cells

After `r` interleaved parameter-estimation rounds, each contributing one Bob cell and then one
Alice cell of type `Fin 2`, Alice writes one fused cell of type `A`; this is the word
`QKD.BB84.PE.transcriptWord r (.cons (A) .nil)`.  `preDecisionRawEquiv` decodes it
into a `PreDecisionRaw r A`: Bob's and Alice's raw outcome strings, indexed in announcement
order, and the raw fused outcome.  No outcome is interpreted here; the semantic readers apply
the chosen finite enumeration afterwards.

The record depends only on `r` and `A`.  The physical tail word `QKD.BB84.classicalTailWord` is
this word at its round count and fused alphabet.
Their common PE/fused part is decoded here.

Each cell is a public classical outcome of a local instrument in a finite-round LOCC tree in the
sense of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II; the cell order
and outcome encoding are this library's.
-/

noncomputable section

namespace QKD.BB84

open LOCC
open QKD.BB84.PE

/-- Raw public cells after `r` interleaved PE rounds and one fused announcement.

The two PE functions retain the source instrument outcomes. In particular, this structure does
not yet apply the chosen finite enumeration. -/
structure PreDecisionRaw (r : ℕ) (A : Type) where
  /-- Bob's raw observed PE outcome at each chronological round. -/
  bobPERaw : Fin r → Fin 2
  /-- Alice's raw observed PE outcome at each chronological round. -/
  alicePERaw : Fin r → Fin 2
  /-- Alice's raw observed fused seed/tag/syndrome outcome. -/
  fusedRaw : A

/-- Decode the zero-round transcript into its two empty PE functions and fused cell. -/
private def preDecisionRawZeroEquiv (A : Type) [Fintype A] [DecidableEq A] :
    Transcript (.cons (A) .nil) ≃ PreDecisionRaw 0 A where
  toFun t :=
    { bobPERaw := Fin.elim0
      alicePERaw := Fin.elim0
      fusedRaw := t.1 }
  invFun d := ⟨d.fusedRaw, ()⟩
  left_inv t := by
    rcases t with ⟨z, ⟨⟩⟩
    rfl
  right_inv d := by
    rcases d with ⟨bs, as, z⟩
    have hbs : (Fin.elim0 : Fin 0 → Fin 2) = bs := Subsingleton.elim _ _
    have has : (Fin.elim0 : Fin 0 → Fin 2) = as := Subsingleton.elim _ _
    cases hbs
    cases has
    rfl

/-- Prepend one raw Bob cell and then one raw Alice cell to a decoded PE record.

Both functions are built with `Fin.cons`: the new chronological round is index `0`, while every
previous index becomes `j.succ`. -/
private def preDecisionRawSuccEquiv (r : ℕ) (A : Type) :
    Fin 2 × (Fin 2 × PreDecisionRaw r A) ≃ PreDecisionRaw (r + 1) A where
  toFun t :=
    { bobPERaw := Fin.cons t.1 t.2.2.bobPERaw
      alicePERaw := Fin.cons t.2.1 t.2.2.alicePERaw
      fusedRaw := t.2.2.fusedRaw }
  invFun d :=
    ⟨d.bobPERaw 0,
      ⟨d.alicePERaw 0,
        { bobPERaw := Fin.tail d.bobPERaw
          alicePERaw := Fin.tail d.alicePERaw
          fusedRaw := d.fusedRaw }⟩⟩
  left_inv t := by
    rcases t with ⟨b, ⟨a, d⟩⟩
    rcases d with ⟨bs, as, z⟩
    simp
  right_inv d := by
    rcases d with ⟨bs, as, z⟩
    simp

/-- Decode the raw PE/fused transcript in chronological order.

At a successor the transcript is `(b, (a, t))`: Bob's new raw cell is prepended to
`bobPERaw`, Alice's is prepended to `alicePERaw`, and the recursively decoded fused cell is
unchanged. -/
def preDecisionRawEquiv (r : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Transcript (transcriptWord r (.cons (A) .nil)) ≃ PreDecisionRaw r A :=
  match r with
  | 0 => preDecisionRawZeroEquiv A
  | r + 1 =>
      ((Equiv.prodCongr (Equiv.refl (Fin 2))
        (Equiv.prodCongr (Equiv.refl (Fin 2)) (preDecisionRawEquiv r A))).trans
        (preDecisionRawSuccEquiv r A))

/-- The successor decoder literally prepends Bob's cell first and Alice's cell second.

This is the Bob-then-Alice announcement order of the parameter-estimation recursion; it rules out
a `Fin.snoc` interpretation of the chronological indices. -/
theorem preDecisionRawEquiv_succ
    (r : ℕ) (A : Type) [Fintype A] [DecidableEq A] (b a : Fin 2)
    (t : Transcript (transcriptWord r (.cons (A) .nil))) :
    preDecisionRawEquiv (r + 1) A (b, (a, t)) =
      { bobPERaw := Fin.cons b (preDecisionRawEquiv r A t).bobPERaw
        alicePERaw := Fin.cons a (preDecisionRawEquiv r A t).alicePERaw
        fusedRaw := (preDecisionRawEquiv r A t).fusedRaw } := by
  rfl

end QKD.BB84
