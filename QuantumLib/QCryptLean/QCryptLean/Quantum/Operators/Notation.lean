import QCryptLean.Quantum.Operators.BraKet

/-! # Scoped Dirac, adjoint, and tensor notation -/
namespace Quantum.Operators

/-- Matrix conjugate transpose in the adjoint scope. -/
scoped[QuantumAdjoint] postfix:1024 "†" => Matrix.conjTranspose

/-- Type class for things that can be converted to a Bra.
    - Ket X → Bra X via .dag
    - Bra X → Bra X via identity -/
class ToBra (α : Type*) (X : outParam (Type*)) where
  /-- Convert a value to its bra representation for Dirac notation. -/
  toBra : α → Bra X

/-- Type class for things that can be converted to a Ket.
    - Ket X → Ket X via identity
    - Bra X → Ket X via .dag -/
class ToKet (α : Type*) (X : outParam (Type*)) where
  /-- Convert a value to its ket representation for Dirac notation. -/
  toKet : α → Ket X

-- Instances for Ket
instance instToKetKet {X : Type*} : ToKet (Ket X) X where
  toKet := id

instance instToBraKet {X : Type*} : ToBra (Ket X) X where
  toBra := Ket.dag

-- Instances for Bra
instance instToBraBra {X : Type*} : ToBra (Bra X) X where
  toBra := id

instance instToKetBra {X : Type*} : ToKet (Bra X) X where
  toKet := Bra.dag

-- Simp lemmas to reduce type class applications
@[simp] theorem ToKet.toKet_ket {X : Type*} (ψ : Ket X) : ToKet.toKet ψ = ψ := rfl
@[simp] theorem ToBra.toBra_bra {X : Type*} (β : Bra X) : ToBra.toBra β = β := rfl
@[simp] theorem ToKet.toKet_bra {X : Type*} (β : Bra X) : ToKet.toKet β = β.dag := rfl
@[simp] theorem ToBra.toBra_ket {X : Type*} (ψ : Ket X) : ToBra.toBra ψ = ψ.dag := rfl

-- ============================================================================
-- Section 14: Standard Basis Notation
-- ============================================================================

with_weak_namespace _root_.QuantumDirac
/-- Expand a Dirac ket argument, interpreting only literal `0` and `1` as qubit basis states.
Other arguments are converted by `Quantum.Operators.ToKet.toKet`. -/
def ketArg (x : Lean.TSyntax `term) : Lean.MacroM (Lean.TSyntax `term) :=
  match x with
  | `($n:num) =>
    match n.getNat with
    | 0 => `(Quantum.Operators.stdKet (0 : Fin 2))
    | 1 => `(Quantum.Operators.stdKet (1 : Fin 2))
    | _ =>
      Lean.Macro.throwErrorAt x
        "Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states"
  | _ => `(Quantum.Operators.ToKet.toKet $x)

/-- Computational-basis zero qubit ket, in `QuantumDirac`, written without internal spaces. -/
scoped[QuantumDirac] notation "|0⟩" => Quantum.Operators.stdKet (0 : Fin 2)

/-- Computational-basis one qubit ket, in `QuantumDirac`, written without internal spaces. -/
scoped[QuantumDirac] notation "|1⟩" => Quantum.Operators.stdKet (1 : Fin 2)

open scoped QuantumDirac in
/-- Computational-basis zero qubit bra, in `QuantumDirac`, written without internal spaces. -/
scoped[QuantumDirac] notation "⟨0|" => Quantum.Operators.Ket.dag |0⟩

open scoped QuantumDirac in
/-- Computational-basis one qubit bra, in `QuantumDirac`, written without internal spaces. -/
scoped[QuantumDirac] notation "⟨1|" => Quantum.Operators.Ket.dag |1⟩

/-- Dirac bra in `QuantumDirac`: `ToBra.toBra` keeps bras and takes the dagger of kets.
Literal `0` and `1` denote qubit basis bras, with optional whitespace.
Other numerals are rejected. -/
scoped[QuantumDirac] notation "⟨" x "|" => Quantum.Operators.ToBra.toBra x

with_weak_namespace _root_.QuantumDirac
/-- Dirac ket in `QuantumDirac`: `ToKet.toKet` keeps kets and takes the dagger of bras.
Literal `0` and `1` denote qubit basis kets, with optional whitespace.
Other numerals are rejected. -/
scoped syntax:max (name := ket) atomic("|" term "⟩") : term

open scoped QuantumDirac in
with_weak_namespace _root_.QuantumDirac
scoped macro_rules
  | `(| $x:term ⟩) => ketArg x

with_weak_namespace _root_.QuantumDirac
/-- A literal qubit bra in `QuantumDirac`, allowing whitespace and only the labels `0` and `1`. -/
scoped macro:max (name := literalBra) (priority := high) "⟨" n:num "|" : term => do
  let ket ← ketArg ⟨n.raw⟩
  `(Quantum.Operators.Ket.dag $ket)


end Quantum.Operators

namespace QuantumDirac

/-!
## Tensor-state notation

Comma kets convert each argument with `Quantum.Operators.ToKet.toKet` and tensor from left
to right. Comma bras take the dagger of that ket. Literal `0` and `1` denote qubit basis
states; other basis states must be written explicitly with `Quantum.Operators.stdKet`.
Neither notation requires the tensor or adjoint scope.
-/

private def tensorKetArgs (x : Lean.TSyntax `term) (xs : Array (Lean.TSyntax `term)) :
    Lean.MacroM (Lean.TSyntax `term) := do
  let mut result ← ketArg x
  for y in xs do
    let ket ← ketArg y
    result ← `(Quantum.Operators.Ket.kronecker $result $ket)
  return result

/-- A left-associated tensor product of at least two states, converted to kets, in `QuantumDirac`.
Literal arguments must be `0` or `1`; other basis states use
`Quantum.Operators.stdKet` explicitly. -/
scoped syntax:max (name := _root_.QuantumDirac.tensorKet)
  atomic("|" term "," term,+ "⟩") : term

scoped macro_rules
  | `(| $x:term, $xs:term,* ⟩) => tensorKetArgs x xs.getElems

/-- The bra of a left-associated tensor product of at least two states, in `QuantumDirac`.
Literal arguments must be `0` or `1`; other basis states use
`Quantum.Operators.stdKet` explicitly. -/
scoped syntax (name := _root_.QuantumDirac.tensorBra) "⟨" term "," term,+ "|" : term

scoped macro_rules
  | `(⟨ $x:term, $xs:term,* |) => do
    let ket ← tensorKetArgs x xs.getElems
    `(Quantum.Operators.Ket.dag $ket)

end QuantumDirac

@[inherit_doc Quantum.Operators.Ket.kronecker]
scoped[QuantumTensor] infixl:100 " ⊗ " => Quantum.Operators.Ket.kronecker
@[inherit_doc Quantum.Operators.Bra.kronecker]
scoped[QuantumTensor] infixl:100 " ⊗ " => Quantum.Operators.Bra.kronecker
@[inherit_doc Matrix.kronecker]
scoped[QuantumTensor] infixl:100 " ⊗ " => Matrix.kronecker
