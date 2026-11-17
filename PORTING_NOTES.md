# Porting notes

## QCryptLean (Maor Ben-Shahar)

- **Source:** https://github.com/maorbenshahar/QCryptLean, commit `2eaa1067c4fb5b580c544c77b6286415b72e83fc` (HEAD of the local `ext/QCryptLean` clone; not yet cross-checked against the import commit `e996298`).
- **License:** Apache-2.0. The imported `LICENSE` and root module `QCryptLean.lean` were dropped in the relocation; both remain in `e996298`.
- **Toolchain:** source is Lean v4.34.1, QuantumLib is v4.33.0. Not yet ported.
- **Authors and accompanying paper:** TODO.

### Status

All 724 files relocated and their `import` lines rewritten; **not yet registered in `QuantumLib.lean` and not built**. `ForMathlib/Logic/Equiv/Fin/FiniteEmbedding.lean` was compiled alone as a smoke test: imports resolve, and the one error is `Set.equivOfEq` missing on 4.33.

### File moves

Old paths are relative to `QuantumLib/QCryptLean/QCryptLean/`, new ones to `QuantumLib/`. Sub-paths are kept unless noted.

| Old | New | Files |
|---|---|---|
| `Quantum/` | `ForPhyslib/QuantumInfo/` | 187 |
| `InfoTheory/{Postselection,QuantumLHL,Security}/` | `QKD/{Postselection,QuantumLHL,Security}/` | 39 |
| rest of `InfoTheory/` | `Entropy/` | 109 |
| `LOCC/` | `LOCC/` | 38 |
| `QKD/` | `QKD/` | 177 |
| `Math/{Algebra,Analysis,Combinatorics,LinearAlgebra,Logic,Probability}/` | `ForMathlib/<same>/` | 170 (all `Math/` rows) |
| `Math/SpectralTheory/` | `ForMathlib/Analysis/Matrix/SpectralTheory/` | |
| `Math/ClassicalEntropy/` | `ForMathlib/InformationTheory/ClassicalEntropy/` | |
| `Math/CodingTheory/` | `ForMathlib/InformationTheory/Coding/` | |
| `Math/Concentration/` | `ForMathlib/Probability/Concentration/` | |
| `Math/FiniteEmbedding{,/}` | `ForMathlib/Logic/Equiv/Fin/FiniteEmbedding{,/}` | |
| `Math/CodingTheory/HashFamily`, `Math/Concentration/PrivacyAmplification` | `ForCslib/Crypto/` | 2 |
| `Math/Combinatorics/{BellSymmetricDim,DeFinettiPrefactor}` | `QKD/Postselection/` | 2 |

`ForPhyslib/QuantumInfo/` is QCryptLean's own state/channel/metric layer and is **still on its own types**; it must be restated on `MState`/`CPTPOp`/`HermitianMat` (dev-plan E4/E5) before upstreaming.

### Import changes

Only `import` lines were rewritten: 5083 of the 5568 imports in the 724 files (the other 485 are `Mathlib`/`Batteries`/`Lean`, untouched). The rewrite is a per-file module-name map, so it follows the table above:

| Old import prefix | New import prefix |
|---|---|
| `QCryptLean.Quantum.` | `QuantumLib.ForPhyslib.QuantumInfo.` (1982 imports) |
| `QCryptLean.QKD.` | `QuantumLib.QKD.` (1163) |
| `QCryptLean.InfoTheory.{Postselection,QuantumLHL,Security}.` | `QuantumLib.QKD.{Postselection,QuantumLHL,Security}.` (109) |
| `QCryptLean.InfoTheory.` (rest) | `QuantumLib.Entropy.` (566) |
| `QCryptLean.LOCC.` | `QuantumLib.LOCC.` (471) |
| `QCryptLean.Math.{Algebra,Analysis,Combinatorics,LinearAlgebra,Logic,Probability}.` | `QuantumLib.ForMathlib.<same>.` |
| `QCryptLean.Math.SpectralTheory.` | `QuantumLib.ForMathlib.Analysis.Matrix.SpectralTheory.` |
| `QCryptLean.Math.ClassicalEntropy.` | `QuantumLib.ForMathlib.InformationTheory.ClassicalEntropy.` |
| `QCryptLean.Math.CodingTheory.` | `QuantumLib.ForMathlib.InformationTheory.Coding.` |
| `QCryptLean.Math.Concentration.` | `QuantumLib.ForMathlib.Probability.Concentration.` |
| `QCryptLean.Math.FiniteEmbedding` | `QuantumLib.ForMathlib.Logic.Equiv.Fin.FiniteEmbedding` |
| `QCryptLean.Math.CodingTheory.HashFamily`, `…Concentration.PrivacyAmplification` | `QuantumLib.ForCslib.Crypto.{HashFamily,PrivacyAmplification}` |
| `QCryptLean.Math.Combinatorics.{BellSymmetricDim,DeFinettiPrefactor}` | `QuantumLib.QKD.Postselection.{BellSymmetricDim,DeFinettiPrefactor}` (23) |

The `Math` rows account for 792 imports (769 into `ForMathlib`/`ForCslib`, 23 into `QKD`).

Namespaces, declaration names and docstrings (some still mention `QCryptLean.…` module names) are untouched.
