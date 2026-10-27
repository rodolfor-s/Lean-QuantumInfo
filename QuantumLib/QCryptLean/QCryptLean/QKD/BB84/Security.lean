import QCryptLean.QKD.BB84.Chronology
import QCryptLean.QKD.BB84.Security.AEP
import QCryptLean.QKD.BB84.Security.BellRenyi

/-!
# Security of memory-free BB84

`QKD.Protocol.IsSecure` combines a bound on the normalized diamond distance between the real
protocol and its ideal key resource with classicality of both accepted key registers. The
comparison retains the public transcript and abort output and allows arbitrary reference systems.
It uses the full output interface of Christandl–König–Renner, arXiv:0809.3019, Theorem 1 and
Lemma 1, rather than the Alice-key marginal criterion of Nahar et al., arXiv:2403.11851,
lines 394–400.

The main theorem, `QKD.BB84.Parameters.isSecure_of_bellRenyiConditions`, proves security at
`Parameters.bellRenyiBudget` under `Parameters.BellRenyiConditions`. It requires a
translation-equivariant error-correction scheme and allows a free privacy-amplification error,
Rényi offset and phase-error deviation. Its Bell-symmetric postselection factor is
`C(sifted + 3, 3)`, and its entropy penalty uses Dupuis–Fawzi, arXiv:1805.11652, Corollary IV.2.
Use this theorem when the scheme satisfies `ECScheme.IsTranslationEquivariant` and the chosen
parameters satisfy `FiniteKey.BellRenyiKeyRate`.

`QKD.BB84.Parameters.isSecure_of_aepConditions` proves security at `Parameters.aepBudget` under
`Parameters.AEPConditions`, with no equivariance assumption on error correction. It uses
`FiniteKey.AEPKeyRate`, the postselection factor `C(sifted + 15, 15)` and an asymptotic
equipartition bound. Its analysis follows Nahar et al., arXiv:2403.11851, Theorem 3, Appendix B
and Section V.C, and Renner, arXiv:quant-ph/0512258v2, Section 6.5. Use it when its key-rate
condition holds, including for schemes without translation equivariance. The two theorems have
different assumptions and budgets; neither implies the other. Both apply to `Parameters.protocol`
through the same reduction from the executable program to `Parameters.modelDistance`.

`QCryptLean.QKD.BB84.Comparison.KeyLengthGap` compares the Bell–Rényi key length with the
Bell-symmetric lift of Tupkary, Tan and Lütkenhaus, arXiv:2311.01600, at matching protocol
parameters and error-correction assumptions.
-/
