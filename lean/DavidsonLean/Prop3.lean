import DavidsonLean.Parse
import DavidsonLean.CertData

/-!
# Proposition 3

`prop3_of_check` (kernel-checked, in `Checker.lean`) reduces the statement to the claim that the
checker accepts the parsed certificate.  That claim is established by `native_decide`, i.e. by
running compiled code; `native_decide` records it as an auxiliary axiom (see `#print axioms` below).
-/

namespace Davidson

/-- the certificate tree, parsed from the embedded token stream -/
def cert : Cert := Parse.parseCert certStr

theorem cert_ok : checkRoot cert = true := by native_decide

/-- **Proposition 3** (K = 79): there is no `σ ∈ [-1,1]^80` with all 68 sums
`τ_j = ∑_{i=0}^{12} aᵢ σ_{i+j}` odd multiples of `3`. -/
theorem prop3 : ¬ ∃ σ : Fin 80 → ℝ, (∀ i, |σ i| ≤ 1) ∧
    ∀ j : Fin 68, ∃ m : ℤ,
      ∑ i : Fin 13, (a i : ℝ) * σ ⟨i.val + j.val, by omega⟩ = 3 * (2 * m + 1) :=
  prop3_of_check cert cert_ok

end Davidson

#print axioms Davidson.prop3
#print axioms Davidson.prop3_of_check
#print axioms Davidson.cert_ok
