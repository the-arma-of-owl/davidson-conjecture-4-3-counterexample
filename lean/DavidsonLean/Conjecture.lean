import DavidsonLean.Gamma
import DavidsonLean.NonInteger

/-!
# Davidson's Conjecture 4.3 is false

Paper §1: "a *direction parameter* is a unit complex number `α` … `α` is *noninteger* if
`a_d ≥ 2`, i.e. if `α` is not an algebraic integer.
**[D, Conjecture 4.3].** If `α` is an algebraic noninteger direction parameter, then
`χ(Γ_α) ≤ 3`."
-/

namespace Davidson

open Polynomial

/-- Davidson's Conjecture 4.3: every algebraic noninteger direction parameter `α`
(`‖α‖ = 1`, algebraic over `ℚ`, not integral over `ℤ`) has `χ(Γ_α) ≤ 3`. -/
def Conjecture43 : Prop :=
  ∀ α : ℂ, ‖α‖ = 1 → IsAlgebraic ℚ α → ¬ IsIntegral ℤ α → (Gamma α).chromaticNumber ≤ 3

/-- Every root of `f` is an algebraic noninteger direction parameter with `χ(Γ_α) ≥ 4`. -/
theorem root_counterexample (α : ℂ) (hα : aeval α Poly.f = 0) :
    ‖α‖ = 1 ∧ IsAlgebraic ℚ α ∧ ¬ IsIntegral ℤ α ∧ 4 ≤ (Gamma α).chromaticNumber :=
  ⟨(Poly.roots_on_circle α hα).1, isAlgebraic_of_root α hα, not_isIntegral α hα,
    four_le_chromaticNumber α hα⟩

/-- `f` has a complex root. -/
theorem exists_root_f : ∃ α : ℂ, aeval α Poly.f = 0 := by
  have hdeg : 0 < (Poly.f.map (algebraMap ℤ ℂ)).degree := by
    rw [degree_map_eq_of_injective (RingHom.injective_int _), degree_eq_natDegree f_ne_zero,
      Poly.f_natDegree]
    decide
  obtain ⟨α, hα⟩ := Complex.exists_root hdeg
  exact ⟨α, by rwa [IsRoot, eval_map_algebraMap] at hα⟩

/-- **Davidson's Conjecture 4.3 is false.** -/
theorem conjecture43_false : ¬ Conjecture43 := by
  intro h
  obtain ⟨α, hα⟩ := exists_root_f
  obtain ⟨h1, h2, h3, h4⟩ := root_counterexample α hα
  have := h4.trans (h α h1 h2 h3)
  exact absurd this (by decide)

end Davidson

#print axioms Davidson.root_counterexample
#print axioms Davidson.exists_root_f
#print axioms Davidson.conjecture43_false
