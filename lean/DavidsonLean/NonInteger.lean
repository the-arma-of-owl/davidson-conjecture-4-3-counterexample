import DavidsonLean.Poly

namespace Davidson.NonInteger
open Polynomial

noncomputable def P : (ZMod 3)[X] := X ^ 6 + X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2

lemma P_natDegree : P.natDegree = 6 := by unfold P; compute_degree!
lemma P_monic : P.Monic := by unfold P; monicity!

lemma coeff_mul_range {R : Type*} [Semiring R] (p q : R[X]) (k : ℕ) :
    (p * q).coeff k = ∑ i ∈ Finset.range (k + 1), p.coeff i * q.coeff (k - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j)]

lemma no_factor (f g : (ZMod 3)[X]) (hf : f.Monic) (hg : g.Monic) (h : f * g = P)
    (d : ℕ) (hgd : g.natDegree = d) (hd1 : 1 ≤ d) (hd3 : d ≤ 3) : False := by
  have hfd : f.natDegree = 6 - d := by
    have := hf.natDegree_mul hg
    rw [h, P_natDegree] at this; omega
  have hk : ∀ k, (f * g).coeff k = P.coeff k := fun k => by rw [h]
  have fz : ∀ j, 6 - d < j → f.coeff j = 0 := fun j hj => coeff_eq_zero_of_natDegree_lt (by omega)
  have gz : ∀ j, d < j → g.coeff j = 0 := fun j hj => coeff_eq_zero_of_natDegree_lt (by omega)
  have f1 : f.coeff (6 - d) = 1 := by rw [← hfd]; exact hf
  have g1 : g.coeff d = 1 := by rw [← hgd]; exact hg
  have e0 := hk 0
  have e1 := hk 1
  have e2 := hk 2
  have e3 := hk 3
  have e4 := hk 4
  have e5 := hk 5
  simp only [coeff_mul_range, Finset.sum_range_succ, Finset.sum_range_zero, P] at e0 e1 e2 e3 e4 e5
  obtain rfl | rfl | rfl : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  · simp [coeff_X_pow, f1, g1, gz] at e0 e1 e2 e3 e4 e5
    revert e0 e1 e2 e3 e4 e5
    generalize f.coeff 0 = a0; generalize f.coeff 1 = a1; generalize f.coeff 2 = a2
    generalize f.coeff 3 = a3; generalize f.coeff 4 = a4; generalize g.coeff 0 = b0
    revert a0 a1 a2 a3 a4 b0
    decide
  · simp [coeff_X_pow, f1, g1, fz, gz] at e0 e1 e2 e3 e4 e5
    revert e0 e1 e2 e3 e4 e5
    generalize f.coeff 0 = a0; generalize f.coeff 1 = a1; generalize f.coeff 2 = a2
    generalize f.coeff 3 = a3; generalize g.coeff 0 = b0; generalize g.coeff 1 = b1
    revert a0 a1 a2 a3 b0 b1
    decide
  · simp [coeff_X_pow, f1, g1, fz, gz] at e0 e1 e2 e3 e4 e5
    revert e0 e1 e2 e3 e4 e5
    generalize f.coeff 0 = a0; generalize f.coeff 1 = a1; generalize f.coeff 2 = a2
    generalize g.coeff 0 = b0; generalize g.coeff 1 = b1; generalize g.coeff 2 = b2
    revert a0 a1 a2 b0 b1 b2
    decide

theorem P_irreducible : Irreducible P := by
  rw [P_monic.irreducible_iff_natDegree']
  refine ⟨fun h => by simpa [h] using P_natDegree, fun f g hf hg h hmem => ?_⟩
  rw [P_natDegree, Finset.mem_Ioc] at hmem
  exact no_factor f g hf hg h _ rfl (by omega) (by omega)

lemma F_map : Poly.F.map (Int.castRingHom (ZMod 3)) * C 2 = P := by
  have h3 : (3 : (ZMod 3)[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero (ZMod 3)[X] 3
  simp only [Poly.F, P, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_X, Polynomial.map_ofNat, Polynomial.map_one]
  rw [show (C 2 : (ZMod 3)[X]) = 2 from rfl]
  linear_combination (X ^ 6 + X ^ 5 - 8 * X ^ 4 - 8 * X ^ 3 + 8 * X ^ 2 + 8 * X) * h3

lemma F_leadingCoeff : Poly.F.leadingCoeff = 2 := by
  rw [leadingCoeff, Poly.F_natDegree]; simp [Poly.F, coeff_X_pow, coeff_X, coeff_one]

lemma F_coeff_zero : Poly.F.coeff 0 = 1 := by simp [Poly.F, coeff_X_pow, coeff_X]

/-- no root of `F` is integral over `ℤ` -/
theorem F_root_not_integral (y : ℂ) (hy : aeval y Poly.F = 0) : ¬ IsIntegral ℤ y := by
  intro hint
  set g := minpoly ℤ y
  have hgm : g.Monic := minpoly.monic hint
  have hgpos : 0 < g.natDegree := minpoly.natDegree_pos hint
  obtain ⟨h, hF⟩ := minpoly.isIntegrallyClosed_dvd hint hy
  have hF0 : Poly.F ≠ 0 := fun h0 => by simpa [h0] using Poly.F_natDegree
  have hh0 : h ≠ 0 := by rintro rfl; simp at hF; exact hF0 hF
  -- reduce mod 3
  set φ := Int.castRingHom (ZMod 3)
  have hP : P = g.map φ * (h.map φ * C 2) := by
    rw [← F_map, hF, Polynomial.map_mul, mul_assoc]
  have hgu : ¬ IsUnit (g.map φ) := by
    rw [(hgm.map φ).isUnit_iff]
    intro h1
    have := hgm.natDegree_map φ
    rw [h1, natDegree_one] at this; omega
  have hu : IsUnit (h.map φ * C 2) :=
    (P_irreducible.isUnit_or_isUnit hP).resolve_left hgu
  have hd0 : (h.map φ * C 2).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  have hg6 : g.natDegree = 6 := by
    have hne : h.map φ * C 2 ≠ 0 := hu.ne_zero
    have := natDegree_mul (hgm.map φ).ne_zero hne
    rw [← hP, P_natDegree, hd0, hgm.natDegree_map] at this; omega
  have hhd : h.natDegree = 0 := by
    have := natDegree_mul hgm.ne_zero hh0
    rw [← hF, Poly.F_natDegree, hg6] at this; omega
  rw [eq_C_of_natDegree_eq_zero hhd] at hF
  have hc : h.coeff 0 = 2 := by
    have := congrArg leadingCoeff hF
    rw [F_leadingCoeff, leadingCoeff_mul, hgm.leadingCoeff, leadingCoeff_C] at this
    simpa using this.symm
  have := congrArg (fun p : ℤ[X] => p.coeff 0) hF
  simp only [coeff_mul_C, F_coeff_zero, hc] at this
  omega


end Davidson.NonInteger

namespace Davidson

open Polynomial ComplexConjugate

/-- **Target 1.** No root of `f` is an algebraic integer. -/
theorem not_isIntegral (α : ℂ) (hα : Polynomial.aeval α Poly.f = 0) : ¬ IsIntegral ℤ α := by
  intro hint
  have hn : ‖α‖ = 1 := (Poly.roots_on_circle α hα).1
  have h0 : α ≠ 0 := by rintro rfl; simp at hn
  -- `conj α` is integral, and `conj α = α⁻¹` on the unit circle
  have hconj : IsIntegral ℤ (conj α) := by
    simpa using hint.map (starRingEnd ℂ).toIntAlgHom
  have hinv : α⁻¹ = conj α := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
  have hy : IsIntegral ℤ (α + α⁻¹) := by rw [hinv]; exact hint.add hconj
  -- `α + α⁻¹` is a root of `F`
  have hF : aeval (α + α⁻¹) Poly.F = 0 := by
    rw [Poly.trace_identity α h0] at hα
    exact (mul_eq_zero.1 hα).resolve_left (pow_ne_zero _ h0)
  exact NonInteger.F_root_not_integral _ hF hy

theorem f_ne_zero : Poly.f ≠ 0 := fun h => by simpa [h] using Poly.f_natDegree

/-- Every root of `f` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_root (α : ℂ) (hα : Polynomial.aeval α Poly.f = 0) : IsAlgebraic ℚ α := by
  refine ⟨Poly.f.map (algebraMap ℤ ℚ), ?_, by rw [aeval_map_algebraMap]; exact hα⟩
  exact (Polynomial.map_ne_zero_iff (algebraMap ℤ ℚ).injective_int).2 f_ne_zero

end Davidson

#print axioms Davidson.NonInteger.P_irreducible
#print axioms Davidson.NonInteger.F_root_not_integral
#print axioms Davidson.not_isIntegral
#print axioms Davidson.isAlgebraic_of_root
