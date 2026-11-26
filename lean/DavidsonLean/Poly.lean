import DavidsonLean.Checker

/-!
# Facts about the polynomial `f` (all kernel-checked, no `native_decide`)

* `f_coeff`, `f_natDegree`, `f_leadingCoeff`, `f_eval_one`, `f_eval_zero`
* `trace_identity`: `f(x) = x^6 F(x + x⁻¹)` for `x ≠ 0`, with `F = y(y²-4)(y+1)(2y²-3)+1`
* `F_six_real_roots`: `F` has six distinct real roots in `(-2,2)`
* `roots_on_circle`: every complex root of `f` has norm `1` and is not real.
-/

namespace Davidson.Poly

open Polynomial

/-- `f(x) = 2x¹² + 2x¹¹ + x¹⁰ - x⁹ - 2x⁸ - x⁷ - x⁶ - x⁵ - 2x⁴ - x³ + x² + 2x + 2` -/
noncomputable def f : ℤ[X] :=
  2 * X ^ 12 + 2 * X ^ 11 + X ^ 10 - X ^ 9 - 2 * X ^ 8 - X ^ 7 - X ^ 6 - X ^ 5 - 2 * X ^ 4 - X ^ 3 +
    X ^ 2 + 2 * X + 2

/-- the trace polynomial `F(y) = 2y⁶ + 2y⁵ - 11y⁴ - 11y³ + 12y² + 12y + 1` -/
noncomputable def F : ℤ[X] :=
  2 * X ^ 6 + 2 * X ^ 5 - 11 * X ^ 4 - 11 * X ^ 3 + 12 * X ^ 2 + 12 * X + 1

/-- `f = ∑ aᵢ Xⁱ` with the coefficient vector `a` used in `prop3` -/
theorem f_eq_sum : f = ∑ i : Fin 13, C (Davidson.a i) * X ^ (i : ℕ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Davidson.a]
  simp [f]
  ring

theorem f_coeff (i : Fin 13) : f.coeff i = Davidson.a i := by
  fin_cases i <;> simp [f, coeff_X_pow, coeff_X, Davidson.a]

/-- `f` is palindromic: `aᵢ = a₁₂₋ᵢ` -/
theorem a_palindromic : ∀ i : Fin 13, Davidson.a i = Davidson.a i.rev := by decide

theorem f_natDegree : f.natDegree = 12 := by
  unfold f; compute_degree!

theorem f_leadingCoeff : f.leadingCoeff = 2 := by
  rw [leadingCoeff, f_natDegree]
  exact f_coeff 12

theorem f_eval_one : f.eval 1 = 1 := by simp [f]

theorem f_eval_zero : f.eval 0 = 2 := by simp [f]

theorem F_factor : F = X * (X ^ 2 - 4) * (X + 1) * (2 * X ^ 2 - 3) + 1 := by
  unfold F; ring

theorem F_natDegree : F.natDegree = 6 := by
  unfold F; compute_degree!

/-- trace identity: `f(x) = x⁶ F(x + x⁻¹)` in any field -/
theorem trace_identity {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    aeval x f = x ^ 6 * aeval (x + x⁻¹) F := by
  simp only [f, F, map_add, map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
  field_simp
  ring

/-- `F` as a real function -/
def Fr (y : ℝ) : ℝ := 2 * y ^ 6 + 2 * y ^ 5 - 11 * y ^ 4 - 11 * y ^ 3 + 12 * y ^ 2 + 12 * y + 1

lemma Fr_cont : Continuous Fr := by unfold Fr; fun_prop

lemma root_between (p q : ℝ) (hpq : p ≤ q) (h : (0 < Fr p ∧ Fr q < 0) ∨ (Fr p < 0 ∧ 0 < Fr q)) :
    ∃ r ∈ Set.Ioo p q, Fr r = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hpq Fr_cont.continuousOn ⟨h2, h1⟩
    exact ⟨r, hr, hr0⟩
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hpq Fr_cont.continuousOn ⟨h1, h2⟩
    exact ⟨r, hr, hr0⟩

/-- `F` has six real roots, separated by `-2 < -3/2 < -1 < -1/2 < 0 < 3/2 < 2`. -/
theorem F_six_real_roots : ∃ r : Fin 6 → ℝ, StrictMono r ∧ (∀ i, -2 < r i ∧ r i < 2) ∧
    ∀ i, Fr (r i) = 0 := by
  obtain ⟨r0, h0, e0⟩ := root_between (-2) (-3/2) (by norm_num) (by left; norm_num [Fr])
  obtain ⟨r1, h1, e1⟩ := root_between (-3/2) (-1) (by norm_num) (by right; norm_num [Fr])
  obtain ⟨r2, h2, e2⟩ := root_between (-1) (-1/2) (by norm_num) (by left; norm_num [Fr])
  obtain ⟨r3, h3, e3⟩ := root_between (-1/2) 0 (by norm_num) (by right; norm_num [Fr])
  obtain ⟨r4, h4, e4⟩ := root_between 0 (3/2) (by norm_num) (by left; norm_num [Fr])
  obtain ⟨r5, h5, e5⟩ := root_between (3/2) 2 (by norm_num) (by right; norm_num [Fr])
  simp only [Set.mem_Ioo] at h0 h1 h2 h3 h4 h5
  refine ⟨![r0, r1, r2, r3, r4, r5], ?_, ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
    fin_cases i <;> simp <;> linarith
  · intro i; fin_cases i <;> simp <;> constructor <;> linarith
  · intro i; fin_cases i <;> simpa

lemma aeval_F_ofReal (r : ℝ) : aeval (r : ℂ) F = (Fr r : ℂ) := by
  simp only [F, Fr, map_add, map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
  push_cast; ring

/-- every complex root `z` of `F` is real and lies in `(-2,2)` -/
theorem F_roots_real (z : ℂ) (hz : aeval z F = 0) : ∃ r : ℝ, -2 < r ∧ r < 2 ∧ z = r := by
  classical
  obtain ⟨r, hmono, hbd, hroot⟩ := F_six_real_roots
  by_contra hcon
  push Not at hcon
  set P : ℂ[X] := F.map (Int.castRingHom ℂ)
  have hP0 : P ≠ 0 := by
    intro h
    have : P.natDegree = 6 := by
      rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)), F_natDegree]
    rw [h] at this; simp at this
  have hPdeg : P.natDegree = 6 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)), F_natDegree]
  have hmem : ∀ w : ℂ, aeval w F = 0 → w ∈ P.roots.toFinset := by
    intro w hw
    have e : (Int.castRingHom ℂ) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_map, e, ← aeval_def]
    exact hw
  let S : Finset ℂ := Finset.image (fun i => ((r i : ℝ) : ℂ)) Finset.univ
  have hS : S.card = 6 := by
    have hinj : Function.Injective (fun i => ((r i : ℝ) : ℂ)) :=
      fun i j h => hmono.injective (Complex.ofReal_injective h)
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hzS : z ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    exact hcon (r i) (hbd i).1 (hbd i).2 hi.symm
  have hsub : insert z S ⊆ P.roots.toFinset := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hmem _ hz
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hw
      apply hmem
      rw [aeval_F_ofReal, hroot i]; simp
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hzS, hS] at h1
  have h2 := Multiset.toFinset_card_le P.roots
  have h3 := card_roots' P
  omega

/-- every complex root of `f` lies on the unit circle and is not real -/
theorem roots_on_circle (α : ℂ) (hα : aeval α f = 0) : ‖α‖ = 1 ∧ α.im ≠ 0 := by
  have h0 : α ≠ 0 := by
    rintro rfl
    have : aeval (0 : ℂ) f = 2 := by
      simp only [f, map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat]; simp
    rw [this] at hα; norm_num at hα
  rw [trace_identity α h0] at hα
  have hF : aeval (α + α⁻¹) F = 0 := by
    rcases mul_eq_zero.1 hα with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) h0
    · exact h
  obtain ⟨r, hr1, hr2, hz⟩ := F_roots_real _ hF
  have hq : α ^ 2 - r * α + 1 = 0 := by
    have : α ^ 2 + 1 = r * α := by
      rw [← hz]; field_simp
    linear_combination this
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp [sq] at hre him
  set u := α.re
  set v := α.im
  have hv : v ≠ 0 := by
    intro hv0
    rw [hv0] at hre
    nlinarith [sq_nonneg (u - r / 2)]
  have hu : 2 * u = r := by
    have : v * (2 * u - r) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hv
    · linarith
  have hn : u * u + v * v = 1 := by nlinarith
  refine ⟨?_, hv⟩
  have hsq : ‖α‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; exact hn
  have hnn : 0 ≤ ‖α‖ := norm_nonneg _
  nlinarith

end Davidson.Poly

#print axioms Davidson.Poly.f_eq_sum
#print axioms Davidson.Poly.f_coeff
#print axioms Davidson.Poly.a_palindromic
#print axioms Davidson.Poly.f_natDegree
#print axioms Davidson.Poly.f_leadingCoeff
#print axioms Davidson.Poly.f_eval_one
#print axioms Davidson.Poly.f_eval_zero
#print axioms Davidson.Poly.trace_identity
#print axioms Davidson.Poly.F_factor
#print axioms Davidson.Poly.F_six_real_roots
#print axioms Davidson.Poly.F_roots_real
#print axioms Davidson.Poly.roots_on_circle
