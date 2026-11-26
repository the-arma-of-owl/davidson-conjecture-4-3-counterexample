import Mathlib

/-!
# Extension step of Lemma 2 (Hahn–Banach)

Given integer vectors `L j ∈ ℤ^N` and integers `τ j` with
`|∑ m_j τ_j| ≤ ‖∑ m_j L_j‖₁` for all integer `m`, there is `σ ∈ [-1,1]^N` with
`σ · L_j = τ_j` for every `j`.

As in the paper: the inequality is extended to rational `m` by homogeneity, to real `m` by
density, and the functional `∑ y_j L_j ↦ ∑ y_j τ_j` on `span L` (well defined because of the
inequality) is extended by Hahn–Banach, dominated by the `ℓ¹` norm.
-/

namespace Davidson.Extension

open Finset

variable {N J : ℕ}

lemma ineq_rat (L : Fin J → Fin N → ℤ) (τ : Fin J → ℤ)
    (hineq : ∀ m : Fin J → ℤ, |∑ j, m j * τ j| ≤ ∑ n, |∑ j, m j * L j n|) (y : Fin J → ℚ) :
    |∑ j, y j * τ j| ≤ ∑ n, |∑ j, y j * L j n| := by
  set d : ℕ := ∏ j, (y j).den with hd
  have hdpos : (0 : ℚ) < d := by
    rw [hd]; push_cast
    exact Finset.prod_pos (fun j _ => by exact_mod_cast (y j).den_pos)
  have hint : ∀ j, ∃ z : ℤ, (d : ℚ) * y j = z := by
    intro j
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun j => (y j).den) (Finset.mem_univ j)
    refine ⟨r * (y j).num, ?_⟩
    rw [hd, hr]; push_cast
    rw [mul_comm ((y j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose m hm using hint
  have h1 := hineq m
  have h2 : ((|∑ j, m j * τ j| : ℤ) : ℚ) ≤ ((∑ n, |∑ j, m j * L j n| : ℤ) : ℚ) := by
    exact_mod_cast h1
  push_cast at h2
  simp only [← hm] at h2
  have e1 : ∑ j, (d : ℚ) * y j * τ j = d * ∑ j, y j * τ j := by
    rw [Finset.mul_sum]; congr 1; funext j; ring
  have e2 : ∀ n, ∑ j, (d : ℚ) * y j * L j n = d * ∑ j, y j * L j n := by
    intro n; rw [Finset.mul_sum]; congr 1; funext j; ring
  simp only [e1, e2, abs_mul, abs_of_pos hdpos, ← Finset.mul_sum] at h2
  exact le_of_mul_le_mul_left h2 hdpos

lemma ineq_real (L : Fin J → Fin N → ℤ) (τ : Fin J → ℤ)
    (hineq : ∀ m : Fin J → ℤ, |∑ j, m j * τ j| ≤ ∑ n, |∑ j, m j * L j n|) (y : Fin J → ℝ) :
    |∑ j, y j * τ j| ≤ ∑ n, |∑ j, y j * L j n| := by
  have hdense : DenseRange (Pi.map (fun (_ : Fin J) (q : ℚ) => (q : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hdense.induction_on (p := fun y : Fin J → ℝ =>
      |∑ j, y j * τ j| ≤ ∑ n, |∑ j, y j * L j n|) y ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro q
    have h := ineq_rat L τ hineq q
    have h' : ((|∑ j, q j * τ j| : ℚ) : ℝ) ≤ ((∑ n, |∑ j, q j * L j n| : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simpa [Pi.map] using h'

/-- **Extension step.** -/
theorem extend (L : Fin J → Fin N → ℤ) (τ : Fin J → ℤ)
    (hineq : ∀ m : Fin J → ℤ, |∑ j, m j * τ j| ≤ ∑ n, |∑ j, m j * L j n|) :
    ∃ σ : Fin N → ℝ, (∀ i, |σ i| ≤ 1) ∧ ∀ j, ∑ n, (L j n : ℝ) * σ n = τ j := by
  -- `T y = ∑ y_j L_j` and `φ y = ∑ y_j τ_j`
  let T : (Fin J → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun y n => ∑ j, y j * L j n
      map_add' := fun x y => by funext n; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by funext n; simp [Finset.mul_sum, mul_assoc] }
  let φ : (Fin J → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∑ j, y j * τ j
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hT : ∀ y n, T y n = ∑ j, y j * L j n := fun _ _ => rfl
  have hφ : ∀ y, φ y = ∑ j, y j * τ j := fun _ => rfl
  let Nrm : (Fin N → ℝ) → ℝ := fun x => ∑ n, |x n|
  have hdom : ∀ y, φ y ≤ Nrm (T y) := by
    intro y
    have := ineq_real L τ hineq y
    simp only [hφ, Nrm, hT]
    exact (le_abs_self _).trans this
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have h1 := ineq_real L τ hineq y
    have h2 : ∀ n, ∑ j, y j * L j n = 0 := fun n => by rw [← hT, hy]; rfl
    simp only [h2, abs_zero, Finset.sum_const_zero, abs_nonpos_iff] at h1
    rw [hφ]; exact h1
  let ψ : LinearMap.range T →ₗ[ℝ] ℝ :=
    (LinearMap.ker T).liftQ φ hker ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hψ : ∀ y, ψ ⟨T y, LinearMap.mem_range_self T y⟩ = φ y := by
    intro y
    simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let fP : (Fin N → ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range T, ψ⟩
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear fP Nrm
    (fun r hr x => by
      simp only [Nrm, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr, Finset.mul_sum])
    (fun x y => by
      simp only [Nrm, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun n _ => abs_add_le _ _))
    (by
      rintro ⟨x, y, rfl⟩
      exact (hψ y).le.trans (hdom y))
  let σ : Fin N → ℝ := fun i => g (fun j => if i = j then 1 else 0)
  have hgσ : ∀ x, g x = ∑ n, x n * σ n := by
    intro x; rw [LinearMap.pi_apply_eq_sum_univ g x]; rfl
  refine ⟨σ, fun i => ?_, fun j => ?_⟩
  · have hN : Nrm (fun j => if i = j then (1:ℝ) else 0) = 1 := by
      simp [Nrm, apply_ite (abs : ℝ → ℝ)]
    have hN' : Nrm (-(fun j => if i = j then (1:ℝ) else 0)) = 1 := by
      simp [Nrm, apply_ite (abs : ℝ → ℝ)]
    have a1 := hg2 (fun j => if i = j then (1:ℝ) else 0)
    have a2 := hg2 (-(fun j => if i = j then (1:ℝ) else 0))
    rw [hN] at a1; rw [hN', map_neg] at a2
    rw [abs_le]; exact ⟨by linarith, a1⟩
  · have hx : (fun n => (L j n : ℝ)) = T (Pi.single j 1) := by
      funext n; rw [hT]; simp [Pi.single_apply]
    have := hg1 ⟨T (Pi.single j 1), LinearMap.mem_range_self T _⟩
    rw [hgσ] at this
    rw [show ∑ n, (L j n : ℝ) * σ n = ∑ n, (T (Pi.single j 1)) n * σ n by rw [← hx]]
    rw [this]
    change ψ ⟨T (Pi.single j 1), _⟩ = _
    rw [hψ, hφ]; simp [Pi.single_apply]

end Davidson.Extension
