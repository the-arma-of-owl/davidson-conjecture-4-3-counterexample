import DavidsonLean.Checker
import DavidsonLean.Height
import DavidsonLean.Extension

/-!
# Lemma 2 (necessity direction of the three-colour criterion), grid form

`necessity` is the general statement for an arbitrary finite family of periods `ℓ_j ∈ ℤ^N` of a
proper 3-colouring of the grid `ℤ^N`.  `lemma2` specialises it to the coefficient vectors
`ℓ_j` of `x^j f(x)`, `0 ≤ j ≤ K - 12`, in `ℤ^{K+1}`.
-/

namespace Davidson

open Finset

/-- **Necessity, general form.** Let `c : ℤ^N → ℤ/3` be a proper colouring of the grid graph
(`c (v + e_n) ≠ c v`) with periods `ℓ_j` (`c (v + ℓ_j) = c v`).  Then there is
`σ ∈ [-1,1]^N` such that every `σ · ℓ_j` is an integer divisible by `3` and congruent to
`∑_n (ℓ_j)_n` modulo `2`. -/
theorem necessity {N J : ℕ} (ℓ : Fin J → Fin N → ℤ) (c : (Fin N → ℤ) → ZMod 3)
    (hproper : ∀ v (n : Fin N), c (v + Pi.single n 1) ≠ c v)
    (hper : ∀ v (j : Fin J), c (v + ℓ j) = c v) :
    ∃ σ : Fin N → ℝ, (∀ i, |σ i| ≤ 1) ∧ ∀ j, ∃ t : ℤ,
      ∑ n, (ℓ j n : ℝ) * σ n = t ∧ (3 : ℤ) ∣ t ∧ t ≡ ∑ n, ℓ j n [ZMOD 2] := by
  obtain ⟨h, hh⟩ := Height.height_exists hproper
  set τ : Fin J → ℤ := fun j => h (ℓ j) - h 0 with hτdef
  have hτ : ∀ v j, h (v + ℓ j) = h v + τ j := fun v j =>
    Height.height_period hh (ℓ j) (fun w => hper w j) v
  have hineq : ∀ m : Fin J → ℤ, |∑ j, m j * τ j| ≤ ∑ n, |∑ j, m j * ℓ j n| := by
    intro m
    have h1 := Height.shift_comb h ℓ τ hτ m 0
    have h2 := Height.height_lipschitz hh 0 (∑ j, m j • ℓ j)
    rw [h1] at h2
    simpa [Finset.sum_apply, smul_eq_mul] using h2
  obtain ⟨σ, hσ1, hσ2⟩ := Extension.extend ℓ τ hineq
  refine ⟨σ, hσ1, fun j => ⟨τ j, hσ2 j, ?_, ?_⟩⟩
  · have := Height.height_mod3 hproper hh 0 (ℓ j)
    rw [hper, sub_self] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by simpa [hτdef] using this)
  · have := Height.height_mod2 hh 0 (ℓ j)
    simpa [hτdef] using this

/-- The coefficient vector `ℓ_j ∈ ℤ^{K+1}` of `x^j f(x)`:
`(ℓ_j)_i = a_{i-j}` for `j ≤ i ≤ j + 12`, and `0` otherwise. -/
def ell (K j : ℕ) : Fin (K + 1) → ℤ := fun i =>
  if h : j ≤ i.val ∧ i.val ≤ j + 12 then a ⟨i.val - j, by omega⟩ else 0

/-- `∑_i (ℓ_j)_i σ_i = ∑_{k=0}^{12} a_k σ_{k+j}` -/
lemma ell_sum {R : Type*} [CommRing R] (K j : ℕ) (hj : j + 12 ≤ K) (σ : Fin (K + 1) → R) :
    ∑ i, (ell K j i : R) * σ i = ∑ k : Fin 13, (a k : R) * σ ⟨k.val + j, by omega⟩ := by
  let emb : Fin 13 ↪ Fin (K + 1) :=
    ⟨fun k => ⟨k.val + j, by omega⟩, fun x y hxy => by
      simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega)⟩
  have hemb : ∀ k, (emb k).val = k.val + j := fun _ => rfl
  have h1 : ∀ k : Fin 13, (a k : R) * σ ⟨k.val + j, by omega⟩ =
      (ell K j (emb k) : R) * σ (emb k) := by
    intro k
    simp only [ell]
    rw [dite_eq_left_of_eq_true (eq_true (by rw [hemb]; omega))]
    congr 3
    ext; simp [hemb]
  simp only [h1]
  rw [← Finset.sum_map Finset.univ emb (fun i => (ell K j i : R) * σ i)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have : ¬ (j ≤ i.val ∧ i.val ≤ j + 12) := by
    rintro ⟨h1, h2⟩
    apply hi
    rw [Finset.mem_map]
    exact ⟨⟨i.val - j, by omega⟩, Finset.mem_univ _, Fin.ext (by rw [hemb]; simp; omega)⟩
  simp [ell, dite_eq_right_of_eq_false (eq_false this)]

lemma sum_a : ∑ k : Fin 13, a k = 1 := by decide

/-- **Lemma 2 (necessity), grid form.** Let `c : ℤ^{K+1} → ℤ/3` be a proper colouring of the
grid graph that is invariant under the coefficient vectors `ℓ_j` of `x^j f(x)`,
`0 ≤ j ≤ K - 12`.  Then there is `σ ∈ [-1,1]^{K+1}` with
`τ_j = ∑_{i=0}^{12} a_i σ_{i+j} ∈ 3(2ℤ+1)` for all `0 ≤ j ≤ K - 12`. -/
theorem lemma2 (K : ℕ) (c : (Fin (K + 1) → ℤ) → ZMod 3)
    (hproper : ∀ v (n : Fin (K + 1)), c (v + Pi.single n 1) ≠ c v)
    (hper : ∀ v (j : Fin (K - 11)), c (v + ell K j) = c v) :
    ∃ σ : Fin (K + 1) → ℝ, (∀ i, |σ i| ≤ 1) ∧
      ∀ j : Fin (K - 11), ∃ m : ℤ,
        ∑ i : Fin 13, (a i : ℝ) * σ ⟨i.val + j.val, by omega⟩ = 3 * (2 * m + 1) := by
  obtain ⟨σ, hσ1, hσ2⟩ := necessity (fun j : Fin (K - 11) => ell K j) c hproper hper
  refine ⟨σ, hσ1, fun j => ?_⟩
  obtain ⟨t, ht1, ht2, ht3⟩ := hσ2 j
  have hj : j.val + 12 ≤ K := by omega
  have hpar : ∑ n, ell K j n = 1 := by
    have := ell_sum (R := ℤ) K j hj (fun _ => 1)
    simp only [mul_one, Int.cast_id] at this
    rw [this, sum_a]
  rw [hpar] at ht3
  unfold Int.ModEq at ht3
  refine ⟨(t / 3 - 1) / 2, ?_⟩
  have ht : t = 3 * (2 * ((t / 3 - 1) / 2) + 1) := by omega
  rw [← ell_sum K j hj σ, ht1]
  conv_lhs => rw [ht]
  push_cast; ring

end Davidson
