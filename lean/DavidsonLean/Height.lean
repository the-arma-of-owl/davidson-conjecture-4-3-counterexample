import Mathlib

/-!
# Height functions for proper 3-colourings of the grid `ℤ^N`

This file contains the combinatorial half of the necessity direction of the three-colour
criterion (Lemma 2 of the paper).  For a proper colouring `c : ℤ^N → ℤ/3` of the grid graph
(steps `± e_n`) we construct an integer height function `h` with

* `h (v + e_n) - h v = ±1` (the lift of `c (v + e_n) - c v ∈ {1, 2}`),
* `h ≡ c - c 0 (mod 3)` up to a constant,
* `h (v + u) - h v ≡ ∑ u_i (mod 2)`,
* `|h (v + u) - h v| ≤ ∑ |u_i|`,
* for every `c`-period `ℓ`, `h (v + ℓ) - h v` is independent of `v`.

The construction follows the paper: the step function `D` has no winding on unit squares, so it
integrates to a potential.  The potential is built coordinate by coordinate.
-/

namespace Davidson.Height

open Finset

variable {N : ℕ}

/-- the unit vector `e_n` of `ℤ^N` -/
abbrev e (n : Fin N) : Fin N → ℤ := Pi.single n 1

/-! ### Generic induction principles on `ℤ` and on `ℤ^N` -/

lemma int_const {α : Type*} (f : ℤ → α) (h : ∀ t, f (t + 1) = f t) : ∀ t, f t = f 0 := by
  intro t
  induction t using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [h, ih]
  | pred i ih => rw [← ih, ← h (-(i:ℤ) - 1)]; congr 1; ring

/-- A function invariant under all unit steps is invariant under all translations. -/
lemma inv_of_step {β : Type*} (φ : (Fin N → ℤ) → β) (h : ∀ v n, φ (v + e n) = φ v) :
    ∀ v u, φ (v + u) = φ v := by
  have single : ∀ v n (t : ℤ), φ (v + Pi.single n t) = φ v := by
    intro v n t
    have := int_const (fun t => φ (v + Pi.single n t)) (fun t => by
      rw [Pi.single_add, ← add_assoc, h]) t
    simpa using this
  intro v u
  have key : ∀ s : Finset (Fin N), ∀ v, φ (v + ∑ i ∈ s, Pi.single i (u i)) = φ v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      intro v
      rw [Finset.sum_insert ha, add_comm (Pi.single a (u a) : Fin N → ℤ), ← add_assoc, single, ih]
  have := key Finset.univ v
  rwa [Finset.univ_sum_single] at this

/-- A function changing by at most `1` along unit steps is `1`-Lipschitz for `‖·‖₁`. -/
lemma lipschitz_of_step (ψ : (Fin N → ℤ) → ℤ) (h : ∀ v n, |ψ (v + e n) - ψ v| ≤ 1) :
    ∀ v u, |ψ (v + u) - ψ v| ≤ ∑ n, |u n| := by
  intro v u
  have single : ∀ v n (t : ℤ), |ψ (v + Pi.single n t) - ψ v| ≤ |t| := by
    intro v n t
    induction t using Int.induction_on with
    | zero => simp
    | succ i ih =>
      have h1 := h (v + Pi.single n (i:ℤ)) n
      rw [add_assoc, ← Pi.single_add] at h1
      have h2 := abs_sub_le (ψ (v + Pi.single n ((i:ℤ) + 1))) (ψ (v + Pi.single n (i:ℤ))) (ψ v)
      have h3 : |(i:ℤ) + 1| = 1 + |(i:ℤ)| := by
        rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ i), abs_of_nonneg (by positivity)]; ring
      rw [h3]
      exact h2.trans (add_le_add h1 ih)
    | pred i ih =>
      have h1 := h (v + Pi.single n (-(i:ℤ) - 1)) n
      rw [add_assoc, ← Pi.single_add, sub_add_cancel, abs_sub_comm] at h1
      have h2 := abs_sub_le (ψ (v + Pi.single n (-(i:ℤ) - 1))) (ψ (v + Pi.single n (-(i:ℤ))))
        (ψ v)
      have h3 : |(-(i:ℤ) - 1)| = 1 + |(-(i:ℤ))| := by
        rw [abs_neg, abs_of_nonneg (by positivity : (0:ℤ) ≤ i), abs_of_neg (by omega)]; ring
      rw [h3]
      exact h2.trans (add_le_add h1 ih)
  have key : ∀ s : Finset (Fin N), ∀ v,
      |ψ (v + ∑ i ∈ s, Pi.single i (u i)) - ψ v| ≤ ∑ n ∈ s, |u n| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      intro v
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (Pi.single a (u a) : Fin N → ℤ),
        ← add_assoc]
      exact (abs_sub_le _ (ψ (v + ∑ i ∈ s, Pi.single i (u i))) _).trans
        (add_le_add (single _ a (u a)) (ih v))
  have := key Finset.univ v
  rwa [Finset.univ_sum_single] at this

/-- Additivity along integer combinations of shifts. -/
lemma shift_comb {J : ℕ} (h : (Fin N → ℤ) → ℤ) (ℓ : Fin J → Fin N → ℤ) (τ : Fin J → ℤ)
    (hτ : ∀ v j, h (v + ℓ j) = h v + τ j) (m : Fin J → ℤ) (v : Fin N → ℤ) :
    h (v + ∑ j, m j • ℓ j) = h v + ∑ j, m j * τ j := by
  have single : ∀ v j (t : ℤ), h (v + t • ℓ j) = h v + t * τ j := by
    intro v j t
    have := int_const (fun t => h (v + t • ℓ j) - t * τ j) (fun t => by
      rw [add_smul, one_smul, ← add_assoc, hτ]; ring) t
    simp only [zero_smul, add_zero, zero_mul, sub_zero] at this
    linarith
  have key : ∀ s : Finset (Fin J), ∀ v,
      h (v + ∑ j ∈ s, m j • ℓ j) = h v + ∑ j ∈ s, m j * τ j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      intro v
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (m a • ℓ a), ← add_assoc, single,
        ih]
      ring
  exact key _ v

/-! ### Primitive of a function `ℤ → ℤ` -/

/-- the primitive `g` of `d` with `g 0 = 0` and `g (t+1) = g t + d t` -/
def prim (d : ℤ → ℤ) (t : ℤ) : ℤ :=
  ∑ s ∈ range t.toNat, d s - ∑ s ∈ range (-t).toNat, d (-((s:ℤ) + 1))

lemma prim_zero (d : ℤ → ℤ) : prim d 0 = 0 := by simp [prim]

lemma prim_succ (d : ℤ → ℤ) (t : ℤ) : prim d (t + 1) = prim d t + d t := by
  unfold prim
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    have h1 : ((n:ℤ) + 1).toNat = n + 1 := by omega
    have h2 : (-((n:ℤ) + 1)).toNat = 0 := by omega
    have h3 : (-(n:ℤ)).toNat = 0 := by omega
    simp only [h1, h2, h3, Int.toNat_natCast, Finset.sum_range_succ]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = -((n:ℤ) + 1) := ⟨(-t - 1).toNat, by omega⟩
    subst hn
    have h1 : (-((n:ℤ) + 1) + 1).toNat = 0 := by omega
    have h2 : (-(-((n:ℤ) + 1) + 1)).toNat = n := by omega
    have h3 : (-((n:ℤ) + 1)).toNat = 0 := by omega
    have h4 : (-(-((n:ℤ) + 1))).toNat = n + 1 := by omega
    simp only [h1, h2, h3, h4, Finset.sum_range_succ]
    simp

/-! ### Closed step functions integrate to a potential -/

/-- `D` has no winding on unit squares. -/
def Closed (D : (Fin N → ℤ) → Fin N → ℤ) : Prop :=
  ∀ v n m, D v n + D (v + e n) m = D v m + D (v + e m) n

lemma update_add_single (v : Fin N → ℤ) (k : Fin N) :
    Function.update v k 0 + Pi.single k (v k) = v := by
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · simp [hi]

lemma potential_aux (D : (Fin N → ℤ) → Fin N → ℤ) (hD : Closed D) :
    ∀ k ≤ N, ∃ h : (Fin N → ℤ) → ℤ, ∀ v (n : Fin N), n.val < k → h (v + e n) = h v + D v n := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => 0, fun v n hn => absurd hn (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨h, hh⟩ := ih (by omega)
    set kk : Fin N := ⟨k, by omega⟩ with hkk
    let I : (Fin N → ℤ) → ℤ → ℤ := fun w t => prim (fun s => D (w + Pi.single kk s) kk) t
    -- segment shift
    have shift : ∀ w (n : Fin N) t, I (w + e n) t - I w t = D (w + Pi.single kk t) n - D w n := by
      intro w n t
      have := int_const (fun t => I (w + e n) t - I w t - (D (w + Pi.single kk t) n - D w n))
        (fun t => by
          simp only [I, prim_succ]
          have hsq := hD (w + Pi.single kk t) n kk
          rw [Pi.single_add, ← add_assoc w, add_right_comm w (e n)]
          linarith) t
      simp only [I, prim_zero, Pi.single_zero, add_zero, sub_self] at this
      linarith
    refine ⟨fun v => h (Function.update v kk 0) + I (Function.update v kk 0) (v kk), ?_⟩
    intro v n hn
    by_cases hnk : n = kk
    · subst hnk
      have h1 : Function.update (v + e kk) kk 0 = Function.update v kk 0 := by
        funext i; by_cases hi : i = kk
        · subst hi; simp
        · simp [hi]
      have h2 : (v + e kk) kk = v kk + 1 := by simp
      simp only [h1, h2, I, prim_succ]
      rw [update_add_single]; ring
    · have hn' : n.val < k := by
        have : n.val ≠ k := fun h => hnk (Fin.ext h)
        omega
      have h1 : Function.update (v + e n) kk 0 = Function.update v kk 0 + e n := by
        funext i; by_cases hi : i = kk
        · subst hi; simp [Ne.symm hnk]
        · simp [Function.update_of_ne hi]
      have h2 : (v + e n) kk = v kk := by simp [Ne.symm hnk]
      simp only [h1, h2]
      rw [hh _ n hn']
      have := shift (Function.update v kk 0) n (v kk)
      rw [update_add_single] at this
      linarith

/-- A closed step function is the gradient of an integer potential. -/
theorem potential (D : (Fin N → ℤ) → Fin N → ℤ) (hD : Closed D) :
    ∃ h : (Fin N → ℤ) → ℤ, ∀ v n, h (v + e n) = h v + D v n := by
  obtain ⟨h, hh⟩ := potential_aux D hD N le_rfl
  exact ⟨h, fun v n => hh v n n.isLt⟩

/-! ### The height function of a proper 3-colouring -/

section colouring

variable (c : (Fin N → ℤ) → ZMod 3)

/-- the step `D(v,n) ∈ {±1}`: the lift of `c (v + e_n) - c v ∈ {1, 2}` -/
def step (v : Fin N → ℤ) (n : Fin N) : ℤ := if c (v + e n) - c v = 1 then 1 else -1

variable {c}
variable (hc : ∀ v n, c (v + e n) ≠ c v)
include hc

lemma step_cast (v : Fin N → ℤ) (n : Fin N) : ((step c v n : ℤ) : ZMod 3) = c (v + e n) - c v := by
  have hne : c (v + e n) - c v ≠ 0 := sub_ne_zero.mpr (hc v n)
  have key : ∀ x : ZMod 3, x ≠ 0 → x ≠ 1 → x = -1 := by decide
  unfold step
  split_ifs with h1
  · rw [h1]; simp
  · rw [key _ hne h1]; simp

omit hc in
lemma step_pm (v : Fin N → ℤ) (n : Fin N) : step c v n = 1 ∨ step c v n = -1 := by
  unfold step; split_ifs <;> simp

lemma step_closed : Closed (step c) := by
  intro v n m
  have hcast : ((step c v n + step c (v + e n) m : ℤ) : ZMod 3) =
      ((step c v m + step c (v + e m) n : ℤ) : ZMod 3) := by
    push_cast
    rw [step_cast hc, step_cast hc, step_cast hc, step_cast hc, add_right_comm v (e n) (e m)]
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  rcases step_pm (c := c) v n with h1 | h1 <;>
    rcases step_pm (c := c) (v + e n) m with h2 | h2 <;>
    rcases step_pm (c := c) v m with h3 | h3 <;>
    rcases step_pm (c := c) (v + e m) n with h4 | h4 <;>
    omega

/-- **Height function.** A proper colouring `c` of the grid admits `h : ℤ^N → ℤ` with
`h (v + e_n) - h v = step c v n ∈ {±1}`. -/
theorem height_exists : ∃ h : (Fin N → ℤ) → ℤ, ∀ v n, h (v + e n) = h v + step c v n :=
  potential _ (step_closed hc)

variable {h : (Fin N → ℤ) → ℤ} (hh : ∀ v n, h (v + e n) = h v + step c v n)
include hh

/-- `h ≡ c` modulo `3`, up to an additive constant. -/
lemma height_mod3 (v u : Fin N → ℤ) :
    ((h (v + u) - h v : ℤ) : ZMod 3) = c (v + u) - c v := by
  have := inv_of_step (fun w => ((h w : ℤ) : ZMod 3) - c w) (fun w n => by
    rw [hh, Int.cast_add, step_cast hc]; ring) v u
  push_cast
  linear_combination this

omit hc in
/-- `h (v + u) - h v ≡ ∑ u_i (mod 2)`. -/
lemma height_mod2 (v u : Fin N → ℤ) : h (v + u) - h v ≡ ∑ i, u i [ZMOD 2] := by
  have hstep : ∀ w n, ((step c w n : ℤ) : ZMod 2) = 1 := by
    intro w n; rcases step_pm (c := c) w n with h1 | h1 <;> rw [h1] <;> decide
  have := inv_of_step (fun w => ((h w : ℤ) : ZMod 2) - ∑ i, ((w i : ℤ) : ZMod 2)) (fun w n => by
    rw [hh, Int.cast_add, hstep]
    have : ∑ i, (((w + e n) i : ℤ) : ZMod 2) = ∑ i, ((w i : ℤ) : ZMod 2) + 1 := by
      simp only [Pi.add_apply, Int.cast_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rw [this]; ring) v u
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).mp ?_
  push_cast
  simp only [Pi.add_apply, Int.cast_add, Finset.sum_add_distrib] at this
  linear_combination this

omit hc in
/-- `h` is `1`-Lipschitz for the `ℓ¹` norm. -/
lemma height_lipschitz (v u : Fin N → ℤ) : |h (v + u) - h v| ≤ ∑ i, |u i| :=
  lipschitz_of_step h (fun w n => by
    rw [hh]; rcases step_pm (c := c) w n with h1 | h1 <;> rw [h1] <;> simp) v u

omit hc in
/-- For a period `ℓ` of `c`, the increment `h (v + ℓ) - h v` does not depend on `v`. -/
lemma height_period (ℓ : Fin N → ℤ) (hℓ : ∀ v, c (v + ℓ) = c v) (v : Fin N → ℤ) :
    h (v + ℓ) = h v + (h ℓ - h 0) := by
  have hD : ∀ w n, step c (w + ℓ) n = step c w n := by
    intro w n; unfold step; rw [add_right_comm, hℓ, hℓ]
  have := inv_of_step (fun w => h (w + ℓ) - h w) (fun w n => by
    rw [add_right_comm, hh, hh, hD]; ring) 0 v
  simp only [zero_add] at this
  linarith

end colouring

end Davidson.Height
