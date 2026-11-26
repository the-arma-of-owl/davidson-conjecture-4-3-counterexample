import Mathlib

/-!
# A verified checker for the Proposition 3 certificate

Forms are affine functions of `x = (σ₀, …, σ₁₁)`, stored as `List ℚ`;
index `12` holds the constant term (we evaluate against the vector `Xpt σ` with `Xpt σ 12 = 1`).

`check` walks a certificate tree.  The soundness theorem `check_sound` says that if `check`
accepts any tree at the root, then no admissible `σ` with `τ₀ > 0` exists.
Nothing about the tree (or the parser producing it) has to be trusted.
-/

namespace Davidson

/-! ## Affine forms -/

/-- pointwise sum (the shorter list is padded with zeros) -/
def addF : List ℚ → List ℚ → List ℚ
  | [], h => h
  | g :: gs, [] => g :: gs
  | g :: gs, h :: hs => (g + h) :: addF gs hs

def smulF (c : ℚ) (g : List ℚ) : List ℚ := g.map (c * ·)

/-- value of a form at a point `x : ℕ → ℝ` -/
def evalF : List ℚ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | g :: gs, x => (g : ℝ) * x 0 + evalF gs (fun n => x (n + 1))

/-- `∑ |gᵢ|` over `i ≠ 12`, plus `g₁₂` (the constant term) -/
def bndAux : ℕ → List ℚ → ℚ
  | _, [] => 0
  | i, g :: gs => (if i = 12 then g else |g|) + bndAux (i + 1) gs

def bnd (g : List ℚ) : ℚ := bndAux 0 g

@[simp] lemma evalF_nil (x : ℕ → ℝ) : evalF [] x = 0 := rfl
@[simp] lemma evalF_cons (g : ℚ) (gs : List ℚ) (x : ℕ → ℝ) :
    evalF (g :: gs) x = (g : ℝ) * x 0 + evalF gs (fun n => x (n + 1)) := rfl

lemma evalF_addF : ∀ (g h : List ℚ) (x : ℕ → ℝ), evalF (addF g h) x = evalF g x + evalF h x
  | [], h, x => by simp [addF]
  | g :: gs, [], x => by simp [addF]
  | g :: gs, h :: hs, x => by
      simp only [addF, evalF_cons, evalF_addF gs hs, Rat.cast_add]; ring

lemma evalF_smulF (c : ℚ) : ∀ (g : List ℚ) (x : ℕ → ℝ), evalF (smulF c g) x = c * evalF g x
  | [], x => by simp [smulF]
  | g :: gs, x => by
      have := evalF_smulF c gs (fun n => x (n + 1))
      simp only [smulF, List.map_cons, evalF_cons, Rat.cast_mul] at this ⊢
      rw [this]; ring

lemma evalF_replicate (g : List ℚ) : ∀ (n : ℕ) (x : ℕ → ℝ),
    evalF (List.replicate n 0 ++ g) x = evalF g (fun m => x (m + n))
  | 0, x => by simp
  | n + 1, x => by
      simp only [List.replicate_succ, List.cons_append, evalF_cons, Rat.cast_zero, zero_mul,
        zero_add]
      rw [evalF_replicate g n]
      congr 1

/-- admissible points: `x i ∈ [-1,1]` except `x 12 = 1` (after a shift by `i`) -/
def Adm (i : ℕ) (x : ℕ → ℝ) : Prop := ∀ n, (n + i = 12 → x n = 1) ∧ (n + i ≠ 12 → |x n| ≤ 1)

lemma evalF_le_bndAux : ∀ (g : List ℚ) (i : ℕ) (x : ℕ → ℝ), Adm i x → evalF g x ≤ bndAux i g
  | [], i, x, _ => by simp [bndAux]
  | g :: gs, i, x, hx => by
      have ih := evalF_le_bndAux gs (i + 1) (fun n => x (n + 1)) (by
        intro n; constructor
        · intro h; exact (hx (n + 1)).1 (by omega)
        · intro h; exact (hx (n + 1)).2 (by omega))
      simp only [evalF_cons, bndAux, Rat.cast_add]
      have h0 : (g : ℝ) * x 0 ≤ ((if i = 12 then g else |g| : ℚ) : ℝ) := by
        split_ifs with h
        · have := (hx 0).1 (by omega); rw [this]; simp
        · have := (hx 0).2 (by omega)
          push_cast
          calc (g : ℝ) * x 0 ≤ |(g : ℝ) * x 0| := le_abs_self _
            _ = |(g : ℝ)| * |x 0| := abs_mul _ _
            _ ≤ |(g : ℝ)| * 1 := by gcongr
            _ = |(g : ℝ)| := mul_one _
      linarith

lemma evalF_le_bnd (g : List ℚ) (x : ℕ → ℝ) (hx : Adm 0 x) : evalF g x ≤ bnd g :=
  evalF_le_bndAux g 0 x hx

/-! ## Bounds from multipliers -/

/-- a row is a form `c_k` together with the value `τ_k`; default row is harmless -/
abbrev Row := List ℚ × ℚ

def ubGo (rows : List Row) : List (ℕ × ℚ) → List ℚ → ℚ → ℚ
  | [], g, acc => bnd g + acc
  | (k, y) :: ys, g, acc =>
      let r := rows.getD k ([], 0)
      ubGo rows ys (addF g (smulF (-y) r.1)) (acc + y * r.2 + 2 * |y|)

/-- upper bound for the form `g` certified by the multipliers `ys` -/
def ub (rows : List Row) (ys : List (ℕ × ℚ)) (g : List ℚ) : ℚ := ubGo rows ys g 0

/-- rows are valid at the point `x`: `|c_k(x) - τ_k| ≤ 2` -/
def RowsOK (rows : List Row) (x : ℕ → ℝ) : Prop :=
  ∀ k, |evalF (rows.getD k ([], 0)).1 x - ((rows.getD k ([], 0)).2 : ℝ)| ≤ 2

lemma ubGo_sound (rows : List Row) (x : ℕ → ℝ) (hx : Adm 0 x) (hr : RowsOK rows x) :
    ∀ (ys : List (ℕ × ℚ)) (g : List ℚ) (acc : ℚ), evalF g x + acc ≤ ubGo rows ys g acc
  | [], g, acc => by
      simp only [ubGo, Rat.cast_add]; linarith [evalF_le_bnd g x hx]
  | (k, y) :: ys, g, acc => by
      simp only [ubGo]
      set r := rows.getD k ([], 0)
      have ih := ubGo_sound rows x hx hr ys (addF g (smulF (-y) r.1)) (acc + y * r.2 + 2 * |y|)
      rw [evalF_addF, evalF_smulF] at ih
      have hk := hr k
      have : (y : ℝ) * evalF r.1 x ≤ y * r.2 + 2 * |(y : ℝ)| := by
        have h1 : (y : ℝ) * (evalF r.1 x - r.2) ≤ |(y : ℝ)| * 2 := by
          calc (y : ℝ) * (evalF r.1 x - r.2) ≤ |(y : ℝ) * (evalF r.1 x - r.2)| := le_abs_self _
            _ = |(y : ℝ)| * |evalF r.1 x - r.2| := abs_mul _ _
            _ ≤ |(y : ℝ)| * 2 := by gcongr
        linarith
      push_cast at ih ⊢
      linarith

lemma ub_sound (rows : List Row) (x : ℕ → ℝ) (hx : Adm 0 x) (hr : RowsOK rows x)
    (ys : List (ℕ × ℚ)) (g : List ℚ) : evalF g x ≤ ub rows ys g := by
  have := ubGo_sound rows x hx hr ys g 0; simpa [ub] using this

/-! ## The polynomial and the tree -/

/-- coefficients `a₀, …, a₁₂` of `f` -/
def aList : List ℤ := [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]

def aQ (i : ℕ) : ℚ := (aList.getD i 0 : ℚ)

/-- the form `c_j = ∑_{i<12} aᵢ σ_{i+j}` built from the history of forms of `σ₀, σ₁, …` -/
def cFormL (hist : List (List ℚ)) (j : ℕ) : List ℕ → List ℚ
  | [] => []
  | i :: is => addF (smulF (aQ i) (hist.getD (j + i) [])) (cFormL hist j is)

def cForm (hist : List (List ℚ)) (j : ℕ) : List ℚ := cFormL hist j (List.range 12)

/-- the constant form `t` -/
def constF (t : ℚ) : List ℚ := List.replicate 12 0 ++ [t]

/-- `σ_{j+12} = (τ_j - c_j)/2` -/
def newForm (cj : List ℚ) (t : ℤ) : List ℚ := smulF (1 / 2) (addF (constF t) (smulF (-1) cj))

/-- unit forms for `σ₀, …, σ₁₁` -/
def initHist : List (List ℚ) := (List.range 12).map (fun n => List.replicate n 0 ++ [1])

/-- certificate tree: every node is an interval node (type `I` in the paper) -/
inductive Cert where
  | node (yu yl : List (ℕ × ℚ)) (kids : List (ℤ × Cert))

/-- the set `T` of possible values of `τ_j` -/
def Tset : List ℤ := [-15, -9, -3, 3, 9, 15]

/-- maximal word length -/
def LMAX : ℕ := 68

mutual
def check (hist : List (List ℚ)) (rows : List Row) (j : ℕ) : Cert → Bool
  | .node yu yl kids =>
    let cj := cForm hist j
    let hi := ub rows yu cj
    let lo := -ub rows yl (smulF (-1) cj)
    decide (j < LMAX) &&
    Tset.all (fun t => (decide (j = 0) && decide (t < 0)) || decide ((t : ℚ) + 2 < lo) ||
      decide (hi < (t : ℚ) - 2) || kids.any (fun p => p.1 == t)) &&
    checkKids hist rows j cj kids

def checkKids (hist : List (List ℚ)) (rows : List Row) (j : ℕ) (cj : List ℚ) :
    List (ℤ × Cert) → Bool
  | [] => true
  | (t, c) :: rest =>
    check (hist ++ [newForm cj t]) (rows ++ [(cj, (t : ℚ))]) (j + 1) c &&
    checkKids hist rows j cj rest
end

/-- the root check -/
def checkRoot (c : Cert) : Bool := check initHist [] 0 c

/-! ## Soundness -/

section Soundness

variable (s : ℕ → ℝ)

/-- the evaluation point attached to `s` -/
def Xpt (n : ℕ) : ℝ := if n < 12 then s n else if n = 12 then 1 else 0

/-- `τ_j(s) = ∑_{i ≤ 12} aᵢ s_{i+j}` -/
def tauR (j : ℕ) : ℝ := ∑ i ∈ Finset.range 13, (aQ i : ℝ) * s (i + j)

/-- `c_j(s) = ∑_{i < 12} aᵢ s_{i+j}` -/
def cR (j : ℕ) : ℝ := ∑ i ∈ Finset.range 12, (aQ i : ℝ) * s (i + j)

lemma tauR_eq (j : ℕ) : tauR s j = cR s j + 2 * s (j + 12) := by
  simp [tauR, cR, Finset.sum_range_succ, aQ, aList, add_comm]

/-- the hypotheses on `s`: box, integrality with values in `T`, `τ₀ > 0` -/
structure Good (tau : ℕ → ℤ) : Prop where
  box : ∀ n, n < LMAX + 12 → |s n| ≤ 1
  tau_eq : ∀ j, j < LMAX → tauR s j = tau j
  tau_mem : ∀ j, j < LMAX → tau j ∈ Tset
  tau0 : 0 < tau 0

/-- invariant at depth `j` -/
structure Inv (tau : ℕ → ℤ) (j : ℕ) (hist : List (List ℚ)) (rows : List Row) : Prop where
  hlen : hist.length = j + 12
  hist_ev : ∀ m, m < j + 12 → evalF (hist.getD m []) (Xpt s) = s m
  rlen : rows.length = j
  rows_ev : ∀ k, k < j → evalF (rows.getD k ([], 0)).1 (Xpt s) = cR s k
  rows_tau : ∀ k, k < j → (rows.getD k ([], 0)).2 = (tau k : ℚ)

lemma adm_X (hs : ∀ n, n < 12 → |s n| ≤ 1) : Adm 0 (Xpt s) := by
  intro n; constructor
  · intro h; simp [Xpt, show n = 12 by omega]
  · intro h
    unfold Xpt
    split_ifs with h1
    · exact hs n h1
    all_goals first | omega | simp

lemma evalF_cFormL (hist : List (List ℚ)) (j : ℕ) (x : ℕ → ℝ) :
    ∀ L : List ℕ, evalF (cFormL hist j L) x = (L.map (fun i => (aQ i : ℝ) * evalF (hist.getD (j + i) []) x)).sum
  | [] => by simp [cFormL]
  | i :: is => by simp [cFormL, evalF_addF, evalF_smulF, evalF_cFormL hist j x is]

lemma evalF_cForm (tau : ℕ → ℤ) (j : ℕ) (hist : List (List ℚ)) (rows : List Row)
    (hI : Inv s tau j hist rows) : evalF (cForm hist j) (Xpt s) = cR s j := by
  unfold cForm; rw [evalF_cFormL]
  have h : ∀ i ∈ List.range 12, (aQ i : ℝ) * evalF (hist.getD (j + i) []) (Xpt s) =
      (aQ i : ℝ) * s (i + j) := by
    intro i hi
    rw [List.mem_range] at hi
    rw [hI.hist_ev _ (by omega), add_comm]
  rw [List.map_congr_left h, cR]
  simp [List.range_succ, Finset.sum_range_succ]
  ring

lemma checkKids_mem (hist : List (List ℚ)) (rows : List Row) (j : ℕ) (cj : List ℚ) :
    ∀ kids : List (ℤ × Cert), checkKids hist rows j cj kids = true → ∀ p ∈ kids,
      check (hist ++ [newForm cj p.1]) (rows ++ [(cj, (p.1 : ℚ))]) (j + 1) p.2 = true
  | [], _, p, hp => by simp at hp
  | (t, c) :: rest, h, p, hp => by
      rw [checkKids, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h.1
      · exact checkKids_mem hist rows j cj rest h.2 p hp

lemma evalF_constF (t : ℚ) : evalF (constF t) (Xpt s) = t := by
  rw [constF, evalF_replicate]; simp [Xpt]

lemma rowsOK_of_inv (tau : ℕ → ℤ) (hg : Good s tau) (j : ℕ) (hj : j ≤ LMAX)
    (hist : List (List ℚ)) (rows : List Row) (hI : Inv s tau j hist rows) : RowsOK rows (Xpt s) := by
  intro k
  by_cases hk : k < j
  · rw [hI.rows_ev k hk, hI.rows_tau k hk, Rat.cast_intCast, ← hg.tau_eq k (by omega),
      tauR_eq]
    have := hg.box (k + 12) (by omega)
    rw [show cR s k - (cR s k + 2 * s (k + 12)) = -(2 * s (k + 12)) by ring, abs_neg, abs_mul]
    norm_num; linarith
  · rw [List.getD_eq_default _ _ (by rw [hI.rlen]; omega)]; simp

theorem check_sound_aux (tau : ℕ → ℤ) (hg : Good s tau) :
    ∀ (n j : ℕ) (hist : List (List ℚ)) (rows : List Row) (c : Cert), LMAX - j = n →
      Inv s tau j hist rows → check hist rows j c = true → False := by
  intro n
  induction n with
  | zero =>
    intro j hist rows c hn _ hc
    obtain ⟨yu, yl, kids⟩ := c
    rw [check] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  | succ n ih =>
    intro j hist rows c hn hI hc
    obtain ⟨yu, yl, kids⟩ := c
    rw [check] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hj, hT⟩, hK⟩ := hc
    have hx := adm_X s (fun n hn => hg.box n (by unfold LMAX; omega))
    have hr := rowsOK_of_inv s tau hg j hj.le hist rows hI
    have hV := evalF_cForm s tau j hist rows hI
    set cj := cForm hist j
    have hhi := ub_sound rows (Xpt s) hx hr yu cj
    have hlo := ub_sound rows (Xpt s) hx hr yl (smulF (-1) cj)
    rw [evalF_smulF, hV] at hlo
    rw [hV] at hhi
    set t := tau j
    have htT := hg.tau_mem j hj
    have htv : (t : ℝ) = cR s j + 2 * s (j + 12) := by rw [← hg.tau_eq j hj, tauR_eq]
    have hsb := abs_le.1 (hg.box (j + 12) (by omega))
    have ht := List.all_eq_true.1 hT t htT
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨p, hp, hpt⟩ : ∃ p ∈ kids, p.1 = t := by
      rcases ht with ((⟨h0, hneg⟩ | hlt) | hgt) | hany
      · subst h0; have := hg.tau0; omega
      · exfalso
        have : ((t : ℚ) : ℝ) + 2 < -((ub rows yl (smulF (-1) cj) : ℚ) : ℝ) := by
          exact_mod_cast hlt
        push_cast at this hlo; linarith
      · exfalso
        have : ((ub rows yu cj : ℚ) : ℝ) < ((t : ℚ) : ℝ) - 2 := by exact_mod_cast hgt
        push_cast at this; linarith
      · obtain ⟨p, hp, hpt⟩ := List.any_eq_true.1 hany
        exact ⟨p, hp, by simpa using hpt⟩
    have hc' := checkKids_mem hist rows j cj kids hK p hp
    rw [hpt] at hc'
    refine ih (j + 1) _ _ p.2 (by omega) ?_ hc'
    constructor
    · simp [hI.hlen]
    · intro m hm
      by_cases hm' : m < j + 12
      · rw [List.getD_append _ _ _ _ (by rw [hI.hlen]; exact hm')]; exact hI.hist_ev m hm'
      · rw [List.getD_append_right _ _ _ _ (by rw [hI.hlen]; omega), hI.hlen,
          show m - (j + 12) = 0 by omega]
        have hm2 : m = j + 12 := by omega
        subst hm2
        simp only [List.getD_cons_zero, newForm, evalF_smulF, evalF_addF, evalF_constF]
        rw [hV]; push_cast; linarith
    · simp [hI.rlen]
    · intro k hk
      by_cases hk' : k < j
      · rw [List.getD_append _ _ _ _ (by rw [hI.rlen]; exact hk')]; exact hI.rows_ev k hk'
      · rw [List.getD_append_right _ _ _ _ (by rw [hI.rlen]; omega), hI.rlen,
          show k - j = 0 by omega, show k = j by omega]
        simpa using hV
    · intro k hk
      by_cases hk' : k < j
      · rw [List.getD_append _ _ _ _ (by rw [hI.rlen]; exact hk')]; exact hI.rows_tau k hk'
      · rw [List.getD_append_right _ _ _ _ (by rw [hI.rlen]; omega), hI.rlen,
          show k - j = 0 by omega, show k = j by omega]
        simp [t]

theorem check_sound (tau : ℕ → ℤ) (hg : Good s tau) (c : Cert) (hc : checkRoot c = true) :
    False := by
  refine check_sound_aux s tau hg _ 0 initHist [] c rfl ?_ hc
  constructor
  · simp [initHist]
  · intro m hm
    have : initHist.getD m [] = List.replicate m 0 ++ [1] := by
      simp [initHist, List.getD_eq_getElem?_getD, hm]
    rw [this, evalF_replicate]
    simp [Xpt, show m < 12 by omega]
  · rfl
  · intro k hk; omega
  · intro k hk; omega

end Soundness

end Davidson

namespace Davidson

/-! ## From the checker to the statement of Proposition 3 -/

/-- the coefficients `a₀, …, a₁₂` -/
def a : Fin 13 → ℤ := ![2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]

/-- the statement of Proposition 3 -/
def Prop3Statement : Prop :=
  ¬ ∃ σ : Fin 80 → ℝ, (∀ i, |σ i| ≤ 1) ∧
    ∀ j : Fin 68, ∃ m : ℤ,
      ∑ i : Fin 13, (a i : ℝ) * σ ⟨i.val + j.val, by omega⟩ = 3 * (2 * m + 1)

/-- extension of `σ` by zero -/
def ext (σ : Fin 80 → ℝ) (n : ℕ) : ℝ := if h : n < 80 then σ ⟨n, h⟩ else 0

lemma sum_eq_tauR (σ : Fin 80 → ℝ) (j : Fin 68) :
    ∑ i : Fin 13, (a i : ℝ) * σ ⟨i.val + j.val, by omega⟩ = tauR (ext σ) j := by
  rw [tauR, ← Fin.sum_univ_eq_sum_range (fun i => (aQ i : ℝ) * ext σ (i + j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h80 : i.val + j.val < 80 := by omega
  simp only [ext, h80, dite_true]
  congr 1
  fin_cases i <;> simp [a, aQ, aList]

lemma tauR_abs_le (s : ℕ → ℝ) (j : ℕ) (hs : ∀ n, n < j + 13 → |s n| ≤ 1) : |tauR s j| ≤ 19 := by
  have h := fun k (hk : k < 13) => abs_le.1 (hs (k + j) (by omega))
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega); have h8 := h 8 (by omega)
  have h9 := h 9 (by omega); have h10 := h 10 (by omega); have h11 := h 11 (by omega)
  have h12 := h 12 (by omega)
  simp only [zero_add] at h0
  rw [abs_le]
  simp only [tauR, Finset.sum_range_succ, Finset.sum_range_zero, aQ, aList]
  norm_num
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
    h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2, h12.1, h12.2]

lemma tauR_neg (s : ℕ → ℝ) (j : ℕ) : tauR (fun n => -s n) j = -tauR s j := by
  simp [tauR, Finset.sum_neg_distrib]

lemma mem_Tset (m : ℤ) (h : |(3 * (2 * m + 1) : ℝ)| ≤ 19) : 3 * (2 * m + 1) ∈ Tset := by
  have h' : |(3 * (2 * m + 1) : ℤ)| ≤ 19 := by exact_mod_cast h
  rw [abs_le] at h'
  have h1 : -3 ≤ m := by omega
  have h2 : m ≤ 2 := by omega
  interval_cases m <;> decide

/-- if `s` satisfies the hypotheses with `τ₀ > 0`, any accepted certificate gives `False` -/
lemma false_of_pos (c : Cert) (hc : checkRoot c = true) (s : ℕ → ℝ)
    (hbox : ∀ n, n < 80 → |s n| ≤ 1)
    (hint : ∀ j, j < 68 → ∃ m : ℤ, tauR s j = 3 * (2 * m + 1))
    (hpos : 0 < tauR s 0) : False := by
  classical
  let tau : ℕ → ℤ := fun j => if h : j < 68 then 3 * (2 * (hint j h).choose + 1) else 0
  have htau : ∀ j, j < 68 → tauR s j = tau j := by
    intro j hj
    simp only [tau, hj, dite_true]; push_cast; exact (hint j hj).choose_spec
  refine check_sound s tau ⟨fun n hn => hbox n (by unfold LMAX at hn; omega),
    fun j hj => htau j hj, fun j hj => ?_, ?_⟩ c hc
  · have hj' : j < 68 := hj
    simp only [tau, hj', dite_true]
    apply mem_Tset
    have := tauR_abs_le s j (fun n hn => hbox n (by omega))
    rw [(hint j hj').choose_spec] at this
    exact this
  · have := htau 0 (by omega); rw [this] at hpos; exact_mod_cast hpos

/-- **Soundness**: if the checker accepts some certificate, Proposition 3 holds. -/
theorem prop3_of_check (c : Cert) (hc : checkRoot c = true) : Prop3Statement := by
  rintro ⟨σ, hbox, hint⟩
  have hbox' : ∀ n, n < 80 → |ext σ n| ≤ 1 := fun n hn => by simp [ext, hn, hbox]
  have hint' : ∀ j, j < 68 → ∃ m : ℤ, tauR (ext σ) j = 3 * (2 * m + 1) := by
    intro j hj
    obtain ⟨m, hm⟩ := hint ⟨j, hj⟩
    exact ⟨m, by rw [← sum_eq_tauR σ ⟨j, hj⟩]; exact hm⟩
  obtain ⟨m0, hm0⟩ := hint' 0 (by omega)
  rcases le_or_gt 0 m0 with hm | hm
  · refine false_of_pos c hc (ext σ) hbox' hint' ?_
    rw [hm0]; have : (0 : ℝ) ≤ m0 := by exact_mod_cast hm
    linarith
  · refine false_of_pos c hc (fun n => -ext σ n) (fun n hn => by rw [abs_neg]; exact hbox' n hn)
      (fun j hj => ?_) ?_
    · obtain ⟨m, hm⟩ := hint' j hj
      exact ⟨-m - 1, by rw [tauR_neg, hm]; push_cast; ring⟩
    · rw [tauR_neg, hm0]; have : (m0 : ℝ) ≤ -1 := by exact_mod_cast (by omega : m0 ≤ -1)
      linarith

end Davidson
