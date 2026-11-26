# Referee report: claimed counterexample to Conjecture 4.3 of Davidson, arXiv:2610.09474

Date: 2026-11-26. Written independently. I read the claimant's files but did not rely on their checker, their generator or their results, and I did not read the other reviewer's notes in `yayin/`. All code named below is my own. Copies are in [`verification/referee_code/`](verification/referee_code/) (paths updated when the report was added to the repository).

## Overall verdict

**"Conjecture 4.3 is false" is correct, and the counterexample is valid.**

Let α be any root of

    f(x) = 2x^12 + 2x^11 + x^10 − x^9 − 2x^8 − x^7 − x^6 − x^5 − 2x^4 − x^3 + x^2 + 2x + 2.

Then α is an algebraic, non-integral unit complex number, and χ(Γ_α) = 4.

- **Lower bound.** The subgraph G_79 is not 3-colourable. This follows from:
  - the reduction (b), which I re-proved rigorously below (with a Farkas-lemma proof of the step the claimant calls "averaging slopes");
  - the certificate. My own exact checker accepts it. I also rebuilt the search from scratch with a different LP solver (GLPK), a different LP formulation and a different kind of certificate. That search produced exactly the same set of 75,530 nodes, and a separate exact verifier accepts it.
- **Upper bound.** χ(Γ_α) ≤ 4 is the paper's Theorem 4.1.
- **Threshold.** G_78 is 3-colourable, so the cut-off at K = 79 is sharp. This holds by three independent exact feasibility certificates, together with the converse of the criterion, which I also prove.

I found no mathematical error. The issues listed below are gaps in exposition and robustness, plus one unproved side claim (the converse). That side claim is true, and its proof is given here.

---

## Task 1 — Definitions. Verdict: **α qualifies**

I read these from the TeX source in `paper_src/tex/`. arXiv lists only v1 (7 Oct 2026); I checked the abstract page myself.

- **"Direction parameter."** There is no formal definition beyond §1, l.123: "Let α=e^{iθ} now be an arbitrary unit complex number, and write Γ_α=MonCay(α)." The abstract and Conjecture 4.7 use "direction parameter" for exactly such an α. Section 4 (l.11) adds that α is noncyclotomic algebraic, with primitive integer minimal polynomial f normalised by a_d > 0.
- **"Noninteger."** This means "not an algebraic integer" (§1 l.141: "algebraic parameters that are not algebraic integers"). For a primitive minimal polynomial this is equivalent to a_d ≥ 2. Here a_d = 2, the content is 1, and f is irreducible, so the monic minimal polynomial f/2 does not lie in Z[x].
- **Other hypotheses.** Conjecture 4.3 has none. Its statement, verbatim: "If α is an algebraic noninteger direction parameter, then χ(Γ_α)≤3."
- **The graph.** By Definition 1.1, Γ_α = Cay(Z[α], Mon(α)) with Mon(α) = {±α^n : n ≥ 0}. Hence the vertex set is Z[α] = ⋃_K M_K, where M_K = Z-span(1, …, α^K).
- **G_K ⊆ Γ_α.** G_K = Cay(M_K, {±α^n : n ≤ K}) has vertices in Z[α] and steps that are allowed steps, so it is a subgraph.
  - In fact G_K is the *induced* subgraph Γ_α[M_K]: for n > K we have α^n ∉ M_K, because a_d = 2 is the least multiplier taking α^n into M_{n−1} (paper §4.1, after Thm 4.1).
- **Abstract graph.** Γ_α ≅ Cay(Z[x]/(f), {±x^n}) depends only on f (Gauss's lemma gives Z[α] ≅ Z[x]/(f)). So all twelve roots give the same graph, and all twelve lie on the unit circle (Task 2).
- **Upper bound.** Theorem 4.1 (García-Marco–Knauer–Menara) applies with a_d = 2 and gives χ ≤ ⌈2a_d/(a_d−1)⌉ = 4.

## Task 2 — Polynomial facts. Verdict: **all confirmed. No sufficient condition for 3 colours in the paper applies, and the counterexample satisfies every necessary restriction the paper places on one (Prop. 4.5, Cor. 4.6).**

Script: `referee/polyfacts.py`; output in `referee/outputs/polyfacts.out`. Exact arithmetic was done with sympy, python-flint and Fractions, and the Sturm sequence is my own implementation.

| Fact | Result |
|---|---|
| Coefficients palindromic, content 1, a_12 = 2 | yes, 1, 2 |
| f(1), f(−1), f(i), Σ\|a_i\| | 1, 1, −1, 19 |
| Trace polynomial F, with x^6 F(x+1/x) = f | F = 2y^6+2y^5−11y^4−11y^3+12y^2+12y+1 = y(y²−4)(y+1)(2y²−3)+1 (identity checked symbolically) |
| Irreducibility of F | F is irreducible mod 3, and its leading coefficient 2 is nonzero mod 3, so F is irreducible over Q. It is also irreducible mod 23, 67, 89, 103, 151, 163, 173. |
| Irreducibility of f | sympy `factor_list` and flint `fmpz_poly.factor`: irreducible. Hand proof: every root β of F is real, and α is a non-real root of x²−βx+1, so [Q(α):Q(β)] = 2 and [Q(α):Q] = 12 = deg f. |
| Real roots of F | Own Sturm sequence: 6 real roots in total, all 6 in (−2,2) (F(±2) = 1 ≠ 0). sympy `count_roots(−2,2)` = 6. |
| All 12 roots on \|z\| = 1 | Follows from the previous row. Numerically, max \|\|z\|−1\| = 0 at 40 digits. |
| Root angles (degrees) | 5.292638, 51.165675, 92.652570, 113.162033, 134.179976, 170.498171 (matches the claimant's JSON) |
| Not a root of unity | Leading coefficient 2 means the roots are not algebraic integers. Directly: gcd(f, x^m−1) = 1 for all m ≤ 400. |
| Mahler measure | 2 (leading coefficient times 1) |

The paper's tests for 3 colours, and why none applies:

| Test (paper) | Value for f | Gives 3 colours? |
|---|---|---|
| Bipartite criterion, Lemma 2.4 (f(1) even ⇒ 2 colours) | f(1) = 1 | no (and Γ_α is not bipartite) |
| Elementary evaluation, Lemma 2.5: q ∣ f(1), f(−1) or f(i) | \|F(2)\| = \|F(−2)\| = \|F(0)\| = 1 | no |
| Cyclotomic Congruence Criterion, Prop 2.9 with 3 ∣ q (equivalent to Φ_m ∣ f mod 3); all 26 orders with φ(m) ≤ 12 checked, with multiplicity | none | no |
| Same criterion, general q (gives only 4 colours) | non-trivial gcds only at m = 6 (q = 7, i.e. F(1) = 7), m = 15 and m = 30 (q = 2) | no: these give the E_7 and E_2 = K_4 targets, i.e. 4 colours, consistent with χ = 4 |
| Eighth-root norm, Lemma 2.12 | F ≡ −3 − 2y (mod y²−2), D_8 = \|9−8\| = 1 | no |
| Theorem 4.1 with a_d ≥ 3; Cor. 4.6 / degree ≤ 8 | a_d = 2; degree 12 | no |
| Cyclotomic Norm Criterion, Thm 2.11 | gives at most 4 colours | irrelevant for 3 |

Prop. 4.5's necessary conditions all hold: a_0 = a_d = 2; F = y(y²−4)Q + 1 with Q = 2y³+2y²−3y−3, leading coefficient 2; Φ_m ∤ f (mod 3) for all m; D_8 = 1 ∈ {1, 7}. Cor. 4.6 needs degree ≥ 10, and the degree is 12. So the counterexample contradicts nothing proved in the paper.

For information: D_m for m = 3…30 is 1, 1, 19, 7, 1, 1, 127, 11, 131, 37, 79, 83, 16, 31, 1801, 17, 1, 41, 293, 43, 6439, 71, 2999, 1483, 53, 197, 79633, 16.

## Task 3 — Reduction (b). Verdict: **true; rigorous proof below. The converse also holds.**

The claimant's sketch is correct in substance but incomplete at two points (Issues 1 and 2). The proof below fills both gaps.

**Notation.** d = 12. Let π : Z^{K+1} → M_K be the map c ↦ Σ c_n α^n, and Λ = ker π. Let ℓ_j ∈ Z^{K+1} be the coefficient vector of x^j f(x), for 0 ≤ j ≤ K−12.

**Lemma A (relation lattice).** Λ = Z-span{ℓ_j}, a free module of rank K−11.

*Proof.* Let p ∈ Z[x] with deg p ≤ K and p(α) = 0. Since f is irreducible, f ∣ p in Q[x]; write p = f·g. Write g = (r/s)·g₀ with g₀ primitive. Gauss's lemma makes f·g₀ primitive, so r/s = ±content(p) ∈ Z and g ∈ Z[x], with deg g ≤ K−12. The converse inclusion is trivial. ∎

So G_K ≅ Cay(Z^{K+1}/Λ, {±e_n}). A proper 3-colouring c of G_K pulls back to a proper colouring c̃ = c∘π of the grid graph Z^{K+1}, and c̃ is Λ-invariant. (Primitivity matters: without Gauss's lemma, Λ could be strictly larger than the span of the shifts.)

**Lemma B (height lift).** For each grid edge u → v, let δ(u,v) ∈ {±1} be the integer with δ ≡ c̃(v) − c̃(u) (mod 3).

- Around each unit square the four δ's sum to a number in {−4, −2, 0, 2, 4} that is ≡ 0 (mod 3). That number must be 0. **This is the essential input** that the phrase "simply connected" leaves implicit.
- Any closed walk in Z^N can be reduced to the empty walk by two moves: deleting a backtrack u → v → u, and commuting two consecutive steps. Neither move changes the δ-sum.
- Hence h(x) := Σ_{path 0→x} δ is well defined, and:
  - h(x ± e_n) − h(x) = ±1;
  - h(x) − h(y) ≡ c̃(x) − c̃(y) (mod 3);
  - h(x) ≡ Σ x_n (mod 2);
  - |h(x) − h(y)| ≤ ‖x − y‖₁. ∎

**Lemma C (shifts).** For ℓ ∈ Λ, the quantity s(ℓ) := h(x+ℓ) − h(x) does not depend on x.

*Proof.* c̃(·+ℓ) = c̃, so h(·+ℓ) and h have identical increments on every edge, and the grid is connected. ∎

Properties of s:

- s : Λ → Z is additive.
- s(ℓ) = h(ℓ) − h(0) ≡ c̃(ℓ) − c̃(0) = 0 (mod 3), by invariance.
- s(ℓ) ≡ Σ_n ℓ_n (mod 2).
- |s(ℓ)| ≤ ‖ℓ‖₁.

For ℓ_j we have Σ_n (ℓ_j)_n = f(1) = 1, which is odd. So τ_j := s(ℓ_j) is an **odd multiple of 3**, and |τ_j| ≤ ‖f‖₁ = 19, so τ_j ∈ {±3, ±9, ±15}.

**Lemma D (bounded slope).** There is σ ∈ [−1,1]^{K+1} with Σ_i a_i σ_{i+j} = τ_j for all 0 ≤ j ≤ K−12.

*Proof (Farkas).* Let A be the matrix with rows ℓ_j, and suppose {σ : Aσ = τ, ‖σ‖_∞ ≤ 1} is empty.

1. LP duality gives y with y·τ > max_{‖σ‖∞≤1} (Aᵀy)·σ = ‖Aᵀy‖₁.
2. The inequality is strict, so y can be taken rational, and then integral after scaling.
3. Then ℓ := Aᵀy = Σ y_j ℓ_j ∈ Λ, and s(ℓ) = y·τ > ‖ℓ‖₁ ≥ |s(ℓ)|, a contradiction. ∎

Equivalent formulations:

- Hahn–Banach: extend s from span Λ using the bound |s(v)| ≤ ‖v‖₁.
- "Averaging slopes", in the correct form: let σ^(R)_n be the mean of h(x+e_n) − h(x) over the box [−R,R]^{K+1}. Then σ^(R) ∈ [−1,1]^{K+1}, and σ^(R)·ℓ → s(ℓ) because boundary terms are O(‖ℓ‖₁/R). Any limit point is a valid σ.

**Converse.** If (σ, τ) is admissible, then G_K is 3-colourable. Put:

- p(x) := Σ x_n mod 2;
- h(x) := the element of 2Z + p(x) nearest to σ·x, with ties broken upward, i.e. h(x) = 2⌊(σ·x − p + 1)/2⌋ + p.

The equalities σ·ℓ_j = τ_j ≡ 3 (mod 6) extend additively to all ℓ ∈ Λ, giving σ·ℓ ∈ Z, σ·ℓ ≡ Σℓ_n (mod 2) and σ·ℓ ≡ 0 (mod 3). Hence:

- h(x + ℓ) = h(x) + σ·ℓ;
- h(x + e_n) − h(x) is odd and has absolute value < 3 (because h − σ·x ∈ (−1, 1] and |σ_n| ≤ 1), so it equals ±1.

Therefore h mod 3 is a proper, Λ-invariant colouring, i.e. a 3-colouring of G_K. ∎

Writing θ = (σ+3)/6, the criterion says: some character of M_K sends every step into [1/3, 2/3]. This is exactly the band-character criterion of kooshi/hadwiger-nelson, LEDGER row 79 (see Task 6).

## Task 4 — Certificate. Verdict: **valid; it proves that no admissible (σ, τ) exists for K = 79. Independently reproduced.**

**Format.** Node w = (τ_0, …, τ_{j−1}) stands for the set P_w ⊂ [−1,1]^12 of initial values x = σ_0..σ_11 for which every forced value σ_{12+k} = (τ_k − c_k(x))/2, k < j, lies in [−1,1].

**Soundness.** Suppose (σ, τ) is admissible with τ_0 > 0. We may assume τ_0 > 0, because (σ, τ) ↦ (−σ, −τ) preserves admissibility and τ_0 ≠ 0. Let w_j be its prefix of length j. Then x = σ_0..σ_11 lies in P_{w_j} for every j ≤ 68. Proceed by induction:

- w_j is present in the file.
- If w_j is an E-node, its Farkas inequality contradicts x ∈ P_{w_j}.
- If w_j is an I-node, then lb ≤ c_j(x) ≤ ub, and c_j(x) ∈ [τ_j − 2, τ_j + 2]. So the slab of τ_j meets [lb, ub]. Also τ_j ∈ T = {±3, ±9, ±15} by the a priori bound |τ_j| ≤ 19. Hence w_{j+1} is a required child and must be present.
- I-nodes have depth < 68, so the chain must end in a contradiction.

The bound |τ| ≤ 19 is a theorem rather than an assumption. Moreover |c_j| ≤ Σ_{i<12}|a_i| = 17, so τ = ±21 could never meet a slab anyway.

**Results.**

1. **My exact checker** (`referee/ref_check.py`). Integer arithmetic with power-of-two denominators. It walks only the *required* children starting from the root, and checks multiplier indices 0 ≤ k < j.
   - On `runs/proof_fB_L68.jsonl` (sha256 19602d8d…b27e, verified) with L = 68: **PASS**. All 75,530 nodes are I-nodes; there are 0 E-nodes; max depth 67; 0 unreferenced nodes; 19.5 s.
   - Depth histogram: it peaks at 3,386 nodes at depth 21, and depth 67 has 2 nodes.
   - Negative control: with L = 67 the check fails at an I-node of depth 67, as it must, since K = 78 is feasible.
2. **Independent search** (`referee/my_dfs_glpk.py`). Built from scratch with a different solver, formulation and certificate:
   - Solver: GLPK 5.0, not HiGHS.
   - Formulation: all variables σ_0..σ_{j+11} are kept, with equality rows, instead of eliminating them.
   - Certificate: a polynomial multiplier y(x) with c_j ≤ y·τ + ‖x^j(f − 2x^12) − y·f‖₁, with the exact bound computed from rationalised duals.
   - Result: **75,530 nodes, exactly the same set of τ-prefixes as the claimant's**, maximum depth 67, no feasible word of length 68. Took 67.7 s.
   - The separate exact verifier `referee/verify_polycert.py` reports **PASS** (89 s).
3. **No symmetry reduction.** The same search without the τ_0 > 0 restriction finds 151,059 = 2·75,530 − 1 nodes. The verifier reports PASS. So the symmetry argument is not even needed.
4. **Deepest nodes.** The two depth-67 words (τ_0 > 0) use only ±3. They are mirror images of each other (reverse the word and negate it; f is palindromic). Their certified ranges of c_67 are [0.1907, 0.3782] and [0.2967, 0.8818]. Both lie inside the gap (−1, 1), so σ_79 cannot exist.
5. **Third method (MILP, SCIP 10.1.0, official binary):**
   - Floating-point mode: K = 79 infeasible (176.9 s, 532,082 nodes); K = 78 feasible (92.6 s).
   - Exact rational mode: K = 78 feasible (1,142 s); my own code checks the rational solution exactly. The exact K = 79 run did not finish; I stopped it after 4,796 s and 17.4 M nodes with no solution found. It is inconclusive, and the exact infeasibility proof for K = 79 therefore rests on the two tree certificates in items 1 and 2.
6. **Threshold K = 78 is feasible**, by three exact certificates:
   - the claimant's `runs/fB_K78_feasible_cert.json`, recomputed exactly: max |σ| = 0.992686;
   - SCIP's floating solution turned into an exact certificate (max-margin LP, margin 0.00731, rationalised and recomputed): `referee/outputs/my_K78_cert_from_scip.json`;
   - SCIP's exact rational solution.

   All three use the same word, up to symmetry. With the converse (Task 3), G_78 is 3-colourable.
7. **For information only:** the claimant's `check_proof.py` also passes (89.7 s). I do not rely on it.
8. **Falsification attempt** (`referee/quotient_attack.py`). I searched for 3-colourings coming from finite quotients, which by the paper's Lemma 2.3 would refute the claim:
   - ring maps Z[α] → Z/N with N ≤ 1500 (589 roots t): none;
   - all characters of R_m(f) for every m with φ(m) ≤ 24 and |R_m(f)| ≤ 4·10⁵ (33 orders): none.

   As a positive control of the σ ↔ character dictionary, the paper's norm-31 character for 2x^6−2x^4+x^3−2x^2+2 gives an admissible period-8 (σ, τ).

## Task 5 — Sanity check on f0 = x^6 − x^4 − x^3 − x^2 + 1. Verdict: **the criterion agrees with the paper: threshold K = 12**

Script: `referee/f0_sanity.py`; output in `referee/outputs/f0_sanity.out`. Additional runs: `my_dfs_glpk.py`/`verify_polycert.py` on f0, SCIP exact, and VIPR.

- **K = 11 is feasible.** The pair σ = (1,−1,1,−1,−1,−1,1,1,1,−1,1,−1), τ = (3,3,3,−3,−3,−3) is exact.
  - My GLPK search finds the same word.
  - SCIP exact finds it, and the VIPR checker `viprchk` verifies the result.
  - The rounding colouring built from it is well-defined (20,000 random relation tests) and proper on all 4,828 edges of the paper's 830-vertex sumset with exponents ≤ 11, and on 20,000 random vertices × 24 neighbours.
  - It is monochromatic on 20 exponent-12 edges, as it must be.
- **K = 12 is infeasible.**
  - My polynomial certificate: 14 nodes, PASS.
  - SCIP exact: infeasible. `viprchk` reports "Successfully verified infeasibility" (with presolving, cuts, conflict analysis and propagation disabled; with cuts enabled, SCIP's certificate contains derivations that `viprchk` cannot parse).
- **The paper's witness** (`anc/sextic-witness.csv`):
  - 24 vertices and 51 edges with exponents ≤ 12, using every exponent 0..12;
  - not 3-colourable (my own backtracking);
  - its exponent-≤11 part is 3-colourable.
- **The 830-vertex sumset** (CaDiCaL 1.5.3 and Glucose 4 via pysat): 3-colourable with exponents ≤ 11; not 3-colourable with exponents ≤ 12 or ≤ 14. The ≤ 14 graph has 4,848 edges, matching the paper's count.

Both directions of the criterion therefore agree with the paper's 4-chromatic theorem and its 24-vertex witness. I did not re-run the claimant's 154-sextic classification.

## Task 6 — Novelty. Verdict: **the criterion is prior art (and the claimant says so). The counterexample polynomial and the certificate appear to be new.**

- **kooshi/hadwiger-nelson, `LEDGER.md` row 79.**
  - It states: a Cayley graph of a finitely generated torsion-free abelian group is 3-colourable ⟺ some character puts every generator in [1/3, 2/3]. This is the same criterion, via σ = 6θ − 3.
  - It has a Lean proof for every abelian group and every S ∌ 0: `CayleyThree.colorable_three_iff_bandSet_nonempty` in `Proofs/HadwigerNelson/CayleyThree/Circular.lean`, l.203, last changed 2026-10-16. The ⟸ direction is the circular colouring ⌊3{θ}⌋.
  - The claimant's citation of it is accurate.
- **kooshi's own notes** (`plans/POROS-2026-10-13-number-field-findings.md`, hunch "row-79-is-the-converse-davidson-lacks"; `FS131-PN1.md`; `FS131-PAS1.md`) observe that Conjecture 4.3 reduces to existence of such a character. They leave it as an open question and report no counterexample.
- **s66lem/conjectures and 1337isnot1337/solved-conjectures:** no file and no code-search hit for Davidson, 2610.09474, "monomial Cayley", or this polynomial.
- **GitHub code search** for the coefficient list and for F: no hits.
- **Citing works:**
  - OpenAlex W7221024409: cited_by_count = 0.
  - Semantic Scholar: returned 429 (rate limit), not checked.
  - arXiv API: "monomial Cayley" matches only the paper itself.
  - Web searches: nothing.
- **Open-problems catalogue** 10m-u/open-problems-catalog, Q4297: still "Open (no later resolution located, 11 October 2026)".
- **Author's site** (jjdavidson.github.io; last pushed 2026-11-17): no update on the conjecture.

---

## Issues found

None of these invalidates the claim.

1. **Reduction (b), "averaging slopes gives σ"** (the claimant's justification as relayed in the brief). As stated it is not a proof: M_K ≅ Z^12 is infinite, so there is no finite period cell to average over, and a 1-Lipschitz bound does not by itself produce a linear σ.
   *Fix:* Lemma D above (Farkas), or Følner-box averaging followed by a limit point.
2. **Reduction (b), "because the square complex is simply connected."** This is true but omits the step that makes it usable: the increment cochain must vanish on each square.
   *Fix:* four ±1's summing to a multiple of 3 must sum to 0 (Lemma B).
3. **`counterexample_fB.json`, `level_threshold` ("3-colourable for K=78") and `finite_witness` ("must contain an edge ±α^n with n ≥ 79").** Both use the *converse* of (b), which the claim neither states nor proves. It is true.
   *Fix:* add the rounding construction from Task 3, or cite the Lean theorem. For the finite witness, also note that the components of Cay(Z[α], {±α^n : n ≤ 78}) are translates of G_78.
4. **`check_proof.py` header (lines 3–5) versus the definition of `T`.** The header certifies "τ ∈ 3(2Z+1)", but the code enumerates only |τ| ≤ Σ|a_i| = 19. The restriction is valid, but it is an unstated lemma.
   *Fix:* state |τ_j| ≤ ‖f‖₁ in the header.
5. **`check_proof.py`, uses of `rws[k]` in both the E-branch and `ub()`.** Multiplier keys are not range-checked, so a negative key would silently index from the end of the list. This is not a soundness hole, since every row on the path is a valid constraint, and the present file has no such keys (my checker enforces 0 ≤ k < j and passes).
   *Fix:* `assert 0 <= k < j`.
6. **No explicit finite witness.** The lower bound rests on the criterion plus a computer certificate, not on a finite non-3-colourable subgraph like the paper's 24-vertex witness. One exists by de Bruijn–Erdős, and by Issue 3 it needs an edge with n ≥ 79. This is not an error.
   *Recommendation:* present the proof as "criterion (with its proof, or the Lean reference) + certificate + an independent checker", or try to extract a finite witness.
7. **Attribution, for any write-up.** The criterion is kooshi row 79. Its height-function ingredient is classical (Krebs–Sankar's winding homomorphism, Chandgotia's height functions, per kooshi's prior-art notes). The new content is f and the certificate.

## Computations

All runs used the venv in the scratch folder: Python 3.14.10, sympy 1.14.0, python-flint 0.9.0, numpy 2.5.5, swiglpk 5.0.13 (GLPK 5.0), pysat 1.9.dev25, PySCIPOpt 6.3.0. The SCIP 10.1.0 binary is from the official scipopt/scip GitHub release (glibc2_34 amd64); `viprchk` was built from scipopt/vipr commit 99eec197a4.

| # | Command or script | Result |
|---|---|---|
| 1 | `polyfacts.py` | Task 2 tables (1 s) |
| 2 | `ref_check.py '[2,2,1,-1,-2,-1,-1,-1,-2,-1,1,2,2]' 68 proof_fB_L68.jsonl` | PASS: 75,530 I-nodes, 0 E-nodes, max depth 67 (19.5 s); L = 67 fails as expected |
| 3 | `my_dfs_glpk.py … 68` and `verify_polycert.py` | 75,530 nodes, same set as the claimant's (67.7 s); PASS (89 s); my certificate sha256 880c4050…8f31 (83 MB, regenerable) |
| 4 | Same, `nosym` | 151,059 nodes (163 s); PASS |
| 5 | `check_feasible.py` on the claimant's K = 78 certificate | valid; max \|σ\| = 0.9926862 |
| 6 | SCIP float on `fB_K79.lp` / `fB_K78.lp` (from `write_lp.py`) | infeasible (176.9 s) / feasible (92.6 s) |
| 7 | `k78_from_scip.py` | exact K = 78 certificate, margin 0.00731 |
| 8 | SCIP exact, K = 78 | feasible (1,142 s); rational solution checked exactly |
| 9 | SCIP exact, K = 79 | stopped by me after 4,795.8 s and 17,443,279 nodes with no solution found; inconclusive |
| 10 | `fB_extras.py` | deepest-node ranges; rounding colouring of G_78: 0/3000 failures of invariance or properness |
| 11 | `quotient_attack.py 1500 400000` | no 3-colouring from finite quotients; positive control passes |
| 12 | `f0_sanity.py`, and `my_dfs_glpk`/`verify_polycert` on f0 for L = 5…8, SCIP exact + `viprchk` for K = 11, 12 | Task 5 results |
| 13 | Claimant's `check_proof.py`, for information only | passes (89.7 s) |

**Reproduction.** Copy the scripts from `referee/` into a folder that contains `data/proof_fB_L68.jsonl` and `data/fB_K78_feasible_cert.json`, then run them with `python3 -I`.
