# Lean formalization: Conjecture 4.3 is false

The code uses Lean 4.37.0-rc1 and Mathlib v4.37.0-rc1. No file contains `sorry`, `admit` or a new `axiom`. [`STATEMENTS.md`](STATEMENTS.md) lists every theorem with its exact Lean statement, the sentence of the paper it formalizes, and every difference.

## Main theorem

```lean
/-- Γ_α = Cay(ℤ[α], {±α^n : n ≥ 0}) on the subring ℤ[α] ⊂ ℂ -/
def Davidson.Gamma (α : ℂ) : SimpleGraph (Algebra.adjoin ℤ ({α} : Set ℂ)) where
  Adj z w := z ≠ w ∧ ∃ n : ℕ, (w : ℂ) - z = α ^ n ∨ (z : ℂ) - w = α ^ n

/-- Davidson's Conjecture 4.3: every algebraic noninteger direction parameter α has χ(Γ_α) ≤ 3. -/
def Davidson.Conjecture43 : Prop :=
  ∀ α : ℂ, ‖α‖ = 1 → IsAlgebraic ℚ α → ¬ IsIntegral ℤ α → (Gamma α).chromaticNumber ≤ 3

theorem Davidson.conjecture43_false : ¬ Conjecture43

theorem Davidson.root_counterexample (α : ℂ) (hα : Polynomial.aeval α Poly.f = 0) :
    ‖α‖ = 1 ∧ IsAlgebraic ℚ α ∧ ¬ IsIntegral ℤ α ∧ 4 ≤ (Gamma α).chromaticNumber
```

Here `Poly.f` is $f=2x^{12}+2x^{11}+x^{10}-x^9-2x^8-x^7-x^6-x^5-2x^4-x^3+x^2+2x+2$. A *direction parameter* is a unit complex number. *Noninteger* means "not an algebraic integer", which is the paper's §1 wording ("$a_d\ge2$, i.e. $\alpha$ is not an algebraic integer").

| Module | Content | Checked by |
|---|---|---|
| `Conjecture` | The conjecture as stated in the paper, its refutation, and the claim that every root of $f$ is a counterexample | Lean kernel, plus `prop3` |
| `NonInteger` | No root of $f$ is an algebraic integer: $F$ is irreducible modulo 3, and $\alpha+\alpha^{-1}$ is a root of $F$ | Lean kernel |
| `Gamma` | $\Gamma_\alpha$, pull-back of a colouring to the grid $\mathbb Z^{80}$, and the result that $\Gamma_\alpha$ is not 3-colourable | Lean kernel, plus `prop3` |
| `Criterion`, `Height`, `Extension` | **Lemma 2** (necessity of the three-colour criterion) for every $K$: height function, constant shifts, Hahn–Banach | Lean kernel |
| `Prop3`, `Checker`, `Parse`, `CertData` | **Proposition 3** in the paper's exact form | Soundness of the checker: Lean kernel. Acceptance of the 75,530-node certificate: `native_decide`. |
| `Sharp78` | The finite $K=78$ system behind sharpness has a solution; the proof exhibits an exact rational one | Lean kernel (`decide +kernel`) |
| `Poly` | §2 facts about $f$ and $F$ | Lean kernel |

The §2 facts in `Poly` are:

- the coefficients of $f$, its degree 12 and leading coefficient 2;
- the identity $f(x)=x^6F(x+x^{-1})$;
- six distinct real roots of $F$ in $(-2,2)$;
- every root of $f$ has modulus 1 and is not real.

## Trust base

`#print axioms Davidson.conjecture43_false` gives:

```
[propext, Classical.choice, Quot.sound, Davidson.cert_ok._native.native_decide.ax_1_1]
```

The last axiom is the one `native_decide` adds:

```
Davidson.cert_ok._native.native_decide.ax_1_1 : decide (checkRoot cert = true) = true
```

It states only that the checker accepts the embedded certificate. Lean establishes this by running compiled code, so the Lean compiler and runtime are trusted for this one step. Four separately written exact checkers also accept the same certificate: ours, the Claude referee's, GPT-6.2 Sol's and GPT-6.2 Astra's (see the repository README). Everything else is checked by the Lean kernel:

- the soundness of the checker, which holds for every tree;
- Lemma 2;
- non-integrality;
- the bridge to $\Gamma_\alpha$;
- the final assembly.

## Not formalized, and not needed for the refutation

- **The upper bound $\chi(\Gamma_\alpha)\le4$**, which is Davidson's Theorem 4.1. So Lean proves $\chi\ge4$, not $\chi=4$.
- **Irreducibility of $f$ over $\mathbb Q$.** The Lean proof of non-integrality goes through $F$ modulo 3 instead.
- **Equivalence of the two forms of "noninteger".** The paper's first form is "$a_d\ge2$ for the primitive minimal polynomial"; it is equivalent to "not an algebraic integer" by Gauss's lemma, which is classical.
- **Lemma 1 in full and Lemma 2′**, which are used only for sharpness.

## Building

```bash
cd lean
python3 tools/convert_cert.py ../certificate/proof_fB_L68.jsonl.gz DavidsonLean/data/cert_L68.txt
sha256sum DavidsonLean/data/cert_L68.txt   # 89632a5f190cf60b3adbdeffcbb3d83bc6e7da10140d4d629aa38e6b1439054b
lake exe cache get                         # prebuilt Mathlib
lake build                                 # about 50 s after Mathlib
lake env lean DavidsonLean/Conjecture.lean # prints the axioms of conjecture43_false
lake env lean DavidsonLean/Test_Corrupt.lean   # negative tests: corrupted certificates are rejected
```

## How this was produced

Claude (Opus 5.5) agents wrote the Lean code in three rounds:

1. the certificate checker, Proposition 3, sharpness and the polynomial facts;
2. Lemma 2 and $\Gamma_\alpha$;
3. non-integrality and the statement of the conjecture.

The coordinating Claude session audited each round:

- compared every definition and statement with the paper;
- checked for `sorry`, extra axioms and kernel-skipping options;
- rebuilt the project from a clean state;
- regenerated the certificate data from the published certificate and got an identical SHA-256;
- ran tests showing that corrupted certificates are rejected.
