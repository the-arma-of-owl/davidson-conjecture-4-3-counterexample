# Lean formalization

The code uses Lean 4.37.0-rc1 and Mathlib v4.37.0-rc1. No file contains `sorry`, `admit` or a new `axiom`. [`STATEMENTS.md`](STATEMENTS.md) lists every theorem with its exact Lean statement, the sentence of the paper it formalizes, and every difference.

## Main theorem

```lean
def Davidson.Gamma (α : ℂ) : SimpleGraph (Algebra.adjoin ℤ ({α} : Set ℂ)) where
  Adj z w := z ≠ w ∧ ∃ n : ℕ, (w : ℂ) - z = α ^ n ∨ (z : ℂ) - w = α ^ n

theorem Davidson.gamma_not_colorable (α : ℂ) (hα : Polynomial.aeval α Poly.f = 0) :
    ¬ (Gamma α).Colorable 3
theorem Davidson.four_le_chromaticNumber (α : ℂ) (hα : Polynomial.aeval α Poly.f = 0) :
    4 ≤ (Gamma α).chromaticNumber
```

`Gamma α` is $\Gamma_\alpha=\mathrm{Cay}(\mathbb Z[\alpha],\{\pm\alpha^n:n\ge0\})$ on the subring $\mathbb Z[\alpha]\subset\mathbb C$. For every root $\alpha$ of $f$ the graph is not 3-colourable. This is the lower bound in the paper's Theorem, formalized from end to end.

| Module | Content | Checked by |
|---|---|---|
| `Gamma` | $\Gamma_\alpha$, the pull-back of a colouring to the grid $\mathbb Z^{80}$, and the main theorem | Lean kernel, plus `prop3` |
| `Criterion`, `Height`, `Extension` | **Lemma 2** (necessity direction of the three-colour criterion) for every $K$: height function on the grid, constant shifts along the relations, Hahn–Banach | Lean kernel |
| `Prop3`, `Checker`, `Parse`, `CertData` | **Proposition 3**, in the paper's exact form | Soundness of the checker: Lean kernel. Acceptance of the 75,530-node certificate: `native_decide`. |
| `Sharp78` | The finite $K=78$ system behind sharpness has a solution. The proof exhibits an exact rational one. | Lean kernel (`decide +kernel`) |
| `Poly` | §2 facts about $f$ and $F$ (listed below) | Lean kernel |

The §2 facts are:

- the coefficients of $f$, its degree 12 and leading coefficient 2;
- $f(1)=1$ and $f(0)=2$;
- the identity $f(x)=x^6F(x+x^{-1})$;
- six distinct real roots of $F$ in $(-2,2)$, and every complex root of $F$ is real and lies there;
- every complex root of $f$ has modulus 1 and is not real.

## Trust base

`#print axioms Davidson.gamma_not_colorable` gives:

```
[propext, Classical.choice, Quot.sound, Davidson.cert_ok._native.native_decide.ax_1_1]
```

The last axiom is the one `native_decide` adds:

```
Davidson.cert_ok._native.native_decide.ax_1_1 : decide (checkRoot cert = true) = true
```

It states only that the checker accepts the embedded certificate. Lean establishes this by running compiled code, so the Lean compiler and runtime are trusted for this one step. Everything else is checked by the Lean kernel:

- the soundness of the checker, which holds for every tree, so the parser and data need no trust;
- Lemma 2;
- the bridge to $\Gamma_\alpha$.

`Davidson.lemma2` and `Davidson.necessity` depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Not formalized

- **That $\alpha$ is an algebraic noninteger,** the hypothesis of Davidson's Conjecture 4.3. This follows from the irreducibility of $f$ over $\mathbb Q$ (§2). We checked irreducibility with computer algebra, and both referees checked it with a short hand argument, but not in Lean. The Lean theorem itself holds for every root of $f$.
- **The upper bound $\chi(\Gamma_\alpha)\le4$** (Davidson's Theorem 4.1). It is not needed to refute the conjecture.
- **Lemma 1 in full and Lemma 2′.** They are used only for sharpness, i.e. that the $K=78$ graph is 3-colourable. `Sharp78` formalizes the finite system behind it.

## Building

```bash
cd lean
python3 tools/convert_cert.py ../certificate/proof_fB_L68.jsonl.gz DavidsonLean/data/cert_L68.txt
sha256sum DavidsonLean/data/cert_L68.txt   # 89632a5f190cf60b3adbdeffcbb3d83bc6e7da10140d4d629aa38e6b1439054b
lake exe cache get                         # prebuilt Mathlib
lake build                                 # about 50 s after Mathlib
lake env lean DavidsonLean/Gamma.lean      # prints the axioms of the main theorem
lake env lean DavidsonLean/Test_Corrupt.lean   # negative tests: corrupted certificates are rejected
```

## How this was produced

Claude (Opus 5.5) agents wrote the Lean code in two rounds:

1. the certificate checker, Proposition 3, sharpness and the polynomial facts;
2. Lemma 2 and the main theorem.

The coordinating Claude session audited each round:

- compared every statement with the paper;
- checked for `sorry`, extra axioms and kernel-skipping options;
- rebuilt the project from a clean state;
- regenerated the certificate data from the published certificate and got an identical SHA-256;
- ran tests showing that corrupted certificates are rejected.
