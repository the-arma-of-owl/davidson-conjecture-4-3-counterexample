# Lean formalization of the finite core

Lean 4.37.0-rc1 with Mathlib v4.37.0-rc1. No file contains `sorry`, `admit` or a new `axiom`. [`STATEMENTS.md`](STATEMENTS.md) lists every theorem with its exact Lean statement, the sentence of the paper it formalizes, and every difference.

| Module | What it proves | Checked by |
|---|---|---|
| `DavidsonLean.Prop3` | **Proposition 3** in the paper's exact form, over ℝ: there is no $\sigma\in[-1,1]^{80}$ with $\sum_{i=0}^{12}a_i\sigma_{i+j}\in3(2\mathbb Z+1)$ for all $0\le j\le67$. | Soundness of the certificate checker: Lean kernel. Acceptance of the 75,530-node certificate: `native_decide`. |
| `DavidsonLean.Sharp78` | Sharpness: the same system for $K=78$ (79 unknowns, 67 equations) has a solution. The proof exhibits an exact rational one. | Lean kernel (`decide +kernel`). |
| `DavidsonLean.Poly` | §2 facts about $f$ and $F$. | Lean kernel. |

The §2 facts are:

- the coefficients of $f$, its degree 12 and leading coefficient 2;
- $f(1)=1$ and $f(0)=2$;
- the identity $f(x)=x^6F(x+x^{-1})$;
- six distinct real roots of $F$ in $(-2,2)$, and every complex root of $F$ is real and lies in $(-2,2)$;
- every complex root of $f$ has modulus 1 and is not real.

## Trust base

`#print axioms Davidson.prop3` gives:

```
[propext, Classical.choice, Quot.sound, Davidson.cert_ok._native.native_decide.ax_1_1]
```

The last axiom is the one `native_decide` adds:

```
Davidson.cert_ok._native.native_decide.ax_1_1 : decide (checkRoot cert = true) = true
```

It states only that the checker accepts the embedded certificate. Lean establishes this by running compiled code, so the Lean compiler and runtime are trusted for this one step. The soundness theorem `prop3_of_check : checkRoot c = true → Prop3Statement` is kernel-checked and holds for **every** tree `c`. The parser, the converter and the data file therefore do not need to be trusted.

All other theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Not formalized

- Lemma 1 (relations), and Lemmas 2 and 2′ (the three-colour criterion).
- Irreducibility of $f$, and Davidson's filters.
- Hence the main theorem $\chi(\Gamma_\alpha)=4$ itself.

The forward direction of the criterion is formalized in [kooshi/hadwiger-nelson](https://github.com/kooshi/hadwiger-nelson), which is not connected to this code.

## Building

```bash
cd lean
python3 tools/convert_cert.py ../certificate/proof_fB_L68.jsonl.gz DavidsonLean/data/cert_L68.txt
sha256sum DavidsonLean/data/cert_L68.txt   # 89632a5f190cf60b3adbdeffcbb3d83bc6e7da10140d4d629aa38e6b1439054b
lake exe cache get                         # prebuilt Mathlib
lake build                                 # about 45 s after Mathlib
lake env lean DavidsonLean/Prop3.lean      # prints the axioms above; runs native_decide (about 35 s)
lake env lean DavidsonLean/Test_Corrupt.lean   # negative tests: corrupted certificates are rejected
```

## How this was produced

- **Writing.** A Claude (Opus 5.5) agent wrote the Lean code.
- **Checking.** The coordinating Claude session then did the following:
  - read every file;
  - compared each statement with the paper;
  - rebuilt everything from a clean state in this standalone project;
  - regenerated the certificate data from the published certificate and got an identical SHA-256;
  - confirmed that corrupted certificates are rejected.
