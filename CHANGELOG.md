# Changelog

## v1.2 (26 Nov 2026)

The proof of the Theorem is unchanged.

- **Second check by GPT-6.2 Astra** ([`verification/astra_3f96a35/`](verification/astra_3f96a35/)), working from commit `3f96a35`:
  - It audited the Lean proof: the statement of the conjecture matches Davidson's definitions, a clean build reproduces the stated axioms, and corrupted certificates are rejected.
  - It found an explicit finite non-3-colourable subgraph: the image of the box $\{-10,\dots,10\}^{80}$, with fewer than $7.95\times10^{52}$ vertices. This is the new part of Remark 1 of the paper.
  - It showed that each of the 68 equations of Proposition 3 is needed. This is the new Remark 2.

  We re-checked the numerical claims with our own code and read the proof (`our_recheck/`).
- **Documentation fixes suggested by Astra.**
  - `lean/README.md` and `lean/STATEMENTS.md` now say "no `axiom` declaration" instead of "no new `axiom`", since `native_decide` adds one auxiliary axiom.
  - The claim "four separately written exact checkers" is now "three", namely those whose code is in this repository.
  - `lean/DavidsonLean/Test_Corrupt.lean` uses `#guard`, so it fails if a corrupted certificate is accepted. It also has a positive control.
- **Removed `REVIEW_GPT-6.2-Sol.md`.** Its re-check of the certificate was reported without code, so it cannot be reproduced. Everything it checked is covered by the Claude referee (`VERIFICATION.md`), the two Astra checks and the Lean proof, all with code. Its comments on the draft of v1 were already incorporated. The file remains in the git history.

## v1.1 (26 Nov 2026)

The mathematics is unchanged.

- **Lean formalization** ([`lean/`](lean/)). The refutation is the Lean theorem `conjecture43_false : ¬ Conjecture43`, with the conjecture stated as in §1 of the paper. The following are checked by the Lean kernel:
  - Lemma 2;
  - non-integrality of the roots of $f$;
  - the soundness of the certificate checker.

  Acceptance of the certificate uses `native_decide`. See `lean/README.md`.
- **Paper.** New paragraph "Formal verification" in §4, and a new bullet in the abstract.
- **Third independent check.** GPT-6.2 Astra's verification package, together with our re-run of it, is in [`verification/astra/`](verification/astra/).
- **Figures.** Pictures of finite pieces of $\Gamma_\alpha$ are in [`figures/`](figures/), with the script `code/draw_figures.py`. They are illustrations, not part of the proof.
- **Citation.** Added [`CITATION.cff`](CITATION.cff) and a BibTeX entry.

## v1 (26 Nov 2026)

First release.
