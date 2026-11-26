# Changelog

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
