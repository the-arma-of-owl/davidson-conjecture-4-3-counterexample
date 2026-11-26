# Davidson's Conjecture 4.3 is false: a non-3-colourable monomial Cayley graph with an algebraic noninteger parameter

**Paper:** [`paper/counterexample.md`](paper/counterexample.md) · **Independent verification:** [`VERIFICATION.md`](VERIFICATION.md), [`REVIEW_GPT-6.2-Sol.md`](REVIEW_GPT-6.2-Sol.md) · **Certificate:** [`certificate/`](certificate/)

## Result

For a unit complex number $\alpha$, $\Gamma_\alpha=\mathrm{Cay}(\mathbb Z[\alpha],\{\pm\alpha^n:n\ge0\})$ is a unit-distance graph in the plane. J. Davidson ([arXiv:2610.09474](https://arxiv.org/abs/2610.09474), Oct 2026) proved $\chi(\Gamma_\alpha)\le4$ for algebraic nonintegers $\alpha$, and conjectured that three colours always suffice (**Conjecture 4.3**).

> **Theorem.** For every root $\alpha$ of
> $$f(x)=2x^{12}+2x^{11}+x^{10}-x^{9}-2x^{8}-x^{7}-x^{6}-x^{5}-2x^{4}-x^{3}+x^{2}+2x+2$$
> (all twelve roots lie on the unit circle), $\chi(\Gamma_\alpha)=4$. Hence Conjecture 4.3 is false.

- $f$ satisfies every necessary condition for a counterexample that Davidson derived: Prop. 4.5, and degree at least $10$.
- **Proof.** Three-colourings of an abelian Cayley graph correspond to characters that put every generator in $[1/3,2/3]$. This criterion is due to [kooshi/hadwiger-nelson](https://github.com/kooshi/hadwiger-nelson), row 79, with a Lean proof of the direction we use. It reduces 3-colourability of the subgraph spanned by $1,\alpha,\dots,\alpha^{79}$ to finitely many linear programs.
- **Certificate.** An exact certificate shows that all of these programs are infeasible: 75,530 nodes with rational Farkas multipliers.
- **Sharpness.** The subgraph spanned by $1,\dots,\alpha^{78}$ is 3-colourable.

## Özet (Türkçe)

Davidson (Ekim 2026), birim karmaşık $\alpha$ için tanımlanan $\Gamma_\alpha$ birim-uzaklık graflarında, $\alpha$ cebirsel tamsayı değilse 3 rengin yeteceğini öne sürdü (Sanı 4.3).

Bu sanı yanlıştır. Yukarıdaki 12. dereceden $f$'nin her kökü için $\chi(\Gamma_\alpha)=4$ olur. Kanıt iki parçadan oluşur:

- **Ölçüt.** Üç renklendirmeyi karakterlerle ilişkilendiren ölçüt (Lean'de biçimselleştirilmiş).
- **Sertifika.** 75.530 düğümlü, kesin rasyonel sayılarla yazılmış bir sertifika.

İki bağımsız hakem sertifikayı baştan kontrol etti.

## Verifying

```bash
cd certificate && gunzip -k proof_fB_L68.jsonl.gz && sha256sum -c SHA256SUMS --ignore-missing
cd .. && python3 code/check_proof.py "[2,2,1,-1,-2,-1,-1,-1,-2,-1,1,2,2]" 68 certificate/proof_fB_L68.jsonl
# -> proof OK ... => no valid word of length 68 with tau_0 > 0 exists   (about 1–3 minutes, pure Python fractions)
```

## How this was produced

- **Direction.** Efe Çam directed the work.
- **Search and certificate.** A Claude (Anthropic) agent, running in Claude Code, did the search, derived the criterion, and wrote the certificate generator and checker. It found the criterion independently; only afterwards did it learn that the criterion is already recorded, with a Lean proof, in kooshi/hadwiger-nelson. That work is credited throughout.
- **Verification.** A separate Claude instance refereed the claim from scratch and re-implemented the checks ([`VERIFICATION.md`](VERIFICATION.md)). GPT-6.2 Sol (OpenAI) refereed it independently and re-checked all 75,530 nodes in exact arithmetic ([`REVIEW_GPT-6.2-Sol.md`](REVIEW_GPT-6.2-Sol.md)).

Errors are possible. Please open an issue if you find one.

## Citation / Atıf

```bibtex
@misc{cam2026davidson,
  author       = {{\c{C}}am, Efe},
  title        = {A counterexample to {D}avidson's {C}onjecture 4.3: a non-3-colourable monomial {C}ayley graph with an algebraic noninteger direction parameter},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://github.com/the-arma-of-owl/davidson-conjecture-4-3-counterexample}},
  note         = {Version 1}
}
```

The same metadata is in [`CITATION.cff`](CITATION.cff), which GitHub uses for its “Cite this repository” button. Atıf için bu BibTeX kaydını ya da GitHub'daki “Cite this repository” düğmesini kullanabilirsiniz.

## License

Text and data: CC BY 4.0. Code: MIT.
