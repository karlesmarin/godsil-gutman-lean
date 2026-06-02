# Paper figures & tables (formalization pearl)

Professional, colour-coded, vector (PDF) + raster (PNG, 300 dpi) assets.
Regenerate any figure with `python3 fig_style.py`-styled scripts. Palette in `fig_style.py`
(teal `#1b6f8c` = positive edge, red `#c1452e` = negative edge, amber accent).

| asset | what it shows |
|---|---|
| `fig1_godsil_gutman` | **Godsil–Gutman** on $K_3$: signings (teal `+` / red `-`) → charpolys → average $= \mu_{K_3}=x^3-3x$. The flagship identity (`godsil_gutman`, proven). |
| `fig2_ramanujan_bound` | **Heilmann–Lieb**: matching-polynomial roots (computed) inside the banded $[-2\sqrt{\Delta-1},2\sqrt{\Delta-1}]$ Ramanujan threshold, for $K_3,C_5,K_4,$ Petersen, $K_{1,4}, K_{3,3}$. Where the story ends. |
| `fig3_zmod2_principle` | **The $\mathbb{Z}/2$ engine**: one sign-averaging fact (`sum_signOf_pow`) feeding the charpoly-level (Godsil–Gutman, proven) and moment-level (parity-walk kernel) results. HONEST: a shared atomic lemma, not a single meta-theorem; the parity gate is downstream of the moment kernel. |
| `fig4_path_tree` | **The proposed next step**: Godsil's path-tree $T(G,u)$ of the diamond (root $u$, amber) — a forest, so $\mu_T=\det(xI-A_T)$, and $\mu_G\mid\mu_{T(G,u)}$; together these give Heilmann–Lieb. HONEST: mapped, **not yet formalized**. |
| `tables.tex` | Table 1: formalised results (Lean names, statements, status). Table 2: SymPy cross-checks (avg charpoly $=\mu_G$; avg $\mathrm{tr}(A^4)=P_4$). booktabs, colour (teal header band, zebra rows). |

## Honesty notes baked into the assets (from the Socratic stress-test)
- Fig 3 does **not** draw an arrow gate→`godsil_gutman` (no false formal derivation); the unification is a *shared atomic lemma*, stated as such.
- Table 1 marks Heilmann–Lieb / interlacing families as **future**, not proven.
- Fig 4 (path-tree) caption + title say **mapped, not yet formalized**; the divisibility and forest facts are stated as the classical route, not as Lean results.
- Fig 1's caption is the textbook $2^{-|E|}$ edge-average; the Lean statement sums over `Sym2 V` (free non-edge bits) with `#cfg`$=2^{|\mathrm{Sym2}\,V|}$ — equivalent, noted in the paper text.
