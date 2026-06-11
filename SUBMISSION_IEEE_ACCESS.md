# IEEE Access submission package — ready to paste

Submission portal (Atypon): https://ieee.atyponrex.com/journal/ieee-access
Main file: `ieee-census.pdf`  ·  Source: `ieee-census.tex` (self-contained: inline TikZ figure,
inline `thebibliography`, IEEEtran class). APC applies on acceptance (~US$2,160).

## Title
Certified Short-Cycle Diagnostics for Deployed LDPC Codes: From WiFi to Quantum, with a
Covering-Tower Factorization

## Author
Carles Marin -- Independent researcher -- karlesmarin@gmail.com -- ORCID 0009-0007-5637-9688

## Abstract (plain text)
Short cycles in the Tanner graph of a low-density parity-check (LDPC) code degrade
belief-propagation (BP) decoding, and counting them is a standard step in code design and
evaluation. This paper does not count them faster. It contributes a short-cycle diagnostic
whose defining identity is a machine-checked theorem -- the trace-formula gap law
tr(A^k) - p_k = tr(B^k), with A the adjacency matrix, B the Hashimoto non-backtracking operator
and p_k the power sums of the matching-polynomial roots -- and whose per-code outputs are
validated by three mutually independent computations that agree exactly. We report a certified
census of the four deployed LDPC codes of the IEEE 802.11n (WiFi) standard at block length
n=648, and, to our knowledge the first such diagnostic on a quantum LDPC code, of the IBM
"gross code" [[144,12,12]] bivariate-bicycle (BB) code, finding girth 6 and c_6=144 shortest
cycles. We then give a covering-tower factorization: a BB code whose Tanner graph is a double
cover of a smaller code's inherits its short-cycle profile through the classical Artin-Ihara /
2-lift identity tr B^k(cover) = tr B^k(base) + tr B_s^k(base), verified exactly on the
gross/[[72,12,6]] pair (c_6 doubles, 144 = 2*72). The contribution is the theorem-backed,
cross-validated, reproducible methodology and its transfer from classical to quantum codes; the
underlying mathematics is classical and is not claimed as new. We are explicit about what the
certificate does and does not guarantee.

## Index terms / keywords
LDPC codes; quantum LDPC codes; Tanner graph; girth; short-cycle enumeration; belief
propagation; non-backtracking operator; bivariate bicycle codes; formal verification;
reproducible computation.

## Cover letter
Dear IEEE Access Editors,

Please consider the enclosed manuscript, "Certified Short-Cycle Diagnostics for Deployed LDPC
Codes: From WiFi to Quantum, with a Covering-Tower Factorization," for publication in IEEE
Access.

The manuscript contributes a short-cycle diagnostic for LDPC Tanner graphs whose defining
counting identity is a machine-checked theorem (verified in the Lean 4 proof assistant) and
whose per-code outputs are validated by three mutually independent computations. We apply it
to the four deployed IEEE 802.11n LDPC codes and, to our knowledge for the first time, to a
deployed quantum LDPC code (the IBM gross code [[144,12,12]]), and we give a covering-tower
factorization that lifts the short-cycle profile across a bivariate-bicycle code family.

The work has not been published and is not under consideration elsewhere. Earlier components
are available as preprints on Zenodo (the IEEE 802.11n census, doi:10.5281/zenodo.20649056,
and the underlying theory, doi:10.5281/zenodo.20648488); the present manuscript is the unified,
extended version. The cycle censuses were computed with AI assistance, disclosed in the
manuscript; the mathematics and all claims are the author's responsibility. All code is
open-source (https://github.com/karlesmarin/godsil-gutman-lean) and the results are
reproducible. The manuscript is explicit about the scope of the certificate.

Thank you for your consideration.

Sincerely,
Carles Marin (independent researcher)

## Declarations the portal will ask
- Previously published / under review elsewhere? -> NO (preprints on Zenodo, disclosed above).
- Generative-AI use -> disclosed in the manuscript footnote (computation assistance).
- Conflicts of interest -> none. Funding -> none.
- Suggested reviewers (optional) -> coding-theory / quantum-error-correction researchers.

## Files to upload
1. ieee-census.pdf (main manuscript).
2. ieee-census.tex (LaTeX source; required at submission or acceptance).
3. No external figure/bib files (figure is inline TikZ; bibliography is inline).
Note: if the system requires the official IEEE Access template, the manuscript can be moved
onto it (it is IEEEtran-based) before the final version.
