# engrXiv (Engineering Archive) submission package — ready to paste

Server: https://engrxiv.org  ·  Submit via free account (no institutional affiliation required).
Main file: `ieee-census.pdf` (venue-neutral preprint; title page already says "Preprint — June 2026",
no IEEE Access branding). Source: `ieee-census.tex`.

---

## ✅ Conditions verified (2026-06-12) — no traps

| Item | Status |
|------|--------|
| **Cost** | **FREE.** No submission fee, no APC, no charge ever. |
| **License** | Default **CC BY 4.0** (author keeps copyright; grants engrXiv a non-exclusive perpetual distribution right). This is what we want — maximum reach for engineers. |
| **Scope** | Broad engineering, incl. Electrical & Computer Eng / Communications. Deployed WiFi 802.11n + 5G LDPC = squarely in scope. |
| **Moderation** | ~3 business days; checks **relevance + categorization + legal rights only**, NOT technical merit / novelty / peer review. Lower friction than arXiv (no endorsement). |
| **Preprint duplication** | Allowed. Work is already on Zenodo as preprint — permitted; we disclose it. |
| **Already published?** | NO. Withdrawn from IEEE Access (manuscript Access-2026-28409); not under review anywhere. ⚠️ Post only AFTER the IEEE withdrawal is confirmed, so it is genuinely "not under consideration elsewhere." |
| **AI disclosure** | Kept verbatim in manuscript footnote (computation assistance; math = author's responsibility). |

Net: free, open, no endorsement, no gatekeeping on merit. Clean route.

---

## Paste-ready metadata

### Title
Certified Short-Cycle Diagnostics for Deployed LDPC Codes: From WiFi to Quantum, with a
Covering-Tower Factorization

### Author
Carles Marín — Independent researcher — karlesmarin@gmail.com — ORCID 0009-0007-5637-9688
(no institutional affiliation; leave affiliation blank or "Independent researcher")

### Abstract (plain text)
Short cycles in the Tanner graph of a low-density parity-check (LDPC) code degrade
belief-propagation (BP) decoding, and counting them is a standard step in code design and
evaluation. This paper does not count them faster. It contributes a short-cycle diagnostic
whose defining identity is a machine-checked theorem — the trace-formula gap law
tr(A^k) - p_k = tr(B^k), with A the adjacency matrix, B the Hashimoto non-backtracking operator
and p_k the power sums of the matching-polynomial roots — and whose per-code outputs are
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

### Keywords / index terms
LDPC codes; quantum LDPC codes; Tanner graph; girth; short-cycle enumeration; belief
propagation; non-backtracking operator; bivariate bicycle codes; formal verification;
reproducible computation.

### Subject classification (engrXiv categories)
Primary: Electrical and Computer Engineering → Communications / Information Theory
Secondary: Electrical and Computer Engineering → Signal Processing (optional)

### License (select on upload)
**CC BY 4.0** (recommended — broadest reuse, keeps attribution).

---

## Disclosures the form will ask
- Previously published / under review elsewhere? → **NO** (withdrawn from IEEE Access; earlier
  components are Zenodo preprints, disclosed below).
- Conflicts of interest → **none**.  Funding → **none**.
- Generative-AI use → disclosed in the manuscript footnote (computation assistance only; the
  mathematics, the theorem, and all claims are the author's responsibility).
- Related preprints (cite in the "comments" / cover field):
  - IEEE 802.11n census — doi:10.5281/zenodo.20649056
  - Underlying gap-window theory (Part VI) — concept doi:10.5281/zenodo.20648488
  - Open-source code & Lean proof — https://github.com/karlesmarin/godsil-gutman-lean

---

## Files to upload
1. `ieee-census.pdf` — main manuscript (self-contained: inline TikZ figure, inline bibliography).
2. (optional) `ieee-census.tex` — source, if a source copy is wanted; not required by engrXiv.
No external figure/bib files needed.

---

## Submission flow (engrXiv)
1. Create / log in to an engrxiv.org account (free; ORCID login works — use 0009-0007-5637-9688).
2. Start a new preprint → upload `ieee-census.pdf`.
3. Paste Title, Abstract, Keywords above.
4. Add author: Carles Marín, ORCID, "Independent researcher".
5. Pick subject classification (Electrical and Computer Engineering → Communications).
6. Select license **CC BY 4.0**.
7. In the comments/notes field, paste the "Related preprints" lines (Zenodo DOIs + GitHub).
8. Submit → moderation ~3 business days → DOI issued on acceptance.

## One pre-flight check before posting
Confirm the IEEE Access withdrawal email has been sent / acknowledged, so the "not under
consideration elsewhere" answer is true at posting time. (It was sent 2026-06-12 — fine to
proceed once you have the acknowledgement, or immediately if you are confident the withdrawal
stands.)
