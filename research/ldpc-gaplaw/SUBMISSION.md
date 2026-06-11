# Submission package — applied LDPC census paper

Source: `ldpc-census.tex` (EN), `ldpc-census-es.tex` (ES). Both self-contained single files
(inline TikZ figure, no external graphics). Compile: `pdflatex` ×2. 0 overfull boxes.

## Venue plan (no arXiv endorser available)

1. **TechRxiv** (preprints.techrxiv.org) — IEEE preprint, NO endorsement, audience =
   comms/coding engineers. PRIMARY preprint home.
2. **Zenodo** — DOI + archives the `.alist` data and `census_pilot2.py`; cross-link to the
   theory paper's Zenodo record (relation: `references` / `isDerivedFrom` -> Part VI DOI).
3. **IEEE Communications Letters** — optional peer-reviewed venue (short format fits; submit
   the EN version). Manage expectations: the paper claims no algorithmic novelty; the hook is
   the certification layer.
4. **arXiv cs.IT** — LATER, only if an endorser is found. Self-contained .tex uploads as-is.

The series theory paper (Part VI, gap-window) stays on Zenodo like Parts I-V.

## Metadata (use for TechRxiv / arXiv / Zenodo forms)

**Title:** Certified Short-Cycle Counts for the IEEE 802.11n (WiFi) LDPC Codes

**Subtitle:** A machine-checked census of the deployed parity-check graphs via the
trace-formula gap law

**Authors:** Carles Marin (independent researcher), karlesmarin@gmail.com
ORCID: 0009-0007-5637-9688

**Abstract (plain text):**
Short cycles in the Tanner graph of a low-density parity-check (LDPC) code degrade
belief-propagation decoding, and counting them is a standard task in code design. This paper
does not count them faster. It counts them with a certificate: for each of the four LDPC
codes of the IEEE 802.11n (WiFi) standard at block length n = 648, the number of shortest
cycles is obtained from a machine-checked identity -- the trace-formula gap law, proved
sorry-free in Lean 4 in the companion paper -- and cross-checked by three mutually
independent computations that agree exactly: the non-backtracking trace tr(B^g)/2g, the gap
law (tr(A^g) - p_g)/2g, and direct enumeration. The census reads c_6 = 3942 (rate 1/2),
c_6 = 8046 (rate 2/3), c_4 = 54 (rate 3/4, where the girth collapses to 4) and c_6 = 32346
(rate 5/6), and it tells a design story: the rate-3/4 code pays for its density with
four-cycles, the most damaging kind, while the rate-5/6 code buys its girth back at the price
of thirty-two thousand hexagons. The counting algorithms of the coding-theory literature are
faster and reach further; the contribution here is the certification layer -- an exact
identity backed by a theorem with a checkable proof -- which, to the best of my knowledge, no
prior cycle-counting tool carries.

**arXiv categories:** primary cs.IT (Information Theory); secondary math.CO (Combinatorics),
cs.LO (Logic in Computer Science).

**TechRxiv taxonomy:** Communication, Networking & Broadcast Technologies > Coding,
information theory; cross-tag Formal methods / verification.

**Keywords:** LDPC codes; Tanner graph; girth; short-cycle enumeration; belief propagation;
non-backtracking operator; Ihara zeta; matching polynomial; formal verification; Lean 4;
IEEE 802.11n.

**MSC 2020:** 94B05 (linear codes), 05C38 (paths and cycles), 68V20 (formalization of
mathematics). **ACM:** E.4 (Coding and Information Theory), F.4.1.

**Comments line:** 5 pages, 1 figure, 1 table. Applied companion to "The Walks That Remember
the Cycles" (Part VI). Lean sources and census pipeline:
https://github.com/karlesmarin/godsil-gutman-lean

**License:** CC-BY 4.0 (matches the rest of the series).

## Pre-submission checklist

- [x] Companion (Part VI) Zenodo DOI = 10.5281/zenodo.20648489 (reserved on the draft;
      becomes final when the Part VI draft is published). Filled into the bibitem
      `MarinGapWindow2026` in both ldpc-census.tex and ldpc-census-es.tex.
- [ ] Decide girth term: `cuello` vs `cintura` (ES, series-wide).
- [ ] Final read of both PDFs by author.
- [ ] (TechRxiv) account + ORCID linked.
- [ ] (Zenodo) upload PDF + tar of research/ldpc-gaplaw + link to Part VI record.
