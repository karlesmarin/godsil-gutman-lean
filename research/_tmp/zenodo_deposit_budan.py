#!/usr/bin/env python3
# Create a Zenodo DRAFT deposition for the Budan-Fourier paper (does NOT publish).
# Reads ZENODO_TOKEN from E:/proyectos/SMEFT/.env (token never printed). Uploads the two PDFs
# (EN + ES) and sets metadata WITH cross-references to the series. Leaves the draft for the
# author to review and click Publish.
#
# Cross-references (related_identifiers):
#   - continues   Sturm   (10.5281/zenodo.20707348)  -- BF is the successor in the real-root strand
#   - references  Newton  (10.5281/zenodo.20693064)  -- cited
#   - references  Godsil-Gutman (10.5281/zenodo.20517350) -- series root, cited
#   - isSupplementedBy  the GitHub repository
# AFTER publishing: take the minted DOI and add it to \bibitem{bflean}/{budanlean} in
# virtual-roots-lean(.tex/-es) and sign-variation-lean(.tex/-es), then recompile + publish those.

import json, os, urllib.request, urllib.error

ENV = r"E:/proyectos/SMEFT/.env"
BASE = "https://zenodo.org/api"
REPO = "E:/proyectos/godsil-gutman-lean"
PDFS = ["budan-fourier-lean.pdf", "budan-fourier-lean-es.pdf"]


def token():
    for line in open(ENV, encoding="utf-8"):
        if line.startswith("ZENODO_TOKEN="):
            return line.split("=", 1)[1].strip().strip('"').strip("'")
    raise SystemExit("ZENODO_TOKEN not found")


TOK = token()
H = {"Authorization": f"Bearer {TOK}", "Content-Type": "application/json"}


def req(method, url, data=None, headers=None, raw=False):
    body = data if raw else (json.dumps(data).encode() if data is not None else None)
    r = urllib.request.Request(url, data=body, method=method,
                               headers=headers if headers is not None else H)
    try:
        with urllib.request.urlopen(r) as resp:
            return resp.status, json.loads(resp.read().decode() or "{}")
    except urllib.error.HTTPError as e:
        msg = e.read().decode()
        print(f"HTTP {e.code} on {method} {url.split('?')[0]}\n{msg[:800]}")
        raise SystemExit(1)


METADATA = {"metadata": {
    "upload_type": "publication",
    "publication_type": "preprint",
    "title": ("Counting with the Derivative Tower: the Budan-Fourier Theorem, "
              "Machine-Checked in Lean 4"),
    "creators": [{"name": "Marin Munoz, Carles", "orcid": "0009-0007-5637-9688",
                  "affiliation": "Independent researcher"}],
    "description": (
        "<p>A machine-checked, <code>sorry</code>-free proof, in Lean 4 over Mathlib, of the "
        "Budan-Fourier theorem: for a nonzero real polynomial p and a &lt; b with "
        "p(a), p(b) &ne; 0, the number of real roots of p in (a, b] counted with multiplicity is "
        "at most the drop V(a) &minus; V(b) in the sign variations of the derivative tower "
        "p, p&prime;, p&Prime;, &hellip;, and the difference V(a) &minus; V(b) &minus; #roots is "
        "<em>even</em>. The even surplus is the fingerprint of the complex roots the interval "
        "cannot see; the b &rarr; &infin; shadow is Descartes' rule of signs, which the same "
        "engine reaches through the identity fourierVar(p, 0) = Polynomial.signVariations p, "
        "Mathlib's own coefficient sign count.</p>"
        "<p>The contribution is the formalization: to the best of the author's knowledge the "
        "first Budan-Fourier theorem in Lean (not first in any system &mdash; a prior "
        "Isabelle/HOL formalization is by W. Li). It runs on the same sign-variation engine as "
        "the companion Sturm formalization, but its local analysis must resolve a whole "
        "<em>vanishing block</em> of the derivative tower at once &mdash; the tower is not a "
        "coprime (Sturm) chain at a multiple root &mdash; handled by the Rseq/Lseq block law. "
        "The headline theorem depends only on the three standard axioms (propext, "
        "Classical.choice, Quot.sound).</p>"
        "<p>This is the Budan-Fourier paper of the godsil-gutman-lean series (real-root-counting "
        "strand: Newton's inequalities, Sturm, Budan-Fourier). English and Spanish versions are "
        "included. Formalized with AI assistance (Claude, Anthropic); the mathematics and all "
        "claims are the author's responsibility.</p>"),
    "access_right": "open",
    "license": "cc-by-4.0",
    "language": "eng",
    "version": "v1",
    "publication_date": "2026-06-17",
    "keywords": ["Lean 4", "Mathlib", "formal verification", "interactive theorem proving",
                 "machine-checked proof", "Budan-Fourier theorem", "Descartes' rule of signs",
                 "Sturm's theorem", "real root counting", "sign variations", "derivative tower",
                 "polynomial", "real algebraic geometry"],
    "related_identifiers": [
        {"identifier": "10.5281/zenodo.20707348", "relation": "continues"},
        {"identifier": "10.5281/zenodo.20693064", "relation": "references"},
        {"identifier": "10.5281/zenodo.20517350", "relation": "references"},
        {"identifier": "https://github.com/karlesmarin/godsil-gutman-lean",
         "relation": "isSupplementedBy"},
    ],
    "notes": ("All load-bearing theorems machine-checked sorry-free in Lean 4 over Mathlib "
              "(godsil toolchain pin v4.30); #print axioms BudanFourier.budan_fourier reports only "
              "propext, Classical.choice, Quot.sound. Build/check: lake env lean BudanFourier.lean "
              "(imports Sturm.lean). Sources and figure scripts in the linked GitHub repository."),
}}

# 1. create draft
st, dep = req("POST", f"{BASE}/deposit/depositions", data={})
dep_id = dep["id"]
bucket = dep["links"]["bucket"]
doi = dep.get("metadata", {}).get("prereserve_doi", {}).get("doi") or f"10.5281/zenodo.{dep_id}"

# 2. upload PDFs to the bucket (PUT raw)
for fn in PDFS:
    path = os.path.join(REPO, fn)
    with open(path, "rb") as f:
        data = f.read()
    hdr = {"Authorization": f"Bearer {TOK}", "Content-Type": "application/octet-stream"}
    req("PUT", f"{bucket}/{fn}", data=data, headers=hdr, raw=True)
    print(f"uploaded {fn} ({len(data)} bytes)")

# 3. set metadata (NO publish)
req("PUT", f"{BASE}/deposit/depositions/{dep_id}", data=METADATA)

print("\n=== DRAFT created (NOT published) ===")
print(f"deposition id : {dep_id}")
print(f"reserved DOI  : {doi}")
print(f"review/publish: https://zenodo.org/uploads/{dep_id}")
print("Open the link, review, and click Publish to mint the DOI.")
print("THEN: put that DOI into bflean/budanlean in virtual-roots and sign-variation, recompile, publish those.")
