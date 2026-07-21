"""Author: Carles Marín.

Program: deterministic 3D figure generator for the transversal-matroid paper.

Purpose: draw every figure of the paper directly from the data that
         check_canonical_obstruction.sage verifies, so that no figure can drift
         away from the mathematics it illustrates.
Input:   the running presentation A0..A4 over {a,b,c,d,x,y}; nothing else.
Output:  fig_presentation_3d.png, fig_lattice_3d.png, fig_decision_3d.png,
         fig_circuit_3d.png.
Verification status: illustrative rendering. Every quantity plotted is recomputed
         here from the presentation by exhaustive enumeration and asserted against
         the theorem before it is drawn; the formal proofs are in
         lean/Theorems/TransversalObstruction.lean.

Run: python generate_obstruction_figures.py
"""

from itertools import combinations, permutations

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

# --- the running example -------------------------------------------------
# N(a)={0,1}  N(b)={1}  N(c)={1,2}  N(d)={3,4}  N(x)={2}  N(y)={4}
FAMILY = [frozenset("a"), frozenset("abc"), frozenset("cx"),
          frozenset("d"), frozenset("dy")]
UNIVERSE = sorted(set().union(*FAMILY))
INDEP = frozenset("abcd")           # the partial transversal used in the paper

TEAL = "#1B6F8C"
BAND = "#DCE7EB"
AMBER = "#E08A1E"
PLUM = "#7B4B94"
GREY = "#B9C2CC"


# --- the mathematics, recomputed here ------------------------------------
def subsets(elements):
    elements = sorted(elements)
    return [frozenset(c) for k in range(len(elements) + 1)
            for c in combinations(elements, k)]


def slots(element):
    return frozenset(i for i, block in enumerate(FAMILY) if element in block)


def neighbourhood(subset):
    return frozenset().union(*[slots(x) for x in subset]) if subset else frozenset()


def is_partial_transversal(chosen):
    chosen = tuple(sorted(chosen))
    if len(chosen) > len(FAMILY):
        return False
    return any(all(e in FAMILY[i] for e, i in zip(chosen, idx))
               for idx in permutations(range(len(FAMILY)), len(chosen)))


def is_tight(subset):
    return len(neighbourhood(subset)) == len(subset)


def tight_subsets(independent):
    return [S for S in subsets(independent) if is_tight(S)]


def max_tight(independent):
    tights = tight_subsets(independent)
    return frozenset().union(*tights) if tights else frozenset()


# --- guards: the picture may not disagree with the theorem ---------------
INDEPENDENTS = [S for S in subsets(UNIVERSE) if is_partial_transversal(S)]
DECISIONS = 0
for _I in INDEPENDENTS:
    _top = max_tight(_I)
    assert is_tight(_top)
    assert all(S <= _top for S in tight_subsets(_I))
    for _e in UNIVERSE:
        if _e in _I:
            continue
        assert is_partial_transversal(_I | {_e}) != (slots(_e) <= neighbourhood(_top))
        DECISIONS += 1
assert is_partial_transversal(INDEP)
MAXTIGHT = max_tight(INDEP)
assert MAXTIGHT == frozenset("abc") and MAXTIGHT < INDEP


def autocrop(path, pad=14):
    """Trim the uniform white margin matplotlib's 3D axes reserve around the drawing.

    The 3D projection always reserves a full cube, so a figure whose content is a wide
    band is saved as a near-square image with large empty borders.  Cropping to the
    non-white bounding box makes the figure the shape of its content, which is what lets
    it sit inline in the paper instead of taking a page to itself.
    """
    try:
        from PIL import Image, ImageChops
    except ImportError:                       # cropping is cosmetic; never fail on it
        return path
    im = Image.open(path).convert("RGB")
    bg = Image.new("RGB", im.size, (255, 255, 255))
    box = ImageChops.difference(im, bg).getbbox()
    if box:
        left, upper, right, lower = box
        im.crop((max(0, left - pad), max(0, upper - pad),
                 min(im.size[0], right + pad), min(im.size[1], lower + pad))).save(path)
    return path


def style(ax, elev=22, azim=-58):
    ax.view_init(elev=elev, azim=azim)
    ax.set_axis_off()
    try:
        ax.set_box_aspect((1.0, 0.55, 0.42))
    except Exception:
        pass


# --- Figure 1: the presentation as a 3D incidence structure --------------
def figure_presentation(path="fig_presentation_3d.png"):
    fig = plt.figure(figsize=(7.6, 3.3))
    ax = fig.add_subplot(111, projection="3d")

    slot_xy = {i: (1.35 * i, 0.9) for i in range(len(FAMILY))}
    elem_x = {"a": 0.0, "b": 1.0, "c": 2.0, "d": 3.35, "x": 4.75, "y": 5.9}
    elem_col = {"a": TEAL, "b": TEAL, "c": TEAL, "d": GREY, "x": PLUM, "y": AMBER}

    saturated = sorted(neighbourhood(MAXTIGHT))
    # translucent slab over the saturated slots: the wall that says no
    xs = [slot_xy[i][0] for i in saturated]
    slab = [[(min(xs) - 0.42, 0.52, 1.02), (max(xs) + 0.42, 0.52, 1.02),
             (max(xs) + 0.42, 1.28, 1.02), (min(xs) - 0.42, 1.28, 1.02)]]
    ax.add_collection3d(Poly3DCollection(slab, facecolor=TEAL, alpha=0.13,
                                         edgecolor=TEAL, linewidths=0.9))

    for i, block in enumerate(FAMILY):
        sx, sy = slot_xy[i]
        hot = i in saturated
        ax.scatter([sx], [sy], [1.0], s=190, marker="s",
                   color=BAND if hot else "white",
                   edgecolors=TEAL if hot else "black", linewidths=1.4, depthshade=False)
        ax.text(sx, sy + 0.22, 1.13, f"$A_{i}$", ha="center", fontsize=9,
                color=TEAL if hot else "black")

    for e in UNIVERSE:
        ex = elem_x[e]
        ax.scatter([ex], [0.0], [0.0], s=150, color="white",
                   edgecolors=elem_col[e], linewidths=1.8, depthshade=False)
        ax.text(ex, -0.24, -0.16, f"${e}$", ha="center", fontsize=10, color=elem_col[e])
        for i in sorted(slots(e)):
            sx, sy = slot_xy[i]
            inside = e in MAXTIGHT
            ax.plot([ex, sx], [0.0, sy], [0.0, 1.0],
                    color=elem_col[e] if e != "d" else GREY,
                    lw=1.9 if inside else 1.2,
                    ls="--" if e == "x" else "-",
                    alpha=0.95 if (inside or e in "xy") else 0.55)

    # the legend names the tight block and the caption reads the picture; a third
    # copy of the same sentence only collides with the element row.

    ax.legend(handles=[
        Line2D([], [], color=TEAL, lw=2, label="tight block $R=\\{a,b,c\\}$ and its three slots"),
        Line2D([], [], color=GREY, lw=2, label="$d$: slack, outside the obstruction"),
        Line2D([], [], color=PLUM, lw=2, ls="--",
               label="$x$ refused: $\\mathrm{N}(x)$ lies inside $\\mathrm{N}(R)$"),
        Line2D([], [], color=AMBER, lw=2,
               label="$y$ admitted: $\\mathrm{N}(y)$ escapes $\\mathrm{N}(R)$")],
        loc="upper center", fontsize=8.5, frameon=False, ncol=2,
        bbox_to_anchor=(0.52, 1.10), columnspacing=1.4, handlelength=1.6)

    style(ax, elev=24, azim=-66)
    ax.set_box_aspect((1.0, 0.42, 0.44))
    ax.set_xlim(-0.6, 6.4); ax.set_ylim(-0.15, 1.45); ax.set_zlim(-0.55, 1.28)
    fig.tight_layout(pad=0.2)
    fig.savefig(path, dpi=200, bbox_inches="tight")
    plt.close(fig)
    return autocrop(path)


# --- Figure 2: the Boolean lattice, with the tight sublattice ------------
def figure_lattice(path="fig_lattice_3d.png"):
    fig = plt.figure(figsize=(6.9, 3.9))
    ax = fig.add_subplot(111, projection="3d")

    elems = sorted(INDEP)
    levels = {}
    for S in subsets(INDEP):
        levels.setdefault(len(S), []).append(S)
    pos = {}
    for k, nodes in levels.items():
        nodes.sort(key=lambda S: "".join(sorted(S)))
        n = len(nodes)
        for j, S in enumerate(nodes):
            angle = (j - (n - 1) / 2.0)
            pos[S] = (angle * 1.05, 0.28 * ((j % 2) * 2 - 1) if n > 2 else 0.0, k)

    tights = set(tight_subsets(INDEP))

    for S in subsets(INDEP):
        for e in elems:
            if e in S:
                continue
            T = S | {e}
            both = S in tights and T in tights
            x0, y0, z0 = pos[S]; x1, y1, z1 = pos[T]
            ax.plot([x0, x1], [y0, y1], [z0, z1],
                    color=TEAL if both else GREY,
                    lw=2.2 if both else 0.7, alpha=1.0 if both else 0.35, zorder=1)

    for S in subsets(INDEP):
        x, y, z = pos[S]
        top = S == MAXTIGHT
        tight = S in tights
        ax.scatter([x], [y], [z], s=230 if top else (140 if tight else 55),
                   color=AMBER if top else (BAND if tight else "white"),
                   edgecolors=AMBER if top else (TEAL if tight else GREY),
                   linewidths=1.9 if top else (1.5 if tight else 0.8),
                   depthshade=False, zorder=3)
        if tight or len(S) == 4:
            ax.text(x, y + 0.34, z + (0.20 if top else 0.24),
                    r"$\emptyset$" if not S else "$\\{" + ",".join(sorted(S)) + "\\}$",
                    ha="center", fontsize=9.5,
                    color=AMBER if top else (TEAL if tight else "0.45"))

    for k in range(5):
        ax.text(-4.75, 0.0, k - 0.06, f"$|S|={k}$", fontsize=8.5, color="0.5")

    ax.legend(handles=[
        Line2D([], [], color=TEAL, lw=2.2, label="covering relation inside the tight sublattice"),
        Line2D([], [], marker="o", ls="", markerfacecolor=BAND, markeredgecolor=TEAL,
               markersize=8, label="tight subset of $I$"),
        Line2D([], [], marker="o", ls="", markerfacecolor=AMBER, markeredgecolor=AMBER,
               markersize=9, label="$\\mathrm{maxTight}(I)$"),
        Line2D([], [], marker="o", ls="", markerfacecolor="white", markeredgecolor=GREY,
               markersize=6, label="not tight")],
        loc="upper left", fontsize=7.6, frameon=False, ncol=2,
        bbox_to_anchor=(-0.04, 1.02), columnspacing=1.2, handlelength=1.5)

    style(ax, elev=13, azim=-72)
    ax.set_box_aspect((1.0, 0.26, 0.82))
    ax.set_zlim(-0.35, 4.9)
    ax.set_xlim(-4.95, 3.30)
    fig.tight_layout(pad=0.2)
    fig.savefig(path, dpi=200, bbox_inches="tight")
    plt.close(fig)
    return autocrop(path)


# --- Figure 3: the decision landscape over all partial transversals ------
def figure_decision(path="fig_decision_3d.png"):
    fig = plt.figure(figsize=(6.8, 3.6))
    ax = fig.add_subplot(111, projection="3d")

    pts = {}
    for I in INDEPENDENTS:
        top = max_tight(I)
        refused = [e for e in UNIVERSE
                   if e not in I and slots(e) <= neighbourhood(top)]
        key = (len(I), len(top), len(refused))
        pts[key] = pts.get(key, 0) + 1

    for (size, tsize, refused), count in sorted(pts.items()):
        ax.scatter([size], [tsize], [refused],
                   s=40 + 46 * count,
                   color=AMBER if refused else BAND,
                   edgecolors=AMBER if refused else TEAL,
                   linewidths=1.4, alpha=0.92, depthshade=False)
        if count > 1:
            ax.text(size, tsize, refused + 0.16, f"{count}", ha="center",
                    fontsize=7.5, color="0.35")

    for size in range(0, 5):
        ax.plot([size, size], [0, 4], [0, 0], color=GREY, lw=0.5, alpha=0.5)

    zmax = max(k[2] for k in pts)
    ax.set_xlabel("$|I|$", fontsize=9.5, labelpad=-2)
    ax.set_ylabel(r"$|\mathrm{maxTight}(I)|$", fontsize=9.5, labelpad=2)
    ax.set_zlabel("refused", fontsize=9.5, labelpad=-6, rotation=0)
    ax.tick_params(labelsize=8, pad=-1)
    ax.set_xticks(range(0, 5)); ax.set_yticks(range(0, 5))
    ax.set_zticks(range(0, zmax + 1))
    ax.set_zlim(-0.12, zmax + 0.35)
    ax.view_init(elev=24, azim=-60)
    ax.set_box_aspect((1.0, 0.82, 0.30))
    ax.text2D(0.0, 0.99,
              f"all {len(INDEPENDENTS)} partial transversals of the presentation; "
              f"{DECISIONS} insertion decisions,\nevery one of them predicted by "
              r"$\mathrm{N}(e)\subseteq\mathrm{N}(\mathrm{maxTight}(I))$",
              transform=ax.transAxes, fontsize=9, color=TEAL, va="top")
    fig.tight_layout(pad=0.2)
    fig.savefig(path, dpi=200, bbox_inches="tight")
    plt.close(fig)
    return autocrop(path)



# --- Figure 4: the geometry of the matroid, and its single circuit ------
def _rank(X):
    for k in range(len(X), -1, -1):
        for c in combinations(sorted(X), k):
            if is_partial_transversal(frozenset(c)):
                return k
    return 0


def _closure(X):
    r = _rank(X)
    return frozenset(e for e in UNIVERSE if _rank(frozenset(X) | {e}) == r)


def figure_circuit(path="fig_circuit_3d.png"):
    """The matroid drawn as a point configuration: its one dependency is a line."""
    circuits = []
    for k in range(1, len(UNIVERSE) + 1):
        for c in combinations(UNIVERSE, k):
            C = frozenset(c)
            if not is_partial_transversal(C) and all(
                    is_partial_transversal(C - {e}) for e in C):
                circuits.append(C)
    assert circuits == [frozenset("bcx")], circuits
    lines = {_closure(frozenset(pq)) for pq in combinations(UNIVERSE, 2)}
    big = [L for L in lines if len(L) > 2]
    assert big == [frozenset("bcx")], big

    # a drawing must honour the dependency: b, c, x are placed collinear.
    P = {"b": (-1.30, 0.00, 0.00), "c": (0.00, 0.00, 0.00), "x": (1.30, 0.00, 0.00),
         "a": (-0.55, 1.25, 1.00), "d": (-2.25, -0.55, -0.95), "y": (0.95, -1.45, 0.95)}
    col = {"b": AMBER, "c": AMBER, "x": AMBER, "a": TEAL, "d": TEAL, "y": TEAL}

    fig = plt.figure(figsize=(6.4, 2.9))
    ax = fig.add_subplot(111, projection="3d")

    for L in sorted(lines, key=len):
        pts = sorted(L)
        if len(pts) == 2:
            (x0, y0, z0), (x1, y1, z1) = P[pts[0]], P[pts[1]]
            ax.plot([x0, x1], [y0, y1], [z0, z1], color=GREY, lw=0.8, alpha=0.45)
    ax.plot([P["b"][0], P["x"][0]], [P["b"][1], P["x"][1]], [P["b"][2], P["x"][2]],
            color=AMBER, lw=3.4, solid_capstyle="round", zorder=2)

    for e, (px, py, pz) in P.items():
        ax.scatter([px], [py], [pz], s=170, color="white", edgecolors=col[e],
                   linewidths=2.1, depthshade=False, zorder=3)
        ax.text(px, py, pz + 0.20, f"${e}$", ha="center", fontsize=11, color=col[e])

    # the reading of the picture lives in the LaTeX caption, not on the canvas
    ax.text(0.0, -0.05, -0.62, r"$\{b,c,x\}$", ha="center", fontsize=10, color=AMBER)
    ax.view_init(elev=15, azim=-62)
    ax.set_axis_off()
    ax.set_box_aspect((1.0, 0.62, 0.52))
    ax.set_zlim(-1.35, 1.25)
    fig.tight_layout(pad=0.2)
    fig.savefig(path, dpi=200, bbox_inches="tight")
    plt.close(fig)
    return autocrop(path)


if __name__ == "__main__":
    import os
    os.chdir(os.path.dirname(os.path.abspath(__file__)) or ".")
    for f in (figure_presentation(), figure_lattice(), figure_decision(),
              figure_circuit()):
        print("wrote", f)
    print(f"data: {len(INDEPENDENTS)} partial transversals, {DECISIONS} decisions, "
          f"maxTight(I) = {sorted(MAXTIGHT)}")
