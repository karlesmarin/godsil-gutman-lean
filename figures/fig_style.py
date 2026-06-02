"""Shared professional style for all paper figures."""
import matplotlib as mpl
import matplotlib.pyplot as plt
# coherent muted-vivid palette
COL = dict(
    pos   = "#1b6f8c",   # positive edge  (deep teal)
    neg   = "#c1452e",   # negative edge  (warm red)
    node  = "#23303a",   # node fill
    accent= "#e08a1e",   # accent / result (amber)
    grey  = "#6b7785",
    lyr0  = "#1b6f8c",
    lyr1  = "#7aa7b5",
    band  = "#dce7eb",
)
def setup():
    mpl.rcParams.update({
        "figure.dpi": 130, "savefig.dpi": 300, "savefig.bbox": "tight",
        "font.family": "serif", "font.size": 11,
        "mathtext.fontset": "cm", "axes.linewidth": 0.8,
        "axes.edgecolor": "#33414c", "text.color": "#1a232b",
        "axes.labelcolor": "#1a232b", "xtick.color": "#33414c", "ytick.color": "#33414c",
    })
def save(fig, name):
    for ext in ("pdf","png"):
        fig.savefig(f"{name}.{ext}", facecolor="white")
    print("wrote", name+".pdf /.png")
