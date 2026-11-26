"""Figures of finite pieces of Gamma_alpha (illustration only, not part of the proof).

Vertices: points reachable from 0 in at most D unit steps +-alpha^n (n < K).
Edges: pairs differing by some alpha^n (n < K), i.e. unit-distance pairs of the graph.
All pieces drawn here use only n <= 78, so they lie in G_78, which is 3-colourable.

Usage:  python3 code/draw_figures.py          (needs numpy, matplotlib; writes figures/)
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.image as mpimg
from matplotlib.collections import LineCollection

F = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]   # f(x), x^12 ... x^0
ROOTS = np.roots(F)
UPPER = sorted([r for r in ROOTS if r.imag > 1e-9], key=np.angle)
ALPHA = UPPER[1]                                     # the root at ~51.2 degrees
OUT = os.path.join(os.path.dirname(__file__), "..", "figures")
CMAP = plt.get_cmap("magma")


def piece(K, D, a=ALPHA):
    steps = [a**n for n in range(K)]
    steps += [-s for s in steps]
    key = lambda z: (round(z.real, 9), round(z.imag, 9))
    pts, lvl, frontier = {key(0j): 0j}, {key(0j): 0}, [0j]
    for d in range(1, D + 1):
        new = []
        for z in frontier:
            for s in steps:
                k = key(z + s)
                if k not in pts:
                    pts[k], lvl[k] = z + s, d
                    new.append(z + s)
        frontier = new
    idx = {k: i for i, k in enumerate(pts)}
    P = np.array(list(pts.values()))
    L = np.array([lvl[k] for k in pts])
    E = np.array([(i, j) for i, z in enumerate(P) for s in steps[:K]
                  if (j := idx.get(key(z + s))) is not None])
    return P, L, E


def draw_piece(K, D, path, size=12, lw=0.5, alpha=0.75, dot=3):
    P, L, E = piece(K, D)
    fig = plt.figure(figsize=(size, size), dpi=200, facecolor="black")
    ax = fig.add_axes([0, 0, 1, 1]); ax.set_facecolor("black"); ax.axis("off"); ax.set_aspect("equal")
    seg = np.stack([np.c_[P[E[:, 0]].real, P[E[:, 0]].imag], np.c_[P[E[:, 1]].real, P[E[:, 1]].imag]], 1)
    d = np.maximum(L[E[:, 0]], L[E[:, 1]])
    col = CMAP(0.92 - 0.55 * d / L.max()); col[:, 3] = alpha * (1.3 - 0.7 * d / L.max())
    ax.add_collection(LineCollection(seg, colors=col, linewidths=lw))
    ax.scatter(P.real, P.imag, s=dot, c=CMAP(0.95 - 0.6 * L / L.max()), linewidths=0, alpha=0.9)
    r = np.abs(P).max() * 1.03; ax.set_xlim(-r, r); ax.set_ylim(-r, r)
    fig.savefig(path, facecolor="black", pil_kwargs={"quality": 90}); plt.close(fig)
    print(f"{os.path.basename(path)}: K={K} D={D}, {len(P)} vertices, {len(E)} edges")


def draw_roots(path):
    fig = plt.figure(figsize=(8, 8), dpi=200, facecolor="black")
    ax = fig.add_axes([0, 0, 1, 1]); ax.set_facecolor("black"); ax.axis("off"); ax.set_aspect("equal")
    t = np.linspace(0, 2 * np.pi, 600); ax.plot(np.cos(t), np.sin(t), color="#5a3a6a", lw=1)
    for n in range(24):
        z = ALPHA**n; ax.plot([0, z.real], [0, z.imag], color=CMAP(0.9 - 0.5 * n / 24), lw=1.2, alpha=0.85)
    ax.scatter(ROOTS.real, ROOTS.imag, s=120, color="#fbd38d", zorder=3, edgecolors="black", linewidths=1.2)
    ax.scatter([ALPHA.real], [ALPHA.imag], s=320, facecolors="none", edgecolors="#fff", linewidths=1.6, zorder=4)
    ax.text(ALPHA.real * 1.13, ALPHA.imag * 1.13, "α", color="white", fontsize=22, ha="center", va="center")
    ax.set_xlim(-1.3, 1.3); ax.set_ylim(-1.3, 1.3)
    fig.savefig(path, facecolor="black"); plt.close(fig)


def banner(panels, path):
    fig = plt.figure(figsize=(18.4, 7.4), dpi=130, facecolor="black")
    for i, p in enumerate(panels):
        ax = fig.add_axes([i / 3 + 0.005, 0.17, 1 / 3 - 0.01, 0.81]); ax.imshow(mpimg.imread(p)); ax.axis("off")
    kw = dict(ha="center", va="center", color="#d8c8e0", fontsize=15)
    for i, t in enumerate(["The 12 roots of $f$ on the unit circle;\nrays: steps $\\alpha^n$, $n<24$",
                           "Steps $\\pm\\alpha^n$ ($n<24$),\nat most 2 steps from 0",
                           "Steps $\\pm\\alpha^n$ ($n<12$),\nat most 3 steps from 0"]):
        fig.text(i / 3 + 1 / 6, 0.115, t, **kw)
    fig.text(0.5, 0.035, "Finite pieces of $\\Gamma_\\alpha$. They use only steps $\\alpha^n$ with $n\\leq 78$, so they lie in "
             "$G_{78}$, which is 3-colourable (Sharpness). A 4-chromatic finite piece must use a step with $n\\geq 79$; "
             "none is known explicitly.", ha="center", va="center", color="#8c7a96", fontsize=11.5)
    fig.savefig(path, facecolor="black"); plt.close(fig)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    print("all |roots| = 1:", np.allclose(np.abs(ROOTS), 1), " alpha =", ALPHA)
    j = lambda n: os.path.join(OUT, n)
    draw_roots(j("roots.png"))
    draw_piece(24, 2, j("piece_K24_D2.jpg"))
    draw_piece(12, 3, j("piece_K12_D3.jpg"))
    draw_piece(40, 2, j("piece_K40_D2.jpg"))
    banner([j("roots.png"), j("piece_K24_D2.jpg"), j("piece_K12_D3.jpg")], j("banner.png"))
