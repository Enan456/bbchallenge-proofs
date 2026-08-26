"""Upgraded non-Euclidean / quantum-inspired charts, real dossier-2 data."""
import sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-enan-Documents-bbchallenge-proofs/cf6f9179-4bab-4e6b-9f6c-ff143cc5776c/scratchpad')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa
import numpy as np
from metastep_check import meta_step

OUT = '/Users/enan/Documents/bbchallenge-proofs/docs/learning/figures'

# collect orbit
ms = (False, -8, -2, 12, 13)
A_, B_, C_, gam_pairs = [], [], [], []
prev_gamma = None
for i in range(200000):
    three, l, h1, h2, r = ms
    a, b, c = h1 - l, h2 - h1, r - h2
    if not three:
        A_.append(a); B_.append(b); C_.append(c)
    nxt = meta_step(*ms)
    if nxt is None:
        break
    if nxt[1] != l or (three and nxt[4] == r + 2):
        g2 = (nxt[4] - nxt[3]) - (nxt[3] - nxt[2])
        if prev_gamma is not None:
            gam_pairs.append((prev_gamma, g2))
        prev_gamma = g2
    ms = nxt
A_, B_, C_ = map(lambda x: np.array(x, dtype=float), (A_, B_, C_))
S = A_ + B_ + C_
t = np.arange(len(A_))

# ---- fig5: Poincaré disk (Cayley transform of half-plane shape/scale)
x = (B_ + 2 * C_) / S - 1.0          # shape coordinate in (-1, 1)
y = np.log(S)                        # log-scale as height
y = (y - y.min()) / (y.max() - y.min()) * 3 + 0.15
z = x + 1j * y
w = (z - 1j) / (z + 1j)              # upper half-plane -> unit disk
fig, ax = plt.subplots(figsize=(5.6, 5.6))
th = np.linspace(0, 2 * np.pi, 400)
ax.plot(np.cos(th), np.sin(th), 'k-', lw=1)
for rr in (0.35, 0.62, 0.82, 0.94):
    ax.plot(rr * np.cos(th), rr * np.sin(th), color='0.85', lw=0.6, zorder=0)
ax.scatter(w.real, w.imag, s=0.6, c=t, cmap='plasma', alpha=0.5)
ax.set_aspect('equal'); ax.axis('off')
ax.set_title('Poincaré disk: the eternal orbit\n(scale = depth toward the boundary; one arc per renewal generation)')
plt.tight_layout(); plt.savefig(f'{OUT}/fig5_poincare.png', dpi=160); plt.close()

# ---- fig6: Fisher–Rao / amplitude octant (sqrt-simplex on the 2-sphere)
p = np.stack([A_ / S, B_ / S, C_ / S])
amp = np.sqrt(p)                     # quantum-inspired: amplitudes
fig = plt.figure(figsize=(6.4, 5.4))
ax = fig.add_subplot(111, projection='3d')
u = np.linspace(0, np.pi / 2, 40)
v = np.linspace(0, np.pi / 2, 40)
uu, vv = np.meshgrid(u, v)
xs = np.sin(vv) * np.cos(uu); ys = np.sin(vv) * np.sin(uu); zs = np.cos(vv)
ax.plot_wireframe(xs, ys, zs, color='0.88', lw=0.4)
ax.scatter(amp[0], amp[1], amp[2], s=0.8, c=t, cmap='viridis', alpha=0.5)
for i, (vx, vy, vz, lab) in enumerate([(1.06, 0, 0, r'$\sqrt{a}$'),
                                       (0, 1.06, 0, r'$\sqrt{b}$'),
                                       (0, 0, 1.06, r'$\sqrt{c}$')]):
    ax.text(vx, vy, vz, lab, fontsize=11)
ax.set_axis_off()
ax.set_title('Amplitude octant (Fisher–Rao sphere): the orbit as a path of\n"pure states" — geodesic distance = statistical distinguishability', pad=0)
ax.view_init(elev=24, azim=38)
plt.tight_layout(); plt.savefig(f'{OUT}/fig6_fisher_rao.png', dpi=160); plt.close()

# ---- fig7: amoeba / tropical tentacles (log-log pairwise)
fig, axes = plt.subplots(1, 2, figsize=(9.6, 4.2))
ax = axes[0]
ax.scatter(np.log(A_ + 1), np.log(B_ + 1), s=0.6, c=t, cmap='plasma', alpha=0.45)
ax.set_xlabel(r'$\log(1+a)$'); ax.set_ylabel(r'$\log(1+b)$')
ax.set_title('Amoeba view, $(a,b)$: tropical tentacles\nare the orbit\'s regimes')
ax = axes[1]
ax.scatter(np.log(B_ + 1), np.log(C_ + 1), s=0.6, c=t, cmap='plasma', alpha=0.45)
ax.set_xlabel(r'$\log(1+b)$'); ax.set_ylabel(r'$\log(1+c)$')
ax.set_title('Amoeba view, $(b,c)$: the conserved-$\\gamma$ spine\nand its renewal branches')
plt.tight_layout(); plt.savefig(f'{OUT}/fig7_amoeba.png', dpi=160); plt.close()

# ---- fig8: renewal return map (the reduced dynamical system itself)
gp = np.array(gam_pairs, dtype=float)
fig, ax = plt.subplots(figsize=(5.8, 5.2))
def slog(v):
    return np.sign(v) * np.log1p(np.abs(v))
ax.scatter(slog(gp[:, 0]), slog(gp[:, 1]), s=22, c=np.arange(len(gp)),
           cmap='cividis')
lim = max(np.abs(slog(gp)).max() * 1.1, 8)
for band in (1, 3, 5):
    ax.axhspan(slog(band) - 0.06, slog(band) + 0.06, color='red', alpha=0.25)
ax.plot([-lim, lim], [-lim, lim], color='0.8', lw=0.7)
ax.set_xlabel(r'symlog $\gamma_k$'); ax.set_ylabel(r'symlog $\gamma_{k+1}$')
ax.set_title('The reduced system\'s return map: $\\gamma_{k+1}$ vs $\\gamma_k$\n(red: the provably fatal values)')
plt.tight_layout(); plt.savefig(f'{OUT}/fig8_returnmap.png', dpi=160); plt.close()
print('figs 5-8 written;', len(A_), 'episodes,', len(gp), 'renewal pairs')
