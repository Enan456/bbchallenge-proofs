"""Figures: standard TM representations vs the non-Euclidean charts,
all from real dossier-2 data."""
import sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-enan-Documents-bbchallenge-proofs/cf6f9179-4bab-4e6b-9f6c-ff143cc5776c/scratchpad')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from metastep_check import meta_step

OUT = '/Users/enan/Documents/bbchallenge-proofs/docs/learning/figures'
CODE = '1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD'

def parse(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3*b:3*b+3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else (int(tr[0]), tr[1], tr[2])
    return tbl

# ---- fig 1: standard space-time diagram + fig 2 growth curves
tbl = parse(CODE)
tape = {}
st, h = 'A', 0
rows = []
ext_l, ext_r, exts = 0, 0, []
N1, W = 1600, 90
for t in range(200000):
    if t < N1:
        row = np.zeros(W)
        for q in range(-W//2, W//2):
            row[q + W//2] = tape.get(q, 0)
        row[max(0, min(W-1, h + W//2))] = 2
        rows.append(row)
    b = tape.get(h, 0)
    wr, mv, nst = tbl[(st, b)]
    tape[h] = wr
    h += 1 if mv == 'R' else -1
    st = nst
    ext_l, ext_r = min(ext_l, h), max(ext_r, h)
    exts.append((ext_l, ext_r))

fig, ax = plt.subplots(figsize=(5.2, 7))
ax.imshow(np.array(rows), aspect='auto', cmap='Greys', interpolation='nearest')
ax.set_xlabel('tape position'); ax.set_ylabel('step')
ax.set_title('Standard representation:\nspace–time diagram (dossier-2, first 1600 steps)')
plt.tight_layout(); plt.savefig(f'{OUT}/fig1_spacetime.png', dpi=150); plt.close()

fig, ax = plt.subplots(figsize=(6, 3.4))
e = np.array(exts)
ax.plot(e[:, 1], lw=1, label='right extent')
ax.plot(e[:, 0], lw=1, label='left extent')
ax.set_xlabel('step'); ax.set_ylabel('tape position')
ax.set_title('Standard representation: tape extent growth (linear axes)')
ax.legend(frameon=False)
plt.tight_layout(); plt.savefig(f'{OUT}/fig2_growth.png', dpi=150); plt.close()

# ---- abstract orbit (a, b, c) via metaStep, with renewal γ log
ms = (False, -8, -2, 12, 13)
A_, B_, C_, gammas, kinds = [], [], [], [], []
prev = None
for i in range(120000):
    three, l, h1, h2, r = ms
    a, b, c = h1 - l, h2 - h1, r - h2
    if not three:
        A_.append(a); B_.append(b); C_.append(c)
    nxt = meta_step(*ms)
    if nxt is None:
        break
    # renewal detection: deep (l changes) or fuse (r jumps 2 from 3-hole)
    if nxt[1] != l or (three and nxt[4] == r + 2):
        l2, h12, h22, r2 = nxt[1], nxt[2], nxt[3], nxt[4]
        gammas.append((r2 - h22) - (h22 - h12))
    ms = nxt
A_, B_, C_ = map(np.array, (A_, B_, C_))

fig, axes = plt.subplots(1, 3, figsize=(11, 3.6))
ax = axes[0]
ax.plot(np.log1p(A_), lw=0.5, label=r'$\log(1+a)$')
ax.plot(np.log1p(B_), lw=0.5, label=r'$\log(1+b)$')
ax.plot(np.log1p(C_), lw=0.5, label=r'$\log(1+c)$')
ax.set_title('log chart: orbit coordinates'); ax.set_xlabel('spawn-entry index')
ax.legend(frameon=False, fontsize=8)
ax = axes[1]
S = A_ + B_ + C_
x = (B_ + 2 * C_) / (2 * S); y = (np.sqrt(3) / 2) * B_ / S
ax.scatter(x, y, s=0.5, alpha=0.3, c=np.arange(len(x)), cmap='viridis')
ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=0.7)
ax.text(-0.02, -0.05, 'a'); ax.text(1.0, -0.05, 'c'); ax.text(0.49, 0.89, 'b')
ax.set_title('simplex chart: projective shape'); ax.axis('off')
ax = axes[2]
ax.scatter(B_ / S, S, s=0.5, alpha=0.3, c=np.arange(len(x)), cmap='viridis')
ax.set_yscale('log')
ax.set_title(r'$\mathbb{H}^2$-style chart: shape vs scale')
ax.set_xlabel('b / (a+b+c)'); ax.set_ylabel('a+b+c  (height, log)')
plt.suptitle('Our representation: the same orbit in three non-Euclidean charts (dossier-2, 120k episodes)', y=1.02)
plt.tight_layout(); plt.savefig(f'{OUT}/fig3_charts.png', dpi=150, bbox_inches='tight'); plt.close()

g = np.array(gammas)
fig, ax = plt.subplots(figsize=(6.6, 3.4))
idx = np.arange(len(g))
ax.scatter(idx[g > 0], g[g > 0], s=14, marker='^', label=r'$\gamma>0$ (fuse path)')
ax.scatter(idx[g < 0], -g[g < 0], s=14, marker='v', label=r'$-\gamma$ ($\gamma<0$, deep path)')
ax.axhspan(1, 5, color='red', alpha=0.15, label='lethal bands $\\gamma\\in\\{1,3,5\\}$')
ax.set_yscale('log')
ax.set_xlabel('renewal index'); ax.set_ylabel(r'$|\gamma| = |c-b|$ (log)')
ax.set_title('The compressed conjecture: renewal invariant $\\gamma$ dodging the lethal bands')
ax.legend(frameon=False, fontsize=8)
plt.tight_layout(); plt.savefig(f'{OUT}/fig4_gamma.png', dpi=150); plt.close()
print('figures written:', len(rows), 'st rows;', len(A_), 'episodes;', len(g), 'renewals')
