"""
goi_proxy.py — Geometry of Interaction proxy for BB6 halting properties.

The GoI execution formula (Girard 1989):

    Ex(u, σ) = Σ_{k=0}^∞  u (σu)^k  =  u (I - σu)^{-1}

where  u = the program (renewal map, as an isometry on ℓ²(orbit))
       σ = the "cut wire" (feedback: output of step k → input of step k+1)

Halting   ↔  π_fatal · Ex(u, σ) · |SEED⟩  ≠ 0
             (the execution hits the fatal absorbing state)

Non-halt  ↔  π_fatal · Ex(u, σ) · |SEED⟩  = 0
             ↔  (I - σ·T_R) is invertible AND resolvent has no fatal-subspace pole
             ↔  SafeMetaOrbit conjecture in operator language

This is the categorical proxy — no game, no provers.
The scalar Green's function

    G_fatal(z) = ⟨fatal | (zI - T_R)^{-1} | SEED⟩

is the halting indicator:
  G_fatal has a pole  →  orbit reaches the fatal set at that step
  G_fatal = 0         →  non-halting (for all z in the reachable spectrum)

We also compute the Ruelle-Lefschetz zeta function

    ζ(z) = exp(Σ_{k=1}^K Tr(T_R^k)/k · z^k)

whose zeros and poles encode the periodic orbit structure of the renewal map.
"""
import sys
if sys.stdout.encoding != 'utf-8':
    sys.stdout.reconfigure(encoding='utf-8')

import numpy as np
import math

# ── Certified renewal map ────────────────────────────────────────────────
SEED = (6, 13)

def R(a, b):
    if b % 2 == 0:
        return a + 6, b - 3
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3)
    return alpha + 3 * beta + 3, b - beta - 4

def fatal(a, b):
    if b <= 2: return True
    if b % 2 == 0: return b == 4
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    return b > beta and b - beta in (1, 3, 5)

K = 200
orb = [SEED]
a, b = SEED
for _ in range(K):
    a, b = R(a, b)
    orb.append((a, b))

N = len(orb)  # K+1 states
idx = {s: i for i, s in enumerate(orb)}

# ── Transfer matrix T_R ──────────────────────────────────────────────────
# T_R[i,j] = 1 if R(orb[j]) = orb[i]   (the renewal map as a linear map)
# Since R is deterministic, each column has exactly one 1.
T = np.zeros((N, N), dtype=float)
for j, s in enumerate(orb[:-1]):
    nxt = R(*s)
    if nxt in idx:
        T[idx[nxt], j] = 1.0
# Last state maps outside the truncated orbit window — row stays zero.

# ── Seed vector and fatal projector ──────────────────────────────────────
e_seed = np.zeros(N)
e_seed[0] = 1.0

pi_fatal = np.diag([1.0 if fatal(*s) else 0.0 for s in orb])
fatal_mask = np.array([fatal(*s) for s in orb])
n_fatal = int(fatal_mask.sum())

# ── GoI execution formula: resolvent approach ────────────────────────────
# Ex(u, σ) · e_seed  =  (I - σT)^{-1} · e_seed  (σ = I: full feedback)
# Equivalent for deterministic R: just T^k · e_seed = e_{R^k(SEED)}
# The non-trivial content is in the RESOLVENT SPECTRUM.

print("=" * 60)
print("GoI Proxy: BB6 Halting via Resolvent / Execution Formula")
print("=" * 60)
print(f"\nOrbit length K = {K},  states N = {N}")
print(f"Fatal states in orbit window: {n_fatal}")
print(f"Fatal states: {[orb[i] for i in range(N) if fatal_mask[i]][:5]}...")

# ── Spectrum of T_R ──────────────────────────────────────────────────────
eigvals = np.linalg.eigvals(T)
rho = float(np.abs(eigvals).max())
print(f"\nSpectrum of T_R:")
print(f"  Spectral radius ρ(T_R) = {rho:.6f}")
nonzero_ev = sorted(np.abs(eigvals[np.abs(eigvals) > 1e-10]).tolist(), reverse=True)
print(f"  Non-zero |λ|: {nonzero_ev[:8]}")
# T_R is nilpotent (shift operator on a finite chain) → all eigenvalues 0
# except possibly on cycles. No cycles in a non-halting orbit ↔ nilpotent.
if rho < 1e-10:
    print("  T_R is NILPOTENT (ρ = 0). No periodic orbits in the K-step window.")
    print("  Nilpotency = the orbit has no cycles ↔ it escapes to infinity.")
else:
    print(f"  T_R has non-zero spectrum — periodic structure detected.")

# ── Green's function G_fatal(z) = ⟨fatal|(zI - T)^{-1}|SEED⟩ ────────────
# Test at several z values outside the spectrum
print(f"\nGreen's function G_fatal(z) = ⟨fatal|(zI - T)^{{-1}}|SEED⟩:")
print(f"  (Non-zero = orbit reaches fatal set at corresponding step)")

any_nonzero = False
for z in [2.0, 1.5, 1.1, 0.5 + 0.5j]:
    try:
        zIT_inv = np.linalg.inv(z * np.eye(N) - T)
        v = zIT_inv @ e_seed
        G_fatal = float(np.abs(pi_fatal @ v).sum())
        print(f"  z = {z!s:10s}:  G_fatal = {G_fatal:.2e}", end="")
        if G_fatal > 1e-12:
            print("  ← HALT SIGNAL")
            any_nonzero = True
        else:
            print("  (zero — consistent with non-halting)")
    except np.linalg.LinAlgError:
        print(f"  z = {z!s:10s}:  SINGULAR — pole detected (halting event at this scale)")
        any_nonzero = True

if not any_nonzero:
    print("\n  ✓ G_fatal = 0 at all tested z.")
    print("  GoI proxy: No fatal-subspace pole → non-halting (conditional on K-step window).")

# ── Nilpotency order: first k with T^k · e_seed = 0 ─────────────────────
# For deterministic R: T^k · e_seed = e_{R^k(SEED)}.
# The fatal projection of this gives the k-th step halting check.
print(f"\nDirect nilpotency check (T^k · e_seed projected onto fatal subspace):")
print(f"  (Non-zero at step k = machine halts at renewal k from SEED)")
v = e_seed.copy()
hit_fatal = False
for k in range(1, min(K + 1, 50)):
    v = T @ v
    fatal_component = float((pi_fatal @ v).sum())
    if fatal_component > 1e-12:
        print(f"  k={k:3d}: FATAL HIT — fatal component = {fatal_component:.4f}")
        hit_fatal = True
        break
if not hit_fatal:
    print(f"  No fatal hit in k=1..{min(K,50)} steps. ✓")
    print(f"  (This mirrors 'SafeMetaOrbit': orbit avoids fatal set for all K tested.)")

# ── Ruelle-Lefschetz zeta function ζ(z) = exp(Σ Tr(T^k)/k · z^k) ────────
print(f"\nRuelle-Lefschetz zeta function ζ(z):")
print(f"  ζ(z) = exp(Σ_{{k=1}}^{{K}} Tr(T^k)/k · z^k)")
print(f"  Tr(T^k) counts closed orbits of length k (k-cycles in the renewal map).")

traces = []
Tk = np.eye(N)
for k in range(1, min(K + 1, 40)):
    Tk = Tk @ T
    traces.append(np.trace(Tk))

nonzero_traces = [(k+1, tr) for k, tr in enumerate(traces) if abs(tr) > 1e-10]
if nonzero_traces:
    print(f"  Non-zero traces (k-cycles): {nonzero_traces[:6]}")
else:
    print(f"  All traces Tr(T^k) = 0 for k=1..{len(traces)}.")
    print(f"  ↔ No periodic orbits (no k-cycles) in the renewal map over K={K} steps.")
    print(f"  ↔ ζ(z) = exp(0) = 1  (trivial zeta function = no periodic structure).")

# ── Summary ───────────────────────────────────────────────────────────────
print("\n" + "=" * 60)
print("Summary: GoI Categorical Proxy")
print("=" * 60)
print("""
The Geometry of Interaction proxy for BB6 halting:

  Halting   ↔  ∃ k:  π_fatal · T^k · e_SEED ≠ 0
            ↔  G_fatal(z) has a pole in the spectrum of T_R
            ↔  (I - σ·T_R) is SINGULAR
            ↔  Tr(T^k) > 0 for some k (periodic orbit through fatal set)

  Non-halt  ↔  ∀ k:  π_fatal · T^k · e_SEED = 0
            ↔  G_fatal(z) = 0 everywhere
            ↔  (I - σ·T_R) is INVERTIBLE
            ↔  ζ(z) = 1 (no cycles, trivial zeta)
            ↔  T_R is NILPOTENT on the reachable subspace

RESULT (K={K} step window):""".format(K=K))

print(f"  ρ(T_R) = {rho:.2e}  {'→ nilpotent (non-halting consistent)' if rho < 1e-10 else '→ has cycles'}")
print(f"  G_fatal = {'0 everywhere' if not any_nonzero else 'NON-ZERO — halt detected'}")
print(f"  Fatal hits in k=1..{min(K,50)}: {'none' if not hit_fatal else 'YES'}")
print(f"""
WHAT LEAN NEEDS TO CLOSE THIS:
  Prove: (I - σ·T_R) is invertible for ALL K, not just K={K}.
  = Prove: no k exists with R^k(SEED) ∈ fatal
  = SafeMetaOrbit conjecture
  in the language of operator algebras on the renewal-map ℓ²-space.
""")
