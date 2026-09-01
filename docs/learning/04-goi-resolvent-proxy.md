---
title: "Geometry of Interaction (GoI) as a Spectral Resolvent"
status: "implemented"
related: 
  - "03-noneuclidean-incision-geometry.md"
  - "qgkit/bb6/goi_proxy.py"
  - "qgkit/bb6/GoI_Resolvent.lean"
---

# The Geometry of Interaction (GoI) Resolvent Proxy

This document defines the exact conceptual and algebraic bridge between the BB6 `SafeMetaOrbit` invariant, Girard's Geometry of Interaction (GoI), and the Quantum Incidence Geometry (QIG) spectral tools in the `Quantum_Geometry` monorepo. 

This serves as the primary orienting document for human researchers and autonomous proving agents (APOLLO, SURYA, SOL) attempting to formalize the halting bounds.

## 1. The Epistemic Shift: From MIP* to Spectral Theory

The full $\text{MIP}^* = \text{RE}$ protocol requires an unbounded tower of quantum entanglement ($\chi = \infty$) to verify Turing-complete execution histories. This is computationally opaque and mathematically fragile (collapsing to $\text{NEXP}$ under finite noise).

We do not need the full game hierarchy. We only need the underlying operator algebra that governs the verification game. In GoI, a program's execution trace is represented by the execution formula:
$$ \text{Ex}(u, \sigma) = u (I - \sigma u)^{-1} $$
where $u$ is the program transition matrix (the renewal map $R$) and $\sigma$ is the feedback wire. 

Algebraically, $(I - \sigma u)^{-1}$ is exactly the **resolvent operator** $R(z) = (zI - T)^{-1}$ evaluated at $z=1$. 

**The Halting Proxy:**
*   If the machine **halts**, the execution reaches an absorbing state. The infinite Neumann series $\sum (\sigma u)^k$ truncates, but the resolvent develops a **pole** in the fatal subspace. 
*   If the machine **never halts** (e.g., escaping to infinity), the transfer operator $T_R$ is locally nilpotent. There are no closed cycles ($\zeta(z) = 1$), and the resolvent $R(1)$ is perfectly invertible with no poles. 

## 2. The Exact Mathematical Dictionary

| BB6 Domain | Operator Theory / QIG Domain |
| :--- | :--- |
| TM Transition Table $\delta$ | Generators of the partial configuration monoid |
| Renewal Map $R(a,b)$ | Shift operator / Transfer matrix $T_R$ |
| Fatal Set $F$ | Absorbing ideal / Projection operator $\pi_{\text{fatal}}$ |
| Halting Event | Pole in the Green's function $G_{\text{fatal}}(z) = \langle \text{fatal} \vert (zI - T_R)^{-1} \vert \text{SEED} \rangle$ |
| `SafeMetaOrbit` | $T_R$ is nilpotent on reachable states; $G_{\text{fatal}}(1) = 0$ |
| Simplex Charting (a,b) | Fisher-Rao geometry / Wootters distance $D_W$ |

## 3. Autoprover Directives (APOLLO / SURYA / SOL)

> **[!] AGENT DIRECTIVE: CROSS-REFERENCE PROTOCOL**
> When working on `qgkit/bb6/GoI_Resolvent.lean` in this repository, you MUST cross-reference the operator algebraic structures defined in the `Quantum_Geometry` monorepo.

*   **Topological Debt & Invertibility**: The proof of `goi_invertible_iff_safe` maps directly to the topological debt null-space proofs. Cross-reference `lean/QIG/TopologicalDebt.lean` and `lean/QIG/RamanujanResolvent.lean` in the monorepo. The "fatal set" corresponds exactly to the subspace where Wigner Mana $\mathcal{M}^- > 0$.
*   **Wootters Distance / Fisher-Rao**: The floating-point charts in `geometry/charts.py` have been formalized. The simplex chart maps (a,b) to a probability vector. The distance from the orbit to the fatal set is governed by the Wootters distance $D_W$. See `zx_error_prop_tools/src/core.py` in the monorepo for the exact `wootters_distance` primitive.
*   **MPO Bond Dimension Bound**: The renewal map $R$ has exactly $3$ piecewise-affine regimes. Therefore, the Schmidt rank of the GoI transfer matrix is bounded by $3$. The maximum entanglement required to verify the geometry of the BB6 orbit in a tensor-network MIP* game is $S = \log_2(3) \approx 1.58$ bits. 

## 4. File Manifest

The `GoI_Integration` implementation is localized in `qgkit/bb6/`:
1.  `goi_proxy.py`: Computes $T_R$, the resolvent Green's function, nilpotency, and the Ruelle-Lefschetz zeta function. 
2.  `halting_game_mip.py`: The nonlocal game framing. Computes the success probability of a seam-forging prover and bounds it using classical and $\chi=3$ quantum tensor-network limits.
3.  `stage_bb6_qig_contextuality.py`: Explicitly computes Wigner Mana ($M^-$) and the Fisher-Rao geometric safety margin of the orbit against the fatal set.
4.  `GoI_Resolvent.lean`: The raw-to-macro Lean 4 contract equating `SafeMetaOrbit` to resolvent invertibility. (Target for APOLLO).
