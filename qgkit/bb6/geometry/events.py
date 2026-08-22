"""Incision-event extraction.

Two modes:

* :func:`antihydra_events` — the exact certified event process.  Mirrors the
  Lean ``eorbit`` / ``hydraOrbit`` of ``packages/bbchallenge`` (the two are
  proved equivalent to the full abstract orbit by ``eventSafe_iff_safeOrbitA``
  and ``hydraSafe_iff_safeOrbitA``): state ``(b, heads)`` from ``(12, 2)``,
  one event per counter movement, ``b <- b + b // 2``.
* :func:`record_events` — a *heuristic proxy* for machines without a proven
  emulation: frontier records (via ``qgkit.bb6.vcollatz.classify``) filtered
  to near-collapse configurations.  Explicitly not certified.
"""

from __future__ import annotations

from qgkit.bb6.vcollatz.classify import simulate_records


def antihydra_events(n_events: int):
    """Yield the first ``n_events`` certified Antihydra incision events.

    Each event dict carries the 1-D hydra view (``b``, ``heads``, parity) and
    the reconstructed boundary triple ``(a, m, c)`` (the Lean ``eorbit``
    state: ``m = 1`` iff ``b`` even, ``c = 2 + 3*(b - 5 - m)//2``), plus the
    death margin at drops and the exact raw-step cost of the event (boundary
    rule + following hydra volley, from the proved step counts ``2c + 11`` /
    ``2c + 15`` / ``2n + 2k + 22``).

    The orbit dying (``heads <= 1`` at odd ``b``) raises ``RuntimeError`` —
    observing that within any finite budget would refute ``HydraSafe`` and
    (by ``hydraSafe_iff_safeOrbitA``) the machine reduction's hypothesis.
    """
    b, heads = 12, 2
    for k in range(n_events):
        m = 1 if b % 2 == 0 else 2
        big_m = b - 5  # pre-volley block value M
        c = 2 + 3 * ((big_m - m) // 2)
        odd = b % 2 == 1
        # exact raw-step cost of this event: the boundary rule, then the
        # hydra volley down from the new block value M' = b + b//2 - 5
        if odd:
            if heads <= 1:
                raise RuntimeError(
                    f"event process died at event {k} (b={b}, heads={heads}) — "
                    "this would refute HydraSafe; report immediately"
                )
            rule_steps = 2 * c + 15  # drop_step
        else:
            # merge_chain: 2n + 2k + 22 with n = heads (counter block), k = c
            rule_steps = 2 * heads + 2 * c + 22
        # volley from (a', M', 2): j hydra steps, the i-th costing 2*(2+3i)+11;
        # closed form sum = 3j^2 + 12j (j is astronomically large, never loop)
        big_m_next = (b + b // 2) - 5
        j = (big_m_next - (1 if (b + b // 2) % 2 == 0 else 2)) // 2
        volley_steps = 3 * j * j + 12 * j
        yield {
            "k": k,
            "b": b,
            "heads": heads,
            "a": heads,
            "m": m,
            "c": c,
            "rule": "drop" if odd else "merge",
            "death_margin": (heads - 2) if odd else None,
            "raw_steps": rule_steps + volley_steps,
        }
        heads = heads - 1 if odd else heads + 2
        b = b + b // 2


def record_events(code: str, steps: int = 200_000, cap: int = 2_000,
                  near: int = 2):
    """Heuristic incision proxy for machines without a proven emulation.

    Simulates frontier records and yields the ones that look like incisions:
    a block at or below ``near`` cells (near-collapse), or a change in the
    number of blocks relative to the previous record.  Returns
    ``(halted, stop_step, events, n_records)``.

    This is bounded empirical structure with a heuristic event definition —
    nothing here is certified, unlike :func:`antihydra_events`.
    """
    halted, stop_step, records = simulate_records(code, steps=steps, cap=cap)
    events = []
    prev_dims = None
    for rec in records:
        blocks = rec["blocks"]
        dims = len(blocks)
        min_block = min(blocks) if blocks else 0
        etype = []
        if blocks and min_block <= near:
            etype.append("near_collapse")
        if prev_dims is not None and dims != prev_dims:
            etype.append("dim_change")
        if etype:
            events.append({
                "step": rec["step"],
                "state": rec["state"],
                "side": rec["side"],
                "blocks": list(blocks),
                "dims": dims,
                "min_block": min_block,
                "width": rec["width"],
                "ones": rec["ones"],
                "type": "+".join(etype),
            })
        prev_dims = dims
    return halted, stop_step, events, len(records)
