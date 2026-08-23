"""Predictive orbit emulator for Antihydra.

Given an event index (or a raw-step target), predicts the machine's exact
record configuration — abstract state (a, m, c), control state, absolute
head position, and the exact raw step index at which that record occurs —
without simulating a single raw step.  Every quantity comes from the
certified layer:

* abstract dynamics: the Lean ``eorbit`` (hydra / drop / merge + volley);
* per-rule raw costs: ``hydra_step`` (2c+11), ``drop_step`` (2c+15, plus
  the one-step A->B bump its transport appends), ``merge_chain``
  (2a+2c+22), summed in closed form (``volleyCost_closed``);
* head positions: the ``Realizes`` grammar (head = p + 3 + m + c) with
  per-rule anchor deltas read off the transport lemmas;
* skip windows: ``halt_localized`` — no orbit death within the next
  ``a - 1`` events.

The rule constants are *validated differentially*: ``tests/bb6/
test_dragon_predictor.py`` runs the raw machine and asserts that every
predicted record index and head position is exactly right.  Prediction is
honest arithmetic about the abstract layer; the differential test is what
ties it to the tape.
"""

from __future__ import annotations

ANTIHYDRA = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

# Raw-step offset and anchor of the first abstract record (2, 7, 2):
# startup_run — stepN 62 blankStart = <B, 6, startTape>, and Realizes
# puts head = p + 3 + m + c, so p = 6 - 3 - 7 - 2 = -6.
STARTUP_STEPS = 62
STARTUP_ANCHOR = -6

# Per-rule raw costs (from the proven trajectories) and anchor deltas
# (from the transport lemmas; differentially validated).
HYDRA_COST = lambda c: 2 * c + 11          # noqa: E731
DROP_COST = lambda c: 2 * c + 15 + 1       # noqa: E731  (+1: transport A->B bump)
MERGE_COST = lambda a, c: 2 * a + 2 * c + 22  # noqa: E731
HYDRA_DP, DROP_DP, MERGE_DP = 0, -1, -1


class OrbitPredictor:
    """Lazily extends the abstract orbit, memoizing per-record data."""

    def __init__(self):
        # record r: (a, m, c, anchor p, raw step index of the record)
        self._recs = [(2, 7, 2, STARTUP_ANCHOR, STARTUP_STEPS)]

    def _extend(self):
        a, m, c, p, step = self._recs[-1]
        if m >= 3:
            self._recs.append((a, m - 2, c + 3, p + HYDRA_DP,
                               step + HYDRA_COST(c)))
        elif m == 2:
            if a < 2:
                raise RuntimeError(
                    f"orbit died at record {len(self._recs) - 1} — refutes "
                    "HydraSafe; report immediately")
            self._recs.append((a - 1, c + 3, 2, p + DROP_DP,
                               step + DROP_COST(c)))
        elif m == 1:
            self._recs.append((a + 2, c + 2, 2, p + MERGE_DP,
                               step + MERGE_COST(a, c)))
        else:
            raise RuntimeError("m = 0: dead orbit")

    def record(self, r: int) -> dict:
        """Exact prediction for abstract record ``r`` (one per rule
        application, volleys not collapsed — the finest certified grain)."""
        while len(self._recs) <= r:
            self._extend()
        a, m, c, p, step = self._recs[r]
        return {
            "record": r,
            "a": a, "m": m, "c": c,
            "state": "B",
            "head": p + 3 + m + c,      # Realizes conjunct 8
            "anchor": p,
            "raw_step": step,
            "boundary": m <= 2,
            "safe_horizon_events": max(a - 1, 0),   # halt_localized
        }

    def record_at_step(self, n: int) -> dict:
        """The latest record at raw step <= n (bracketing a raw-step
        target without simulating)."""
        if n < STARTUP_STEPS:
            raise ValueError("target inside the 62-step startup")
        r = 0
        while True:
            while len(self._recs) <= r + 1:
                self._extend()
            if self._recs[r + 1][4] > n:
                out = self.record(r)
                out["next_record_step"] = self._recs[r + 1][4]
                return out
            r += 1
