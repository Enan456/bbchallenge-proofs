"""Incision geometry: event extraction and non-Euclidean charts (plan 3).

Empirical counterpart of the Lean packages:

* ``packages/bbchallenge/Bridge/Incision.lean`` proves that checking the
  Antihydra abstract orbit only at boundary events is sound and complete
  (``eventSafe_iff_safeOrbitA``); :func:`events.antihydra_events` is the
  Python mirror of that certified event process.
* ``packages/extensions/Extensions/Charts.lean`` holds the exact chart
  definitions; :mod:`charts` is their floating-point rendering.

Everything produced here is bounded empirical structure — no plot or metric
is evidence of halting or non-halting.
"""

from qgkit.bb6.geometry.events import antihydra_events, record_events
from qgkit.bb6.geometry.charts import log_chart, simplex_chart, h2_chart

__all__ = [
    "antihydra_events",
    "record_events",
    "log_chart",
    "simplex_chart",
    "h2_chart",
]
