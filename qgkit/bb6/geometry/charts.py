"""Non-Euclidean coordinate charts for incision plotting.

Floating-point renderings of the exact charts in
``packages/extensions/Extensions/Charts.lean``.  The choice of charts is a
modeling hypothesis (see ``docs/learning/03-noneuclidean-incision-geometry.md``)
— in raw Euclidean coordinates an escaping orbit degenerates every plot;
these normalizations are where a machine-characteristic incision figure
would show up if one exists.
"""

from __future__ import annotations

import math

_LN2 = math.log(2)


def _log1p_big(v) -> float:
    """``log1p`` that survives integers beyond float range (orbit values grow
    like 1.5^k and overflow floats within a few thousand events)."""
    if v < 10 ** 300:
        return math.log1p(v)
    bl = v.bit_length()
    mantissa = v >> (bl - 53)
    return _LN2 * (bl - 53) + math.log(mantissa)


def log_chart(vec):
    """Componentwise ``log1p``: multiplicative growth becomes additive."""
    return [_log1p_big(v) for v in vec]


def simplex_chart(vec):
    """Projective normalization onto the probability simplex.

    The death face ``{m = 0}`` of the Antihydra orbit is literally a face of
    the simplex in these coordinates.  Returns ``None`` for the zero vector.
    """
    s = sum(vec)
    if s == 0:
        return None
    return [v / s for v in vec]


def h2_chart(vec):
    """Upper-half-plane surrogate ``(x, y)``.

    ``x`` is the normalized imbalance between the first and last component,
    ``y = log1p(total mass)`` the scale height — exponential escape becomes
    steady upward motion, and bounded structure shows up as a bounded
    figure.  Mirrors ``Extensions.h2Chart`` (exact integer version).
    """
    s = sum(vec)
    if s == 0:
        return (0.0, 0.0)
    return ((vec[0] - vec[-1]) / s, _log1p_big(s))
