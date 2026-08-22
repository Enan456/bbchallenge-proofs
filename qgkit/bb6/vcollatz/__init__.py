"""Vector generalized Collatz steps for BB6 experiments.

This package exposes a reversible vector representation useful for classical
exploration and search. It is bookkeeping over exact integer arithmetic and
makes no claim of quantum advantage or speedup.
"""

# The reversible-map module lives in the parent Quantum_Geometry repo and is
# not part of this packaged snapshot (which ships classify.py + macro.py
# only); guard the import so the shipped modules stay usable.
try:
    from .reversible import (VGCMap, batched_step, reversible_step,
                             reverse_step, step_vec)
    __all__ = [
        "VGCMap",
        "batched_step",
        "reversible_step",
        "reverse_step",
        "step_vec",
    ]
except ImportError:  # packaged repo: reversible not included
    __all__ = []
