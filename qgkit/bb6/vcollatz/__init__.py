"""Vector generalized Collatz steps for BB6 experiments.

This package exposes a reversible vector representation useful for classical
exploration and search. It is bookkeeping over exact integer arithmetic and
makes no claim of quantum advantage or speedup.
"""

from .reversible import VGCMap, batched_step, reversible_step, reverse_step, step_vec

__all__ = [
    "VGCMap",
    "batched_step",
    "reversible_step",
    "reverse_step",
    "step_vec",
]
