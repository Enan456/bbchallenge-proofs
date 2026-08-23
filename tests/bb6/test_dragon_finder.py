from __future__ import annotations

from fractions import Fraction

from qgkit.bb6.dragon.finder import OrbitFinder
from qgkit.bb6.dragon.predictor import ANTIHYDRA

DOSSIER1 = "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"


def test_finder_recovers_antihydra_rules_exactly():
    spec = OrbitFinder(ANTIHYDRA, steps=150_000).fit()
    assert spec is not None, "fail-closed fit rejected Antihydra"
    assert spec["n_transitions"] > 50
    # the hydra rule on interior records: (a, m, c) -> (a, m-2, c+3), 2c+11
    hydra = [r for k, r in spec["rules"].items()
             if k[0] == 3 and k[1] == 3 and k[2] == (3, 3, 3)]
    assert hydra, "no interior 3-block rule found"
    for r in hydra:
        a_map, m_map, c_map = r["maps"]
        assert a_map[:3] == (1, 0, 0) and a_map[3] == 0        # a' = a
        assert m_map[:3] == (0, 1, 0) and m_map[3] == -2       # m' = m-2
        assert c_map[:3] == (0, 0, 1) and c_map[3] == 3        # c' = c+3
        assert r["cost"][:3] == (0, 0, 2) and r["cost"][3] == 11  # 2c+11


def test_finder_fits_dossier1_exactly():
    spec = OrbitFinder(DOSSIER1, steps=150_000).fit()
    assert spec is not None, "fail-closed fit rejected dossier-1"
    assert spec["n_transitions"] > 50
    assert spec["n_rules"] >= 3


def test_fractions_are_exact():
    spec = OrbitFinder(ANTIHYDRA, steps=80_000).fit()
    for rule in spec["rules"].values():
        for m in list(rule["maps"]) + [rule["cost"]]:
            assert all(isinstance(x, Fraction) or x == int(x) for x in m)
