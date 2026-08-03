from __future__ import annotations

from qgkit.bb6.vcollatz.classify import (
    KNOWN_WIKI_CRYPTIDS,
    abstraction_class,
    compact_growth_features,
    simulate_records,
)

ANTIHYDRA = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"
BB2_HALTER = "1RB1LB_1LA---"


def test_simulate_records_detects_halt():
    halted, stop_step, _records = simulate_records(BB2_HALTER, steps=1_000)
    assert halted
    assert stop_step < 10


def test_simulate_records_antihydra_produces_frontier_records():
    halted, _stop_step, records = simulate_records(ANTIHYDRA, steps=200_000, cap=200)
    assert not halted
    assert len(records) >= 40
    assert {"step", "side", "state", "width", "ones", "blocks"} <= set(records[0])


def test_compact_growth_features_short_input_is_none():
    assert compact_growth_features([]) is None


def test_compact_growth_features_antihydra_has_score():
    _halted, _stop, records = simulate_records(ANTIHYDRA, steps=200_000, cap=200)
    features = compact_growth_features(records)
    # Antihydra grows and keeps compact block structure; features must exist.
    assert features is not None
    assert isinstance(features["score"], float)
    assert features["dmax"] >= 1


def test_abstraction_class_labels():
    assert abstraction_class([2] * 10) == "SHORT_UNDECIDED"
    assert abstraction_class(list(range(1, 40))) == "GROWING_DIM"
    assert abstraction_class([3] * 60) == "FIXED_DIM_CARRY"
    assert abstraction_class([2, 3, 4, 3, 2, 3, 4, 3] * 10) == "BOUNDED_VARYING"


def test_known_wiki_cryptids_set_size():
    assert len(KNOWN_WIKI_CRYPTIDS) == 17


from qgkit.bb6.vcollatz.classify import characterize_holdout

TRANSLATED_CYCLER = "1RB---_1RA---"


def test_characterize_decides_translated_cycler():
    row = characterize_holdout(TRANSLATED_CYCLER, decider_budget=5_000,
                               sim_steps=5_000, extract_steps=5_000)
    assert row["decided"] is True
    assert row["label"].startswith("DECIDED_NONHALT")


def test_characterize_decides_halter():
    row = characterize_holdout(BB2_HALTER, decider_budget=5_000,
                               sim_steps=5_000, extract_steps=5_000)
    assert row["label"] == "DECIDED_HALTS"


def test_characterize_antihydra_undecided_with_features():
    row = characterize_holdout(ANTIHYDRA, decider_budget=2_000,
                               backward_depth=50, ctl_radius=2,
                               far_dfa_states=4,
                               sim_steps=200_000, extract_steps=50_000)
    assert row["decided"] is False
    assert row["features"] is not None
    assert row["label"] in {
        "VCOLLATZ_EXACT_PROJECTION", "CRYPTID_COMPACT_GROWTH",
        "GROWING_DIM", "FIXED_DIM_CARRY", "BOUNDED_VARYING", "SHORT_UNDECIDED",
    }
    assert row["novel"] is False  # Antihydra is a known wiki cryptid


def test_characterize_skip_decider():
    row = characterize_holdout(ANTIHYDRA, run_decider=False,
                               sim_steps=100_000, extract_steps=20_000)
    assert row["decided"] is False
    assert row["decider"] is None


def test_characterize_demotes_unsound_bouncer_certificate():
    row = characterize_holdout(
        "1RB1RC_1LA---_0RE1LD_0LF0LC_1RA1RF_1RE0LF",
        decider_budget=20_000, backward_depth=200, ctl_radius=4,
        far_dfa_states=6, sim_steps=200_000, extract_steps=50_000)
    assert row["decided"] is False
    assert row["decider"]["toc_class"] == "bouncer"
    assert row["decider"]["demoted"] == "unsound_bouncer_certificate_2026-07-18"
    assert not row["label"].startswith("DECIDED")
