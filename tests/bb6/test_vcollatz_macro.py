from qgkit.bb6.vcollatz.classify import simulate_records
from qgkit.bb6.vcollatz.macro import astate, fit_macro_rules, predict_next, replay_records


TRANSLATED_CYCLER = "1RB---_1RA---"


def test_translated_cycler_fits_and_replays_exactly():
    halted, _stop, records = simulate_records(TRANSLATED_CYCLER, steps=5_000)
    assert not halted
    rules = fit_macro_rules(records)
    replay = replay_records(records, 8, rules)
    assert rules["n_conflicts"] == 0
    assert replay["exact"]
    assert replay["n_mismatches"] == 0


def test_predict_abstains_on_unseen_group_key():
    _halted, _stop, records = simulate_records(TRANSLATED_CYCLER, steps=5_000)
    rules = fit_macro_rules(records)
    state, side, blocks = astate(records[-1])
    assert predict_next((state, "L" if side == "R" else "R", blocks), rules) is None
