Fast Tendermint protocol modelled in Quint
==========================================

The Quint language and the `quint` command can be retrieved in https://quint.sh.

This module is composed of two files:

1. choreo_broadcast.qnt: generic construction ("library") for modelling distributed algorithms;
2. fast-tendermint.qnt: Fast Tendermint protocol modelling using choreo "library".

Execution
=========

General moduling, module 'main', with Byzantine actors and asynchrony.
Checks the `agreement` safety invariant with up to 100 state transitions:

$ quint run fast-tendermint.qnt --main main --invariant agreement --max-steps 100

Liveness enabling module 'live', with post-GST guarantees guarding timeouts.
Check the `all_decided` liveness witnesses, namely the number of simulated
executions when all correct processes reach the same decision.
From 45 state transitions, all 5 correct processes should reach a decision:

$ quint run fast-tendermint.qnt --main live --invariant agreement --witnesses all_decided --max-steps 45

The 'main' module reaches GST from round 3. From around 120 state transitions,
all correct processes should reach a decision:

$ quint run fast-tendermint.qnt --main main --invariant agreement --witnesses all_decided --max-steps 120
