# Fast Tendermint protocol

Fast Tendemint is a variation of [Tendermint consensus protocol][tendermint-arxiv]
that achieves consensus in two communication steps while tolerating `f < n/5`
Byzantine processes.

The original algorithm achieves consensus in three communication steps while
tolerating `f < n/3` Byzantine processes, which is optimal.
Fast Tendermint speed ups the original algorithm, the cost of which is
requiring `n = 5f + 1` processes in order to tolerate `f` Byzantine processes.

The protocol was described in the paper
_"Brief Announcement: Fast Tendermint: Speeding Up a Foundational Consensus Protocol"_,
to appear in the upcoming LIPIcs volume "DISC 2026".

The full version of the paper is availble in arXiv: <arXiv link>

## Quint Model

The Quint language and the `quint` command can be retrieved in https://quint.sh.

This module is composed of two files:

1. `choreo_broadcast.qnt`: generic construction ("library") for modelling distributed algorithms;
2. `fast-tendermint.qnt`: Fast Tendermint protocol modelling using choreo "library".

### Execution

General moduling, module `main`, with Byzantine actors and asynchrony.
Checks the `agreement` safety invariant with up to 100 state transitions:

    $ quint run fast-tendermint.qnt --main main --invariant agreement --max-steps 100

Liveness enabling module `live`, with post-GST guarantees guarding timeouts.
Check the `all_decided` liveness witnesses, namely the number of simulated
executions when all correct processes reach the same decision.
From 45 state transitions, all 5 correct processes should reach a decision:

    $ quint run fast-tendermint.qnt --main live --invariant agreement --witnesses all_decided --max-steps 45

The `main` module reaches GST from round 3. From around 120 state transitions,
all correct processes should reach a decision:

    $ quint run fast-tendermint.qnt --main main --invariant agreement --witnesses all_decided --max-steps 120

[tendermint-arxiv]: https://arxiv.org/abs/1807.04938
