# Formal Tendermint

Formal specifications and model checking for Tendermint-style consensus algorithms.

## Protocols

### Fast Tendermint (`fast-tendermint/`)

A variation of [Tendermint](https://arxiv.org/abs/1807.04938) that achieves consensus
in two communication steps while tolerating `f < n/5` Byzantine processes.

Described in _"Fast Tendermint: Speeding Up a Foundational
Consensus Protocol"_, DISC 2026. Full version: .

## Tools

- [Quint](https://quint.sh) — model checking and simulation

## Running the Quint Models

General module `main`, with Byzantine actors and asynchrony.
Checks the `agreement` safety invariant with up to 100 state transitions:

    $ quint run fast-tendermint.qnt --main main --invariant agreement --max-steps 100

Liveness-enabling module `live`, with post-GST guarantees guarding timeouts.
Checks the `all_decided` liveness witnesses across simulated executions.
From 45 state transitions, all 5 correct processes should reach a decision:

    $ quint run fast-tendermint.qnt --main live --invariant agreement --witnesses all_decided --max-steps 45

The `main` module reaches GST from round 3. From around 120 state transitions,
all correct processes should reach a decision:

    $ quint run fast-tendermint.qnt --main main --invariant agreement --witnesses all_decided --max-steps 120
