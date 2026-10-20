// -*- mode: Bluespec; -*-

// Copyright (c) 2026, Circle Internet Group, Inc. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * Lemma 2 violation by skipping rounds, in a scripted execution.
 *
 * Two correct processes leave a round without recording the value `v` that
 * can be decided in it: c5 skips round 1 and c1 skips round 2, by running
 * OnTimeoutPrecommit(r) with r above their current round.
 * With the Byzantine process b they make 2f + 1 precommits for `w` in round 3,
 * and c2-c5 replace `valid = (1, v)` by `(3, w)`.
 * The execution is then extended until c2-c5 decide `w` and c1 decides `v`,
 * which violates Agreement.
 *
 * Thanks to Alex Ranchal-Pedrosa for describing this problematic scenario.
 *
 * Run with: quint test double-round-skip.qnt --main double_round_skip
 *
 * A run can also be the initial state of a random simulation of the model,
 * for example, from the state where all processes have reached round 3:
 *   quint run double-round-skip.qnt --main double_round_skip \
 *     --init double_round_skip --step step --invariant lemma2 --max-steps 30
 *
 * It passes if OnTimeoutPrecommit does not update `valid`. With the update
 * of lines 48-50 of the pseudo-code, c5 records `v` when it skips round 1,
 * and the execution does not violate Lemma 2.
 */
module double_round_skip {

	import basicSpells.* from "./choreo_broadcast"

	/// Correct processes, `b` is the Byzantine process.
	pure val CORRECT = Set("c1", "c2", "c3", "c4", "c5")

	// c5 proposes `u` in round 0, c2 proposes `v` in round 1, b proposes `w`
	// in round 3. All rounds are before GST: timeouts are never guarded.
	import fast_tendermint(
		CORRECT		= CORRECT,
		FAULTS		= 1,
		FAULTY		= Set("b"),
		PROPOSERS	= ["c5", "c2", "c3", "b", "c4", "c1"],
		VALUES		= Map("c1" -> "a1", "c2" -> "v", "c3" -> "a3", "c4" -> "a4", "c5" -> "u"),
		BYZ_VALUES	= Set("v", "w"),
		GST_ROUND	= 100
	) as ft from "./fast-tendermint"

	// A second choreo instance drives the system, with the rules of `ft`.
	import choreo_broadcast(processes = CORRECT) as net from "./choreo_broadcast"

	action init = net::init({
		system:		CORRECT.mapBy(pid => ft::upon_init(pid)),
		messages:	Set(),
		events:		CORRECT.mapBy(pid => Set()),
		extensions:	"",
	})

	/// Random steps of the model, to simulate from the state reached by a run.
	action step = net::step(ft::listener, ft::noop_effect)

	/// Process `p` fires the rule `upon`, for a parameter given by `listen`
	/// that satisfies `keep`. Not enabled if there is no such parameter.
	action micro(p, listen, upon, keep) = {
		val ctx = net::convert_context(net::s, p)
		nondet param = listen(ctx).filter(keep).oneOf()
		net::process_transitions(p, Set(upon(ctx, param)), ft::noop_effect)
	}

	/// Micro steps of `act`, one after the other, for each process.
	action each(ps, act) = ps.length().reps(i => act(ps[i]))

	// One micro step per rule, restricted to a round (and a value).
	action start(ps) =
		each(ps, p => micro(p, ft::start_rule, ft::StartRound, _ => true))
	action fresh_proposal(ps, round, value) =
		each(ps, p => micro(p, ft::fresh_proposal_rule, ft::upon_fresh_proposal,
			proposal => proposal.round == round and proposal.value == value))
	action re_proposal(ps) =
		each(ps, p => micro(p, ft::re_proposal_rule, ft::upon_re_proposal, _ => true))
	action decision(ps, value) =
		each(ps, p => micro(p, ft::decision_rule, ft::upon_decision,
			params => params.proposal.value == value))
	action observation(ps) =
		each(ps, p => micro(p, ft::observation_rule, ft::upon_observation, _ => true))
	action quorum_any(ps, round) =
		each(ps, p => micro(p, ft::quorum_any_rule, ft::upon_quorum_any,
			msgs => ft::unique_round(msgs) == round))
	action timeout_prepropose(ps, round) =
		each(ps, p => micro(p, ft::expired_timeout_prepropose, ft::OnTimeoutPrePropose,
			r => r == round))
	action timeout_propose(ps, round) =
		each(ps, p => micro(p, ft::expired_timeout_propose, ft::OnTimeoutPropose,
			r => r == round))
	action timeout_precommit(ps, round) =
		each(ps, p => micro(p, ft::expired_timeout_precommit, ft::OnTimeoutPrecommit,
			r => r == round))

	/// Lemma 2, as `ft::lemma2`, on the messages and processes of `net`.
	// `ft::lemma2` reads the state of the choreo instance of `ft`.
	val lemma2 = {
		val all_precommits = ft::precommits(net::s.messages)
		val precommitted = all_precommits.map(precommit => precommit.value).exclude(Set(ft::Nil))
		tuples(all_precommits.map(precommit => precommit.round), precommitted).forall(((round, value)) =>
			all_precommits.filter(precommit => precommit.round == round and precommit.value == value).
				map(precommit => precommit.sender).size() < ft::QUORUM or
			net::s.system.values().forall(process =>
				process.valid.value == value or process.valid.round < round
			)
		)
	}

	/// Agreement: no two correct processes decide differently.
	// `ft::agreement` reads the state of the choreo instance of `ft`.
	val agreement = tuples(CORRECT, CORRECT).forall(((p1, p2)) =>
		net::s.system.get(p1).decision == ft::Nil or
		net::s.system.get(p2).decision == ft::Nil or
		net::s.system.get(p1).decision == net::s.system.get(p2).decision
	)

	/// Round 0: c5 precommits `u`, c1-c4 time out and precommit nil, leave
	/// round 0. c5 stays in round 0.
	/// Round 1: c2 proposes `v`, c1-c4 precommit `v`. c2-c4 record `v` as valid
	/// and leave round 1. c1 does not see the precommits of the others.
	run rounds_0_and_1 = init
		.then(start(["c5", "c1", "c2", "c3", "c4"]))
		.then(fresh_proposal(["c5"], 0, "u"))
		.then(timeout_propose(["c1", "c2", "c3", "c4"], 0))
		.then(quorum_any(["c1", "c2", "c3", "c4"], 0))
		.then(timeout_precommit(["c1", "c2", "c3", "c4"], 0))
		.then(timeout_prepropose(["c2"], 1))
		.then(fresh_proposal(["c2", "c1", "c3", "c4"], 1, "v"))
		.then(observation(["c2", "c3", "c4"]))
		.then(quorum_any(["c2", "c3", "c4"], 1))
		.then(timeout_precommit(["c2", "c3", "c4"], 1))
		// A decision of `v` is possible in round 1, and respected so far
		.expect(lemma2)

	/// First skip: c5 leaves round 0 for round 2, without recording `v`.
	/// Round 2: c3 re-proposes `v`, c2, c4 and c5 precommit nil.
	/// Second skip: c1 leaves round 1 for round 3, without recording `v`.
	/// c2-c5 leave round 2. All processes are in round 3.
	run double_round_skip = rounds_0_and_1
		.then(quorum_any(["c5"], 1))
		.then(timeout_precommit(["c5"], 1))
		.then(re_proposal(["c3"]))
		.then(timeout_propose(["c2", "c4", "c5"], 2))
		.then(quorum_any(["c1"], 2))
		.then(timeout_precommit(["c1"], 2))
		.then(quorum_any(["c2", "c3", "c4", "c5"], 2))
		.then(timeout_precommit(["c2", "c3", "c4", "c5"], 2))
		// Lemma 2 still holds
		.expect(lemma2)

	/// Round 3: c1 and c5 are not locked on `v`, they precommit `w`, as b
	/// does. c2-c4 are locked, they precommit nil. c2-c5 observe 2f + 1
	/// precommits for `w`, and record `(3, w)`, that overrides `(1, v)`.
	/// Lemma 2 is violated: `v` can be decided in round 1.
	run lemma2_violated = double_round_skip
		.then(fresh_proposal(["c1", "c5", "c2", "c3", "c4"], 3, "w"))
		.then(observation(["c2", "c3", "c4", "c5"]))
		.expect(not(lemma2))

	/// Agreement is not violated yet, as no process has decided.
	/// Round 4: c2-c5 leave round 3 with `valid = (3, w)`, and c4, the proposer
	/// of round 4, re-proposes `w`. c2-c5 precommit `w`, as does b: they hold
	/// n - f precommits for `w` and the proposal of round 3, and decide `w`.
	/// c1, still in round 3, holds the precommits of round 1 and decides `v`.
	/// Agreement is violated.
	run agreement_violated = lemma2_violated
		.then(quorum_any(["c2", "c3", "c4", "c5"], 3))
		.then(timeout_precommit(["c2", "c3", "c4", "c5"], 3))
		.then(re_proposal(["c2", "c3", "c4", "c5"]))
		.expect(agreement)
		.then(decision(["c2", "c3", "c4", "c5"], "w"))
		.expect(agreement)
		.then(decision(["c1"], "v"))
		.expect(not(agreement))
}
