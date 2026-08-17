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
 * Fast Tendermint Quint model.
 */
module fast_tendermint {

	import basicSpells.* from "./choreo_broadcast"
	import choreo_broadcast(processes = CORRECT) as choreo from "./choreo_broadcast"

	// ========= Types ========== //

	type Process = str
	type Round = int
	type Step = NoStep | PreProposeStep | ProposeStep | PrecommitStep
	type Value = str
	type ValueId = Option[Value] // Option := None | Some(v)
	val Nil = None

	// Type for `valid := (round, value)` field
	type RoundValue = { round: Round, value: ValueId }

	// Process state
	type State = {
		round: Round,
		step: Step,
		decision: Option[Value],
		valid: RoundValue,
	}

	/// PROPOSAL message.
	/// if valid_round == -1, then value is a Value v
	/// else value is a non-Nil ValueId id(v)
	type ProposalMessage = {
		sender: Process,
		round: Round,
		value: Value,
		valid_round: Round,
	}

	/// PRECOMMIT message.
	type PrecommitMessage = {
		sender: Process,
		round: Round,
		value: ValueId,
	}

	/// Fast Tendermint helpers

	/// Returns a full value to propose.
	// Each process is assigned a value.
	pure def getValue(pid: Process) : Value =
		VALUES.get(pid)

	/// Returns an unique identifier for a value.
	pure def id(v: Value) : ValueId = Some(v)

	/// Round-robin proposers with the configured schedule.
	pure def proposer(round: Round) : Process =
		PROPOSERS[round % PROPOSERS.length()]

	/// Application-specific validity predicate.
	pure def validate(v: Value) : bool = true

	// === Thresholds === //

	/// Number of processes
	pure val N = CORRECT.size() + FAULTY.size()

	/// Quorum: all non-faulty processes
	// When N = 5F + 1, QUORUM = 4F + 1
	pure val QUORUM = N - FAULTS


	/// Value-validity quorum
	// Provided that N > 5F (fault tolerance assumption), any two sets with
	// QUORUM and VALID_QUORUM processes share at least one correct process.
	pure val VALID_QUORUM = 2 * FAULTS + 1

	// ==== Choreo types and setup ==== //

	/// Two message types
	type Message =
		| Proposal(ProposalMessage)
		| Precommit(PrecommitMessage)

	/// One timeout per round step
	type Timeout = {
		round: Round,
		step: Step,
	}

	// No extensions in use
	type Extensions = str

	// No custom effects
	type NoEffect = str

	type Effect			= choreo::Effect[Message, Timeout, NoEffect]
	type LocalState		= choreo::LocalState[Process, State]
	type LocalContext	= choreo::LocalContext[Process, State, Message, Timeout, Extensions]
	type Transition		= choreo::Transition[Process, State, Message, Timeout, NoEffect]
	type GlobalContext	= choreo::GlobalContext[Process, State, Message, Timeout, Extensions]

	/// Initial step of the state machine
	action init = choreo::init({
		// map: Process -> LocalState
		system: 	CORRECT.mapBy(pid => upon_init(pid)),
		// Set[Message]
		messages:	Set(),
		// map: Process -> Set[Timeout]
		events:		CORRECT.mapBy(pid => Set()),
		extensions: "",
	})

	/// Any non-initial step of the state machine
	action step = choreo::step(listener, noop_effect)

	/// Noop, required by choreo
	pure def noop_effect(env: GlobalContext, _: NoEffect): GlobalContext = env

	/// Listeners: main logic to produce transitions
	pure def listener(ctx: LocalContext) : Set[Transition] =
		Set(
			choreo::cue(ctx, start_rule, StartRound),
			choreo::cue(ctx, fresh_proposal_rule, upon_fresh_proposal),
			choreo::cue(ctx, re_proposal_rule, upon_re_proposal),
			choreo::cue(ctx, observation_rule, upon_observation),
			choreo::cue(ctx, quorum_any_rule, upon_quorum_any),
			choreo::cue(ctx, decision_rule, upon_decision),
			// WaitForValid() function logic
			choreo::cue(ctx, observation_rule_prepropose, upon_observation_prepropose),
			choreo::cue(ctx, expired_timeout_prepropose, OnTimeoutPrePropose),
			// Timeouts
			choreo::cue(ctx, expired_timeout_propose, OnTimeoutPropose),
			choreo::cue(ctx, expired_timeout_precommit, OnTimeoutPrecommit),
		).flatten()

	// ========= Listeners ========== //

	// In choreo parlance, defines the possible `upon` triggers given the set
	// of available messages and local process' state. Outputs the data needed
	// to trigger a state-transition, multiple outputs are usually possible.

	/// Start rule: process in NoStep round state, not modelled in the
	/// algorithm, should start round 0. Listener invokes StartRound(0).
	pure def start_rule(ctx: LocalContext) : Set[Round] = {
		val state = ctx.state
		if (state.step == NoStep and state.round == 0)
			Set(0)
		else Set() // listener not currently enabled
	}

	/// Get PROPOSAL messages from a Message set.
	pure def proposals(messages: Set[Message]): Set[ProposalMessage] =
		messages.filterMap(m => match m {
			| Proposal(proposal) => Some(proposal)
			| Precommit(precommit) => None
		})

	/// Get PRECOMMIT messages from a Message set.
	pure def precommits(messages: Set[Message]): Set[PrecommitMessage] =
		messages.filterMap(m => match m {
			| Proposal(proposal) => None
			| Precommit(precommit) => Some(precommit)
		})

	/// Fresh-proposal rule: process a PROPOSAL during propose round step.
	//
	// 18:	upon ⟨PROPOSAL, round_p, v,−1⟩ from proposer(round_p) while step_p = propose do
	pure def fresh_proposal_rule(ctx: LocalContext) : Set[ProposalMessage] = {
		val state = ctx.state
		if (state.step == ProposeStep)
			proposals(ctx.messages).filter(proposal => all {
				proposal.sender == proposer(proposal.round),
				proposal.round == state.round,
				proposal.valid_round == -1,
			})
		else Set() // listener not currently enabled
	}

	/// Re-proposal rule: process a PROPOSAL during propose round step,
	/// backed by a VALID_QUORUM of PRECOMMITs at a previous round vr.
	//
	// 24:	upon ⟨PROPOSAL, round_p, id(v), vr⟩ from proposer(round_p) with 0 ≤ vr < round_p AND
	// 		2f + 1 ⟨PRECOMMIT, vr, id(v)⟩ while step_p = propose do
	pure def re_proposal_rule(ctx: LocalContext) : Set[ProposalMessage] = {
		val state = ctx.state
		if (state.step == ProposeStep)
			proposals(ctx.messages).filter(proposal => all {
				proposal.sender == proposer(proposal.round),
				proposal.round == state.round,
				proposal.valid_round >= 0,
				proposal.valid_round < proposal.round,
				val supporting = precommits(ctx.messages).filter(
					precommit => all {
						precommit.round == proposal.valid_round,
						precommit.value == id(proposal.value)
					}
				)
				size(supporting) >= VALID_QUORUM,
			})
		else Set() // listener not currently enabled
	}

	/// Valid (round, value) backed by VALID_QUORUM of PRECOMMITs.
	type ValidCertificate = {
		round: Round,
		value: ValueId,
		precommits: Set[PrecommitMessage],
	}

	/// Return all available Valid certificates.
	pure def valid_certificates(ctx: LocalContext) : Set[ValidCertificate] = {
		val all_precommits = precommits(ctx.messages)
		val rounds = all_precommits.map(precommit => precommit.round)
		val values = all_precommits.map(precommit => precommit.value).exclude(Set(Nil))
		tuples(rounds, values).fold(Set(), (sets, entry) => {
			val (round, value) = entry
			val precommits = all_precommits.filter(precommit =>
				all {
					precommit.round == round,
					precommit.value == value,
				})
			val senders = precommits.map(m => m.sender)
			if (size(senders) >= VALID_QUORUM)
				sets.union(Set({
					round: round,
					value: value,
					precommits: precommits,
				}))
			else sets
		})
	}

	/// Observation rule: a valid becomes valid when it receives VALID_QUORUM
	/// PRECOMMITs in a round. Valid for the process's current round.
	//
	// 32:	upon 2f + 1 ⟨PRECOMMIT, round_p, id(v)⟩ with round_p > valid_p.round do
	pure def observation_rule(ctx: LocalContext) : Set[ValidCertificate] = {
		val state = ctx.state
		if (state.round > state.valid.round)
			valid_certificates(ctx).filter(
				certificate => certificate.round == state.round
			)
		else Set() // listener not currently enabled
	}

	/// Quorum any rule: upon a quorum of PRECOMMITs for a round r, schedule a
	/// timeout to join the subsequent round r + 1 if round r does not succeed.
	//
	// 34:	upon 4f + 1 ⟨PRECOMMIT, r, ∗⟩ for the first time with r ≥ round_p do
	pure def quorum_any_rule(ctx: LocalContext) : Set[Set[PrecommitMessage]] = {
		val state = ctx.state
		val potential_rounds = precommits(ctx.messages).
			map(precommit => precommit.round).
			filter(round => round >= state.round)
		potential_rounds.fold(Set(), (sets, round) =>
			if (ctx.events.contains({ step: PrecommitStep, round: round }))
				sets // not the "first time" for round, timeout already scheduled
			else if (round == state.round and size(observation_rule(ctx)) > 0)
				sets // the observation rule has priority over quorum any rule
			else
				val precommits_for_round = precommits(ctx.messages).
					filter(precommit => precommit.round == round)
				val senders = precommits_for_round.map(m => m.sender)
				if (size(senders) >= QUORUM)
					sets.union(Set(precommits_for_round))
				else sets // no QUORUM of precommits for round
		)
	}

	/// Decision requires a PROPOSAL and a QUORUM of PRECOMMIT messages.
	type DecisionParams = {
		proposal:	ProposalMessage,
		precommits: Set[PrecommitMessage],
	}

	/// Decision rule: upon a fresh PROPOSAL, carrying a full value `v` and
	/// with `vr = -1` and a QUORUM of same-round PRECOMMITs for `id(v)`.
	//
	// 36: 	upon ⟨PROPOSAL, r, v,−1⟩ from proposer(r) AND 4f + 1 ⟨PRECOMMIT, r′, id(v)⟩ do
	pure def decision_rule(ctx: LocalContext) : Set[DecisionParams] = {
		val state = ctx.state
		val fresh_proposals = proposals(ctx.messages).filter(
			proposal => proposal.valid_round == -1 and
				proposal.sender == proposer(proposal.round)
		)
		val potential_rounds = precommits(ctx.messages).
			map(precommit => precommit.round)
		tuples(fresh_proposals, potential_rounds).fold(Set(), (sets, entry) => {
			val (proposal, round) = entry
			val matching_precommits = precommits(ctx.messages).
				filter(precommit => all {
					precommit.round == round,
					precommit.value == id(proposal.value),
				})
			val senders = matching_precommits.map(m => m.sender)
			if (size(senders) >= QUORUM)
				sets.union(Set(
					{ proposal: proposal, precommits: matching_precommits }
				))
			else sets
		})
	}

	/// Observation rule pre-proposal: a value becomes valid when it receives
	/// 2f+1 PRECOMMITs in a round; any previous round can be valid here.
	//
	// 40: 			if 2f + 1 ⟨PRECOMMIT, r, id(v)⟩ with r > valid_p.round then
	// 41: 				valid_p ← (r, id(v))
	//
	// If the '(valid_p.round < round_p − 1)' condition of the pseudo-code
	// WaitForValid() method is observed, proceed with StartRound(round).
	pure def observation_rule_prepropose(ctx: LocalContext) : Set[ValidCertificate] = {
		val state = ctx.state
		val valid = state.valid
		if (state.step == PreProposeStep)
			valid_certificates(ctx).filter(
				certificate => certificate.round > valid.round
			)
		else Set() // listener not currently enabled
	}

	pure def expired_timeout_prepropose(ctx: LocalContext) : Set[Round] = {
		val state = ctx.state
		// Timeouts should expire when liveness is ensured past GST
		val liveness_guard = if (state.round >= GST_ROUND) all {
			observation_rule_prepropose(ctx).size() == 0,
		} else true // before GST, no liveness guard
		if (state.step == PreProposeStep and liveness_guard)
			ctx.events.filter(timeout => all {
				timeout.step == PreProposeStep,
				timeout.round == state.round,
			}).map(timeout => timeout.round)
		else Set() // listener not currently enabled
	}

	// 42:	function OnTimeoutPropose(round)
	// 43:		if round = round_p ∧ step_p = propose then
	pure def expired_timeout_propose(ctx: LocalContext) : Set[Round] = {
		val state = ctx.state
		// Timeouts should expire when liveness is ensured past GST
		val liveness_guard = if (state.round >= GST_ROUND) all {
			FAULTY.contains(proposer(state.round)),
			fresh_proposal_rule(ctx).size() == 0,
			re_proposal_rule(ctx).size() == 0,
		} else true // before GST, no liveness guard
		if (state.step == ProposeStep and liveness_guard)
			ctx.events.filter(timeout => all {
				timeout.step == ProposeStep,
				timeout.round == state.round,
			}).map(timeout => timeout.round)
		else Set() // listener not currently enabled
	}

	// 46:	function OnTimeoutPrecommit(round)
	// 47:		if round ≥ round_p ∧ decision_p = nil then
	pure def expired_timeout_precommit(ctx: LocalContext) : Set[Round] = {
		val state = ctx.state
		// Timeouts should expire when liveness is ensured past GST
		val liveness_guard = if (state.round >= GST_ROUND) all {
			decision_rule(ctx).size() == 0,
			observation_rule(ctx).size() == 0,
		} else true // before GST, no liveness guard
		if (state.decision == Nil and liveness_guard)
			ctx.events.filter(timeout => all {
				timeout.step == PrecommitStep,
				timeout.round >= state.round,
			}).map(timeout => timeout.round)
		else Set() // listener not currently enabled
	}

	// ========= Algorithm ========== //

	/// Produce a transition with unchanged state and no effect.
	pure def no_transition(state: LocalState) : Transition = {
		post_state: state,
		effects: Set(),
	}

	/// Implements: schedule OnTimeout<Step>(<round>) after timeout<Step>(<round>)
	pure def scheduleTimeout(step: Step, round: Round) : Set[Effect] =
		Set(choreo::TriggerEvent({step: step, round: round}))

	/// Update valid value and round, if new round and value allow for.
	pure def update_valid(state: LocalState, round: Round, value: ValueId) : LocalState = {
		val valid = state.valid
		if (round >= valid.round) {
			...state,
			valid: { round: round, value: value },
		} else {
			state
		}
	}

	/// Initialization of a process.
	//
	// 1: round_p := 0
	// 2: step_p ∈ {propose, precommit}
	// 3: decision_p := nil
	// 4: valid_p := (−1, nil)
	pure def upon_init(id: Process) : LocalState = {
		// Mandatory choreo field
		process_id: id,
		// Fast Tendermint state fields
		round: 0,
		step: NoStep,
		decision: Nil,
		valid: { round: -1, value: Nil },
	}

	/// Start a new round of consensus.
	//
	// 5: function StartRound(round)
	// 6: 	round_p ← round
	// 7: 	step_p ← propose
	// 8: 	if proposer(round_p) = p then
	// 9: 		if round_p > 0 then
	// 10: 			WaitForValid(timeoutPrecommit(round_p))
	// ...
	// 15: 		broadcast ⟨PROPOSAL, round_p, proposal, valid_p.round⟩
	// 16: 	else
	// 17: 		schedule OnTimeoutPropose(round_p) after timeoutPropose(round_p)
	pure def StartRound(ctx: LocalContext, round: Round) : Transition = {
		val state = {...ctx.state,
			round: round,
			step: ProposeStep
		}
		val transition = if (state.process_id == proposer(round)) {
			if (round > 0 and WaitForValid(state)) {
				// Models a blocking WaitForValid using a timeout
				// and the additional PreProposeStep round step.
				post_state: {...state,
					step: PreProposeStep
				},
				effects: scheduleTimeout(PreProposeStep, round),
			} else {
				// Models an immediate return of WaitForValid
				broadcast_proposal(state)
			}
		} else {
			post_state: state,
			effects: scheduleTimeout(ProposeStep, round),
		}
		val byzantine_effects = byzantine_messages_for_round(ctx, round).
			union(byzantine_messages_for_round(ctx, round + 1)).
				map(message => choreo::Broadcast(message))
		{...transition,
			effects: transition.effects.union(byzantine_effects),
		}
	}

	/// Broadcast a fresh proposal or re-broadcast the valid value.
	//
	// 11: 		if valid_p.value = nil then
	// 12: 			proposal ← getValue()
	// 13: 		else
	// 14: 			proposal ← valid_p.value
	// 15:		broadcast ⟨PROPOSAL, round_p, proposal, valid_p.round⟩
	pure def broadcast_proposal(state: LocalState): Transition = {
		val pid = state.process_id
		val valid = state.valid
		val proposal =
			if (valid.value == Nil) getValue(pid)
			else valid.value.unwrap()
		val msg =  Proposal({ sender: pid, round: state.round,
			value: proposal, valid_round: valid.round })
		{
			post_state: {...state,
				step: ProposeStep,
			},
			effects: Set(choreo::Broadcast(msg)),
		}
	}

	/// Broadcast a precommit for `id(v)` or `nil` and move to `precommit` step.
	pure def broadcast_precommit(state: LocalState, value: ValueId) : Transition = {
		val msg = Precommit({ sender: state.process_id, round: state.round, value: value })
		{
			post_state: {...state,
				step: PrecommitStep,
			},
			effects: Set(choreo::Broadcast(msg)),
		}
	}

	/// Fresh-proposal rule: process a PROPOSAL during propose round step.
	//
	// 18:	upon ⟨PROPOSAL, round_p, v,−1⟩from proposer(round_p) while step_p = propose do
	// 19:		if validate(v) ∧ (valid_p.round = −1 ∨ valid_p.value = id(v)) then
	// 20: 			broadcast ⟨PRECOMMIT, round_p, id(v)⟩
	// 21: 		else
	// 22: 			broadcast ⟨PRECOMMIT, round_p, nil⟩
	// 23: 		step_p ← precommit
	pure def upon_fresh_proposal(ctx: LocalContext, msg: ProposalMessage) : Transition = {
		val v = msg.value
		val state = ctx.state
		val valid = state.valid
		if (validate(v) and (valid.round == -1 or valid.value == id(v))) {
			broadcast_precommit(state, id(v))
		} else {
			broadcast_precommit(state, Nil)
		}
	}

	/// Re-proposal rule: process a PROPOSAL during propose round step,
	/// backed by a VALID_QUORUM of PRECOMMITs at a previous round vr.
	//
	// 24:	upon ⟨PROPOSAL, round_p, id(v), vr⟩ from proposer(round_p) with 0 ≤ vr < round_p AND
	// 		2f + 1 ⟨PRECOMMIT, vr, id(v)⟩ while step_p = propose do
	// 25: 		if valid_p.round ≤ vr ∨ valid_p.value = id(v) then
	// 26: 			if valid_p.round ≤ vr then
	// 27: 				valid_p ← (vr, id(v))
	// 28: 			broadcast ⟨PRECOMMIT, round_p, id(v)⟩
	// 29: 		else
	// 30: 			broadcast ⟨PRECOMMIT, round_p, nil⟩
	// 31: 		step_p ←precommit
	pure def upon_re_proposal(ctx: LocalContext, msg: ProposalMessage) : Transition = {
		val v = msg.value
		val vr = msg.valid_round
		val state = ctx.state
		val valid = state.valid
		if (valid.round <= vr or valid.value == id(v)) {
			val state_update_valid = update_valid(state, vr, id(v))
			broadcast_precommit(state_update_valid, id(v))
		} else {
			broadcast_precommit(state, Nil)
		}
	}

	/// The unique round of a set of PRECOMMIT messages.
	// Crashes if more than one round is found.
	pure def unique_round(msgs: Set[PrecommitMessage]) : Round =
		val rounds = msgs.map(message => message.round)
		if (rounds.size() == 1) rounds.fold(-1, (_, r) => r)
		else Map().get(-1)

	/// The unique ValueId of a set of PRECOMMIT messages.
	// Crashes if more than one value is found.
	pure def unique_value(msgs: Set[PrecommitMessage]) : ValueId =
		val values = msgs.map(message => message.value)
		if (values.size() == 1) values.fold(Nil, (_, v) => v)
		else Map().get(Nil)

	/// Observation rule: a valid becomes valid when it receives 2f+1
	/// PRECOMMITs in a round. Valid for the process's current round.
	//
	// 32:	upon 2f + 1 ⟨PRECOMMIT, round_p, id(v)⟩ with round_p > valid_p.round do
	// 33:		valid_p ← (round_p, id(v))
	pure def upon_observation(ctx: LocalContext, certificate: ValidCertificate) : Transition = {
		val state = ctx.state
		val valid = ctx.state.valid
		val validity_guard = all {
			certificate.round == state.round,
			certificate.value != Nil,
		}
		if (validity_guard and state.round > valid.round) {
			post_state: update_valid(state, certificate.round, certificate.value),
			effects: Set(),
		} else {
			no_transition(state)
		}
	}

	/// Quorum any rule: upon a quorum of PRECOMMITs for a round r, schedule a
	/// timeout to join the subsequent round r + 1 if round r does not succeed.
	//
	// 34:	upon 4f + 1 ⟨PRECOMMIT, r, ∗⟩ for the first time with r ≥ round_p do
	// 35:		schedule OnTimeoutPrecommit(r) after timeoutPrecommit(r)
	pure def upon_quorum_any(ctx: LocalContext, msgs: Set[PrecommitMessage]) : Transition = {
		post_state: ctx.state,
		effects: scheduleTimeout(PrecommitStep, unique_round(msgs)),
	}

	/// Decision rule: upon a fresh PROPOSAL, carrying a full value `v` and
	/// with `vr = -1` and a QUORUM of same-round PRECOMMITs for `id(v)`.
	//
	// 36: 	upon ⟨PROPOSAL, r, v,−1⟩ from proposer(r) AND 4f + 1 ⟨PRECOMMIT, r′, id(v)⟩ do
	// 37:		decision_p ← v
	pure def upon_decision(ctx: LocalContext, params: DecisionParams) : Transition = {
		val state = ctx.state
		val round = unique_round(params.precommits)
		val value = unique_value(params.precommits)
		val validity_guard = (params.proposal.valid_round == -1 and
			round >= 0 and value != Nil)
		if (validity_guard and state.decision == Nil) {
			val state_update_valid = update_valid(state, round, value)
			{
				post_state: {...state_update_valid,
					decision: Some(params.proposal.value),
				},
				effects: Set(),
			}
		} else { // Noop when state.decision is already set
			no_transition(state)
		}
	}

	/// Proposer waits for a timeout before proposing in the current round.
	/// During this period, the proposer is allowed to update its valid value.
	//
	// 38:	function WaitForValid(timeout)
	// 39:		while (valid_p.round < round_p − 1) ∧ !timeout.elapsed() do
	// 40: 			if 2f + 1 ⟨PRECOMMIT, r, id(v)⟩with r > valid_p.round then
	// 41: 				valid_p ← (r, id(v))
	//
	// Modeled in three parts:
	// 1. WaitForValid() checks whether the proposer should wait at all
	// 2. If so, a timeoutPrePropose(round) is scheduled and the process
	//    transitions to the introduced PreProposeStep meta round step.
	// 3. Once in the PreProposeStep round step, the process returns to the
	//    execution of StartRound(round), from line 11, in two scenarios:
	//    a. Once the scheduled timeoutPrePropose(round) expires, if the
	//       process is still in the PreProposeStep meta step;
	//    b. If the exit condition represented by WaitForValid() is observed
	//       when valid is updated by upon_observation_prepropose() function;
	// 4. The continuation of StartRound(round) consists of updating the round
	//    step to `propose` and broadcasting a proposal for the started round.

	/// Check whether the proposer should wait for a fresh valid value.
	pure def WaitForValid(state: LocalState): bool = {
		state.valid.round < state.round - 1
	}

	/// Upon expiration of timeoutPrePropose, if still in the PreProposeStep
	/// as the proposer of the round, then proceeed with the StartRound(round)
	/// operation from line 11, since WaitForValid() has returned.
	//
	// This modeled in the pseudo-code with the `!timeout.elapsed()` condition
	// of the while do loop that is the core of `WaitForValid(timeout)` method.
	pure def OnTimeoutPrePropose(ctx: LocalContext, round: Round) : Transition = {
		val state = ctx.state
		val validity_guard = (state.process_id == proposer(round) and
			state.step == PreProposeStep and state.round == round)
		if (validity_guard) {
			// Models a delayed return of WaitForValid.
			// Continues StartRound(round) from line 11.
			broadcast_proposal(state)
		} else {
			no_transition(state)
		}
	}

	/// Observation rule pre-proposal: a value becomes valid when it receives
	/// 2f+1 PRECOMMITs in a round; any previous round can be valid here.
	//
	// 40: 			if 2f + 1 ⟨PRECOMMIT, r, id(v)⟩ with r > valid_p.round then
	// 41: 				valid_p ← (r, id(v))
	//
	// If the '(valid_p.round < round_p − 1)' condition of the pseudo-code
	// WaitForValid() method is observed, proceed with StartRound(round).
	pure def upon_observation_prepropose(ctx: LocalContext, certificate: ValidCertificate) : Transition = {
		val state = ctx.state
		val valid = ctx.state.valid
		val round = certificate.round
		val validity_guard = all{
			state.step == PreProposeStep,
			round >= 0,
			round < state.round,
			certificate.value != Nil,
		}
		if (validity_guard and round > valid.round) {
			val state_update_valid = update_valid(state, round, certificate.value)
			if (round == state.round - 1) {
				// Models an early return of WaitForValid.
				// Continues StartRound(round) from line 11.
				broadcast_proposal(state_update_valid)
			} else {
				post_state: state_update_valid,
				effects: Set(),
			}
		} else {
			no_transition(state)
		}
	}

	/// Upon expiration of timeoutPropose(round), if still in the `propose`
	/// step, broadcast a PRECOMMIT for `nil` and move to `precommit` step.
	//
	// 42:	function OnTimeoutPropose(round)
	// 43:		if round = round_p ∧ step_p = propose then
	// 44: 			broadcast ⟨PRECOMMIT, round_p, nil⟩
	// 45: 			step_p ← precommit
	pure def OnTimeoutPropose(ctx: LocalContext, round: Round) : Transition = {
		val state = ctx.state
		if (state.round == round and state.step == ProposeStep) {
			broadcast_precommit(state, Nil)
		} else {
			no_transition(state)
		}
	}

	/// Upon expiration of timeoutPrecommit(round), if still in the `precommit`
	/// step, broadcast a PRECOMMIT for `nil` and move to `precommit` step.
	//
	// 46:	function OnTimeoutPrecommit(round)
	// 47:		if round ≥ round_p ∧ decision_p = nil then
	// 48:			StartRound(round + 1)
	pure def OnTimeoutPrecommit(ctx: LocalContext, round: Round) : Transition = {
		val state = ctx.state
		if (state.round == round and state.decision == Nil) {
			StartRound(ctx, round + 1)
		} else {
			no_transition(state)
		}
	}

	// ==== Byzantine behaviour ==== //
	// Byzantine processes are not modelled according to the algorithm.

	/// Messages from Byzantine processes for a given round.
	pure def byzantine_messages_for_round(ctx: LocalContext, round: Round) : Set[Message] = {
		val fresh_proposals = tuples(FAULTY, BYZ_VALUES).map(((pid, value)) =>
			Proposal({ sender: pid, round: round, value: value, valid_round: -1 })
		)
		// Check for VALID_QUORUMs in previous rounds
		val potential_precommits = precommits(ctx.messages).filter(precommit => all {
				precommit.round < round,
				precommit.value != Nil,
			})
		val potential_rounds = potential_precommits.map(precommit => precommit.round)
		val potential_values = potential_precommits.map(precommit => precommit.value)
		val valid_pairs = tuples(potential_rounds, potential_values).filter(
			((round, value)) => {
				val matching_precommits = potential_precommits.filter(precommit => all {
					precommit.round == round,
					precommit.value == value,
				})
				val senders = matching_precommits.map(m => m.sender)
				size(senders) >= VALID_QUORUM
		})
		val re_proposals = tuples(FAULTY, valid_pairs).map(((pid, pair)) =>
			val (vr, value) = pair
			Proposal({ sender: pid, round: round, value: value.unwrap(), valid_round: vr })
		)
		val valid_values = valid_pairs.map(pair => pair._2.unwrap())
		val precommits = tuples(FAULTY, BYZ_VALUES.union(valid_values)).
			map(((pid, value)) =>
				Precommit({ sender: pid, round: round, value: id(value) })
			)
		fresh_proposals.union(precommits).union(re_proposals)
	}

	// ========= Witnesses ========== //
	// Look for some specific characteristic on an execution.
	// Parameter `--witnesses` of `quint run` passes one or multiple of them.
	// If the witness is observed in any state of the execution, it is counted.

	val s = choreo::s
	val processes = s.system.values()

	/// A correct process has decided.
	val one_decided = processes.exists(state => state.decision != None)

	/// A correct processess have decided.
	val all_decided = processes.forall(state => state.decision != None)

	/// A correct processes reached a round.
	// Pass 'round_reached(1)' for example to `--witnesses`
	def round_reached(round: Round): bool = processes.exists(state => state.round >= round)

	/// All correct processes reached a round.
	def round_reached_all(round: Round): bool = processes.forall(state => state.round >= round)

	// ========= Invariants ========== //
	// Safety conditions, that cannot be violated at any point of the execution.
	// Pass `--invariant` with the invariant name to `quint run`.
	// Multiple `--invariant` parameters can be provided.

	/// Lemma 2: If 4f + 1 processes precommit for id(v) in round r (v can be
	/// decided at round r), then no correct process sets valid = (r′, id(w))
	/// for any id(w) != id(v) and r′ ≥ r.
	// This variant considers when the value v is decided in round r.
	// This core Lemma is the base for the ensuring Agreement.
	val lemma2 = tuples(processes, processes).forall(((decider, other)) =>
		match decider.decision {
			| None => true
			| Some(value) =>
				other.valid.value == Nil or
				other.valid.value == id(value) or
				// if valid.value != id(value), then valid.round < r
				other.valid.round < decider.round
		}
	)

	/// Agreement: no two correct processes decide differently.
	val agreement = tuples(processes, processes).forall(((p1, p2)) =>
		p1.decision == Nil or
		p2.decision == Nil or
		// Both have decided => decisions equal
		p1.decision == p2.decision
	)

	// ========= Constants ========== //
	// Defined by the importing module.

	/// Correct consensus processes
	const CORRECT: Set[Process]

	/// Expected maximum number of faults
	const FAULTS: int

	/// Faulty (Byzantine) processes: do not run state machine
	const FAULTY: Set[Process]

	/// Schedule of processes assigned as proposer(Round)
	const PROPOSERS: List[Process]

	/// Initial value of each correct process
	const VALUES: Process -> Value

	/// Values proposed by Byzantine processes
	const BYZ_VALUES: Set[Value]

	/// Round from which the system is synchronous and should be live
	const GST_ROUND: Round
}

module main {
	/// Main execution of Fast Tendermint protocol with N = 5F + 1
	// Byzantine proposers at rounds 0/2/4, honest on odd rounds.
	// Liveness guards prevent spurious timeouts after round 3.
	import fast_tendermint(
		CORRECT		= Set("p1", "p2", "p3", "p4", "p5"),
		FAULTS 		= 1,
		FAULTY 		= Set("p6"),
		PROPOSERS	= ["p6", "p1", "p6", "p2", "p6", "p3", "p4", "p5"],
		VALUES 		= Map("p1" -> "v1", "p2" -> "v2", "p3" -> "v3", "p4" -> "v4", "p5" -> "v5"),
		BYZ_VALUES	= Set("b1", "b2"),
		GST_ROUND	= 3
	).*
}

module live {
	/// Live execution of Fast Tendermint protocol with N = 5F + 1
	// Byzantine proposers at rounds 0/2/4, honest on odd rounds.
	// Liveness guards prevent spurious timeouts at any round.
	// Every process decides in 45 steps (`--max-steps 45`).
	import fast_tendermint(
		CORRECT		= Set("p1", "p2", "p3", "p4", "p5"),
		FAULTS 		= 1,
		FAULTY 		= Set("p6"),
		PROPOSERS	= ["p6", "p1", "p6", "p2", "p6", "p3", "p4", "p5"],
		VALUES 		= Map("p1" -> "v1", "p2" -> "v2", "p3" -> "v3", "p4" -> "v4", "p5" -> "v5"),
		BYZ_VALUES	= Set("b1", "b2"),
		GST_ROUND	= 0
	).*
}
