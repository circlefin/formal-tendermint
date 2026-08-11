// -*- mode: Bluespec; -*-

/**
 * Choreo: Choreograph distributed protocols in Quint
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 *
 * Downloaded from https://github.com/quint-co/choreo.
 *
 * Adapted for broadcast-only protocols, which simplifies the model: a single
 * message queue for all processes, instead of a per-process message queue.
 */
module choreo_broadcast {

  import basicSpells.*

  type LocalState[process_id, ext] = {
    process_id: process_id
    | ext
  }

  type Transition[p, s, m, e, ce] = {
    post_state: LocalState[p, s],
    effects: Set[Effect[m, e, ce]],
  }

  type GlobalContext[p, s, m, e, ext] = {
    system: p -> LocalState[p, s],
    messages: Set[m],
    events: p -> Set[e],
    extensions: ext
  }

  type LocalContext[p, s, m, e, ext] = {
    state: LocalState[p, s],
    messages: Set[m],
    events: Set[e],
    extensions: ext
  }

  // This is the message routing to the # handler
  type Listener[p, s, m, e, ce, ext] =
    (LocalContext[p, s, m, e, ext]) => Set[Transition[p, s, m, e, ce]]

  type DeterministicListener[p, s, m, e, ce, ext] =
    (LocalContext[p, s, m, e, ext]) => Transition[p, s, m, e, ce]

  // Only needed for micro_step
  type Input[m, e] = Message(m) | Event(e)

  // Only needed for micro_step
  type MicroListener[p, s, m, e, ce, ext] =
    (LocalContext[p, s, m, e, ext], Input[m, e]) => Set[Transition[p, s, m, e, ce]]

  type EffectProcessor[p, s, m, e, ce, ext] =
    (GlobalContext[p, s, m, e, ext], ce) => GlobalContext[p, s, m, e, ext]

  type Effect[m, e, ce] =
    | Broadcast(m)
    | TriggerEvent(e)
    | CustomEffect(ce)

  /// A displayer is a function that takes a global context and returns a displayable representation of it.
  /// This is used to visualize the state of the system for debugging or monitoring purposes.
  /// After type instantiation, it should have the following signature:
  /// ```
  /// (Environment) => Display
  /// ```
  /// The display type can be anything.
  type Displayer[p, s, m, e, ext, d] = (GlobalContext[p, s, m, e, ext]) => d

  pure def apply_effect(
    env: GlobalContext[p, s, m, e, ext],
    v: p,
    tr: Transition[p, s, m, e, ce],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, ext]
  ): GlobalContext[p, s, m, e, ext] = {
    val env1 = { ...env, system: env.system.setBy(v, s => tr.post_state) }

    tr.effects.fold(env1, (e, effect) => {
      match effect {
        | Broadcast(m) => {
          { ...e, messages: e.messages.setAdd(m) }
        }
        | TriggerEvent(ev) => {
          { ...e, events: e.events.setBy(v, b => b.setAdd(ev)) }
        }
        | CustomEffect(ex) => {
          apply_custom_effect(e, ex)
        }
      }
    })
  }

  const processes: Set[p]
  var s: GlobalContext[p, s, m, e, ext]
  var display: d

  pure def initialize(x: a, f: Option[(a) => Set[b]]): Set[b] = {
    match f {
      | Some(fun) => fun(x)
      | None => Set()
    }
  }

  pure def convert_context(
    env: GlobalContext[p, s, m, e, ext],
    v: p
  ): LocalContext[p, s, m, e, ext] = {
    {
      state: env.system.get(v),
      messages: env.messages,
      events: env.events.get(v),
      extensions: env.extensions
    }
  }

  action process_transitions(
    v: p,
    transitions: Set[Transition[p, s, m, e, ce]],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions],
  ): bool =
    nondet transition = oneOf(transitions)
    val post_env = apply_effect(s, v, transition, apply_custom_effect)
    s' = post_env

  action process_transitions_with_displayer(
    v: p,
    transitions: Set[Transition[p, s, m, e, ce]],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions],
    displayer: Displayer[p, s, m, e, extensions, d],
  ): bool =
    nondet transition = oneOf(transitions)
    val post_env = apply_effect(s, v, transition, apply_custom_effect)
    all {
      s' = post_env,
      display' = displayer(post_env),
    }

  action init(ctx: GlobalContext[p, s, m , e, ext]): bool = {
    s' = ctx
  }

  action init_with_displayer(
    ctx: GlobalContext[p, s, m , e, ext],
    displayer: Displayer[p, s, m, e, extensions, d],
  ): bool = all {
    s' = ctx,
    display' = displayer(ctx)
  }

  action step(
    listener: Listener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions]
  ): bool = {
    nondet v = oneOf(processes)
    val input = convert_context(s, v)
    val transitions = listener(input).filter(t => t.effects.size() > 0 or t.post_state != input.state)
    process_transitions(v, transitions, apply_custom_effect)
  }

  action step_with_displayer(
    listener: Listener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions],
    displayer: Displayer[p, s, m, e, extensions, d]
  ): bool = {
    nondet v = oneOf(processes)
    val input = convert_context(s, v)
    val transitions = listener(input).filter(t => t.effects.size() > 0 or t.post_state != input.state)
    process_transitions_with_displayer(v, transitions, apply_custom_effect, displayer)
  }

  action micro_step(
    listener: MicroListener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions]
  ): bool = {
    nondet process = processes.oneOf()
    val ctx = convert_context(s, process)
    any {
      nondet msg = s.messages.oneOf()
      val transitions = listener(ctx, Message(msg))
      process_transitions(process, transitions, apply_custom_effect),

      nondet event = s.events.get(process).oneOf()
      val transitions = listener(ctx, Event(event))
      process_transitions(process, transitions, apply_custom_effect),
    }
  }

  action step_with(
    v: p,
    listener: Listener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions]
  ): bool = {
    val input = convert_context(s, v)
    val transitions = listener(input).filter(t => t.effects.size() > 0 or t.post_state != input.state)
    process_transitions(v, transitions, apply_custom_effect)
  }

  action step_deterministic(
    v: p,
    listener: DeterministicListener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions]
  ): bool = {
    val input = convert_context(s, v)
    val transitions = Set(listener(input)).filter(t => t.effects.size() > 0 or t.post_state != input.state)
    process_transitions(v, transitions, apply_custom_effect)
  }

  action step_with_filter(
    v: p,
    listener: Listener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions],
    f: (Transition[p, s, m, e, ce]) => bool
  ): bool = {
    val input = convert_context(s, v)
    val transitions = listener(input).filter(t => t.effects.size() > 0 or t.post_state != input.state).filter(f)
    process_transitions(v, transitions, apply_custom_effect)
  }

  action step_with_messages(
    v: p,
    listener: Listener[p, s, m, e, ce, extensions],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, extensions],
    f: Set[m] => Set[m]
  ): bool = {
    val input = convert_context(s, v)
    val input1 = { ...input, messages: f(input.messages) }
    val transitions = listener(input1).filter(t => t.effects.size() > 0 or t.post_state != input.state)
    process_transitions(v, transitions, apply_custom_effect)
  }

  // In a broadcast-only setting, all processes share a single message set,
  // so losing messages affects everyone uniformly. No process parameter.
  action lose_messages(f: Set[m] => Set[m]): bool = {
    val msgs = s.messages
    val new_msgs = msgs.exclude(f(msgs))
    all {
      s' = { ...s, messages: new_msgs }
    }
  }

  pure def cue(
    ctx: LocalContext[p, s, m, e, ext],
    listen_fn: (LocalContext[p, s, m, e, ext]) => Set[r],
    upon_fn: (LocalContext[p, s, m, e, ext], r) => Transition[p, s, m, e, ce]
  ): Set[Transition[p, s, m, e, ce]] = {
    val params = listen_fn(ctx)
    params.map(param => upon_fn(ctx, param))
  }

  type CueResult[p, s, m, e, ext, r] = CueOk({ ctx: LocalContext[p, s, m, e, ext], params: r }) | NoCue

  def with_cue(
    process: p,
    listen_fn: (LocalContext[p, s, m, e, ext]) => Set[r],
    params: r
  ): CueResult[p, s, m, e, ext, r] = {
    val ctx = convert_context(s, process)
    val valid_params = listen_fn(ctx)
    val is_valid = valid_params.contains(params)
    if (is_valid)
      CueOk({ ctx: ctx, params: params })
    else
      NoCue
  }

  action perform(
    cue_result: CueResult[p, s, m, e, ext, r],
    upon_fn: (LocalContext[p, s, m, e, ext], r) => Transition[p, s, m, e, ce],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, ext],
  ): bool = {
    match cue_result {
      | CueOk(cue) => process_transitions(cue.ctx.state.process_id, Set(upon_fn(cue.ctx, cue.params)), apply_custom_effect)
      | NoCue => all { false, s' = s }
    }
  }

  action perform_with_displayer(
    cue_result: CueResult[p, s, m, e, ext, r],
    upon_fn: (LocalContext[p, s, m, e, ext], r) => Transition[p, s, m, e, ce],
    apply_custom_effect: EffectProcessor[p, s, m, e, ce, ext],
    displayer: Displayer[p, s, m, e, extensions, d],
  ): bool = {
    match cue_result {
      | CueOk(cue) => process_transitions_with_displayer(cue.ctx.state.process_id, Set(upon_fn(cue.ctx, cue.params)), apply_custom_effect, displayer)
      | NoCue => all { false, s' = s, display' = display }
    }
  }
}

// Useful helpers
module basicSpells {

  /// Option type, which may hold some value or none
  type Option[a] = Some(a) | None

  pure def unwrap(value: Option[a]): a = {
    match value {
      | None => Map().get(value)
      | Some(x) => x
    }
  }

  /// Adds an element to a set.
  pure def setAdd(s: Set[a], elem: a): Set[a] = {
    s.union(Set(elem))
  }

  pure def filterMap(s: Set[a], f: (a) => Option[b]): Set[b] = {
    s.fold(Set(), (acc, e) => {
      match f(e) {
        | Some(x) => acc.union(Set(x))
        | None => acc
      }
    })
  }

  /// Get the set of values of a map.
  ///
  /// - @param map a map from type a to type b
  /// - @returns the set of all values in the map
  pure def values(m: a -> b): Set[b] = {
    m.keys().map(k => m.get(k))
  }

}
