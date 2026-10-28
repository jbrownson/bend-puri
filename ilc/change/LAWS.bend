import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# How values change
# -----------------
# A Changes says how values change: values of type Value, by changes of
# type Delta, which `apply` applies. It is only the apply part of what the
# theory calls a change structure.

# LAW: Value is the type of the values.
law value:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Value(C.Changes{V, D, f}) == V : Data}

# LAW: Delta is the type of their changes.
law delta:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Delta(C.Changes{V, D, f}) == D : Data}

# LAW: Changes.apply applies a change by its function.
law changes_apply:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Changes.apply(C.Changes{V, D, f}) == f : D -> V -> V}

# Changes to any value
# --------------------
# A type supplies its edits, and how one applies, as a Changes ce.
# C.Change.of(ce) is the Change made of ce's edits. With Keep (a change
# that does nothing), Replace (a change from any value to any other) and
# Then (composition), a Change has the rest of a change structure.

# LAW: a Change of ce's edits is a Change of its values and edits.
law change_of:
  for -ce: C.Changes
  {C.Change.of(ce) == C.Change<C.Value(ce), C.Delta(ce)> : Data}

# LAW: keeping changes nothing.
law apply_keep:
  for ~ce: C.Changes
  for a: C.Value(ce)
  {C.apply(~ce, C.Keep{}, a) == a : C.Value(ce)}

# LAW: replacing gives the new value.
law apply_replace:
  for ~ce: C.Changes
  for x: C.Value(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Replace{x}, a) == x : C.Value(ce)}

# LAW: an edit is applied as ce says.
law apply_edit:
  for ~ce: C.Changes
  for e: C.Delta(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Edit{e}, a) == C.Changes.apply(ce)(e, a) : C.Value(ce)}

# LAW: one change then another applies the first, then the second.
law apply_then:
  for ~ce: C.Changes
  for p: C.Change.of(ce)
  for q: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Then{p, q}, a) == C.apply(~ce, q, C.apply(~ce, p, a)) : C.Value(ce)}

# LAW: Changes of ce's edits change ce's values, by C.apply.
law changes:
  for ~ce: C.Changes
  {C.changes(~ce) == C.Changes{C.Value(ce), C.Change.of(ce), d => a => C.apply(~ce, d, a)} : C.Changes}

# It follows that:

# LAW: keeping first does nothing.
law then_keep_left:
  for ~ce: C.Changes
  for q: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Then{C.Keep{}, q}, a) == C.apply(~ce, q, a) : C.Value(ce)}

# LAW: keeping last does nothing.
law then_keep_right:
  for ~ce: C.Changes
  for p: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Then{p, C.Keep{}}, a) == C.apply(~ce, p, a) : C.Value(ce)}

# LAW: grouping doesn't matter.
law then_assoc:
  for ~ce: C.Changes
  for p: C.Change.of(ce)
  for q: C.Change.of(ce)
  for r: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.Then{C.Then{p, q}, r}, a) == C.apply(~ce, C.Then{p, C.Then{q, r}}, a) : C.Value(ce)}

# Mapping a change
# ----------------
# C.map(fa, fe, d) maps d's new values by fa and its edits by fe.

# LAW: mapping keeping keeps.
law map_keep:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Keep{}) == C.Keep{} : C.Change<B, EB>}

# LAW: mapping a replacement maps the new value.
law map_replace:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for x: A
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Replace{x}) == C.Replace{fa(x)} : C.Change<B, EB>}

# LAW: mapping an edit maps the edit.
law map_edit:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for e: EA
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Edit{e}) == C.Edit{fe(e)} : C.Change<B, EB>}

# LAW: mapping one change then another maps each, in the same order.
law map_then:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for p: C.Change<A, EA>
  for q: C.Change<A, EA>
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Then{p, q}) == C.Then{C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, p), C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, q)} : C.Change<B, EB>}

# Incremental functions
# ---------------------
# An Inc<ca, cb> is a function from values that change as ca says to
# values that change as cb says, with its derivative: from a value and its
# change, the change to the function's result.

# LAW: Inc.f gives the function.
law inc_f:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Delta(ca) -> C.Delta(cb)
  {C.Inc.f(ca, cb, C.Inc{f, df}) == f : C.Value(ca) -> C.Value(cb)}

# LAW: Inc.df gives the derivative.
law inc_df:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Delta(ca) -> C.Delta(cb)
  {C.Inc.df(ca, cb, C.Inc{f, df}) == df : C.Value(ca) -> C.Delta(ca) -> C.Delta(cb)}

# LAW: an Inc is correct when applying its derivative's change to f(a)
# gives f of the changed value.
law inc_ok:
  for -ca: C.Changes
  for -cb: C.Changes
  for -g: C.Inc<ca, cb>
  {C.Inc.ok(ca, cb, g) == (@a: C.Value(ca) -> @d: C.Delta(ca) -> {C.Changes.apply(cb)(C.Inc.df(ca, cb, g)(a, d), C.Inc.f(ca, cb, g)(a)) == C.Inc.f(ca, cb, g)(C.Changes.apply(ca)(d, a)) : C.Value(cb)}) : Type}

# Lifting
# -------
# lift turns g, whose derivative handles one edit as ca says, into an Inc
# whose derivative handles any change.

# LAW: lift(g) has g's function, and lift.df for its derivative.
law lift:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  {C.lift(~ca, ~cb, ~g) == C.Inc{C.Inc.f(ca, C.changes(~cb), g), a => d => C.lift.df(~ca, ~cb, ~g, d, a)} : C.Inc<C.changes(~ca), C.changes(~cb)>}

# LAW: keeping the input keeps the result.
law lift_keep:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.Keep{}, a) == C.Keep{} : C.Change.of(cb)}

# LAW: replacing the input replaces the result, with f of the new value.
law lift_replace:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  for x: C.Value(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.Replace{x}, a) == C.Replace{C.Inc.f(ca, C.changes(~cb), g)(x)} : C.Change.of(cb)}

# LAW: one edit gives g's change.
law lift_edit:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  for e: C.Delta(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.Edit{e}, a) == C.Inc.df(ca, C.changes(~cb), g)(a, e) : C.Change.of(cb)}

# LAW: one change then another lifts the second from the value the first
# produced.
law lift_then:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  for p: C.Change.of(ca)
  for q: C.Change.of(ca)
  for +a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.Then{p, q}, a) == C.Then{C.lift.df(~ca, ~cb, ~g, p, a), C.lift.df(~ca, ~cb, ~g, q, C.apply(~ca, p, a))} : C.Change.of(cb)}

# It follows that:

# LAW: lift(g) is correct for every change, if g is correct for every
# single edit.
law lift_ok:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~g: C.Inc<ca, C.changes(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.changes(~cb), g)
  C.Inc.ok(C.changes(~ca), C.changes(~cb), C.lift(~ca, ~cb, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the changed value.
law recompute:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~f: C.Value(ca) -> C.Value(cb)
  {C.recompute(~ca, ~cb, ~f) == C.Inc{f, a => d => C.Replace{f(C.Changes.apply(ca)(d, a))}} : C.Inc<ca, C.changes(~cb)>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~ca: C.Changes
  for ~cb: C.Changes
  for ~f: C.Value(ca) -> C.Value(cb)
  C.Inc.ok(ca, C.changes(~cb), C.recompute(~ca, ~cb, ~f))
