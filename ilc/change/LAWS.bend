import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# How values are edited
# ---------------------
# Edits say how values are edited: values of type Value, by edits of type
# Edit, which `apply` applies. They are a change structure when one edit
# gets from any value to any other; C.complete makes any edits into one.

# LAW: Value is the type of the values.
law value:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Value(C.Edits{V, D, f}) == V : Data}

# LAW: Edit is the type of their edits.
law edit_type:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Edit(C.Edits{V, D, f}) == D : Data}

# LAW: Edits.apply applies an edit by its function.
law edits_apply:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Edits.apply(C.Edits{V, D, f}) == f : D -> V -> V}

# LAW: edits are a change structure when one edit gets from any value to
# any other.
law change_structure:
  for -ce: C.Edits
  {C.ChangeStructure(ce) == (@a: C.Value(ce) -> @b: C.Value(ce) -> &d: C.Edit(ce) -> {C.Edits.apply(ce)(d, a) == b : C.Value(ce)}) : Type}

# Changes to any value
# --------------------
# A type supplies its edits, ce. A Change of ce's edits, C.Change.of(ce),
# is a run of edits after an optional new value to start from, and
# C.complete(ce) is the change structure they make.

# LAW: a Change of ce's edits is a Change of its values and edits.
law change_of:
  for -ce: C.Edits
  {C.Change.of(ce) == C.Change<C.Value(ce), C.Edit(ce)> : Data}

# LAW: a change with no new value and no edits changes nothing.
law apply_nil:
  for ~ce: C.Edits
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{None{}, Nil{}}, a) == a : C.Value(ce)}

# LAW: a new value replaces the old one, and the edits follow.
law apply_start:
  for ~ce: C.Edits
  for x: C.Value(ce)
  for es: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{Some{x}, es}, a) == C.apply(~ce, C.Change{None{}, es}, x) : C.Value(ce)}

# LAW: the edits apply in order, as ce says.
law apply_con:
  for ~ce: C.Edits
  for e: C.Edit(ce)
  for es: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{None{}, e <> es}, a) == C.apply(~ce, C.Change{None{}, es}, C.Edits.apply(ce)(e, a)) : C.Value(ce)}

# LAW: keep has no new value and no edits.
law keep:
  for -ce: C.Edits
  {C.keep(ce) == C.Change{None{}, Nil{}} : C.Change.of(ce)}

# LAW: replace(x) has x as its new value, and no edits.
law replace:
  for -ce: C.Edits
  for x: C.Value(ce)
  {C.replace(ce, x) == C.Change{Some{x}, Nil{}} : C.Change.of(ce)}

# LAW: edit(e) is the single edit e.
law edit:
  for -ce: C.Edits
  for e: C.Edit(ce)
  {C.edit(ce, e) == C.Change{None{}, [e]} : C.Change.of(ce)}

# LAW: p then a change that starts over is that change.
law then_start:
  for -ce: C.Edits
  for p: C.Change.of(ce)
  for y: C.Value(ce)
  for es: List<&2, C.Edit(ce)>
  {C.then(ce, p, C.Change{Some{y}, es}) == C.Change{Some{y}, es} : C.Change.of(ce)}

# LAW: p then a change that doesn't start over runs its edits after p's.
law then_edits:
  for -ce: C.Edits
  for s: Maybe<&2, C.Value(ce)>
  for ps: List<&2, C.Edit(ce)>
  for qs: List<&2, C.Edit(ce)>
  {C.then(ce, C.Change{s, ps}, C.Change{None{}, qs}) == C.Change{s, List.append(&2, C.Edit(ce), ps, qs)} : C.Change.of(ce)}

# LAW: Changes of ce's edits change ce's values by C.apply.
law complete:
  for ~ce: C.Edits
  {C.complete(~ce) == C.Edits{C.Value(ce), C.Change.of(ce), d => a => C.apply(~ce, d, a)} : C.Edits}

# LAW: values that change only as a whole have no edits of their own.
law whole:
  for ~A: Data
  {C.whole(~A) == C.Edits{A, Empty, e => a => Empty.absurd(A, e)} : C.Edits}

# It follows that:

# LAW: keeping changes nothing.
law apply_keep:
  for ~ce: C.Edits
  for a: C.Value(ce)
  {C.apply(~ce, C.keep(ce), a) == a : C.Value(ce)}

# LAW: replacing gives the new value.
law apply_replace:
  for ~ce: C.Edits
  for x: C.Value(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.replace(ce, x), a) == x : C.Value(ce)}

# LAW: completed edits are a change structure: from any value, replacing
# gets to any other.
law complete_change_structure:
  for ~ce: C.Edits
  C.ChangeStructure(C.complete(~ce))

# LAW: an edit is applied as ce says.
law apply_edit:
  for ~ce: C.Edits
  for e: C.Edit(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.edit(ce, e), a) == C.Edits.apply(ce)(e, a) : C.Value(ce)}

# LAW: p then q applies p, then q.
law apply_then:
  for ~ce: C.Edits
  for p: C.Change.of(ce)
  for q: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.then(ce, p, q), a) == C.apply(~ce, q, C.apply(~ce, p, a)) : C.Value(ce)}

# LAW: keeping first is the same change.
law then_keep_left:
  for -ce: C.Edits
  for q: C.Change.of(ce)
  {C.then(ce, C.keep(ce), q) == q : C.Change.of(ce)}

# LAW: keeping last is the same change.
law then_keep_right:
  for -ce: C.Edits
  for p: C.Change.of(ce)
  {C.then(ce, p, C.keep(ce)) == p : C.Change.of(ce)}

# LAW: grouping doesn't matter.
law then_assoc:
  for -ce: C.Edits
  for p: C.Change.of(ce)
  for q: C.Change.of(ce)
  for r: C.Change.of(ce)
  {C.then(ce, C.then(ce, p, q), r) == C.then(ce, p, C.then(ce, q, r)) : C.Change.of(ce)}

# Mapping a change
# ----------------
# C.map(fa, fe, d) maps d's new value by fa and its edits by fe.

# LAW: mapping a change maps its new value and each of its edits.
law map:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for s: Maybe<&2, A>
  for es: List<&2, EA>
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Change{s, es}) == C.Change{C.map.start(~A, ~B, ~fa, s), C.map.edits(~EA, ~EB, ~fe, es)} : C.Change<B, EB>}

# LAW: no new value maps to no new value.
law map_start_none:
  for ~A: Data
  for ~B: Data
  for ~fa: A -> B
  {C.map.start(~A, ~B, ~fa, None{}) == None{} : Maybe<&2, B>}

# LAW: a new value maps by fa.
law map_start_some:
  for ~A: Data
  for ~B: Data
  for ~fa: A -> B
  for x: A
  {C.map.start(~A, ~B, ~fa, Some{x}) == Some{fa(x)} : Maybe<&2, B>}

# LAW: no edits map to no edits.
law map_edits_nil:
  for ~EA: Data
  for ~EB: Data
  for ~fe: EA -> EB
  {C.map.edits(~EA, ~EB, ~fe, Nil{}) == Nil{} : List<&2, EB>}

# LAW: each edit maps by fe, in order.
law map_edits_con:
  for ~EA: Data
  for ~EB: Data
  for ~fe: EA -> EB
  for e: EA
  for es: List<&2, EA>
  {C.map.edits(~EA, ~EB, ~fe, e <> es) == fe(e) <> C.map.edits(~EA, ~EB, ~fe, es) : List<&2, EB>}

# Incremental functions
# ---------------------
# An Inc<ca, cb> is a function from values that change as ca says to
# values that change as cb says, with its derivative: from a value and its
# change, the change to the function's result.

# LAW: Inc.f gives the function.
law inc_f:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)
  {C.Inc.f(ca, cb, C.Inc{f, df}) == f : C.Value(ca) -> C.Value(cb)}

# LAW: Inc.df gives the derivative.
law inc_df:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)
  {C.Inc.df(ca, cb, C.Inc{f, df}) == df : C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)}

# LAW: an Inc is correct when applying its derivative's change to f(a)
# gives f of the changed value.
law inc_ok:
  for -ca: C.Edits
  for -cb: C.Edits
  for -g: C.Inc<ca, cb>
  {C.Inc.ok(ca, cb, g) == (@a: C.Value(ca) -> @d: C.Edit(ca) -> {C.Edits.apply(cb)(C.Inc.df(ca, cb, g)(a, d), C.Inc.f(ca, cb, g)(a)) == C.Inc.f(ca, cb, g)(C.Edits.apply(ca)(d, a)) : C.Value(cb)}) : Type}

# Lifting
# -------
# lift turns g, whose derivative handles one edit as ca says, into an Inc
# whose derivative handles any change.

# LAW: lift(g) has g's function, and lift.df for its derivative.
law lift:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  {C.lift(~ca, ~cb, ~g) == C.Inc{C.Inc.f(ca, C.complete(~cb), g), a => d => C.lift.df(~ca, ~cb, ~g, d, a)} : C.Inc<C.complete(~ca), C.complete(~cb)>}

# LAW: keeping the input keeps the result.
law lift_keep:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.keep(ca), a) == C.keep(cb) : C.Change.of(cb)}

# LAW: replacing the input replaces the result, with f of the new value.
law lift_replace:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  for x: C.Value(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.replace(ca, x), a) == C.replace(cb, C.Inc.f(ca, C.complete(~cb), g)(x)) : C.Change.of(cb)}

# LAW: one edit gives g's change.
law lift_edit:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  for e: C.Edit(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.edit(ca, e), a) == C.Inc.df(ca, C.complete(~cb), g)(a, e) : C.Change.of(cb)}

# LAW: p then q lifts q from the value p produced.
law lift_then:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  for p: C.Change.of(ca)
  for q: C.Change.of(ca)
  for +a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.then(ca, p, q), a) == C.then(cb, C.lift.df(~ca, ~cb, ~g, p, a), C.lift.df(~ca, ~cb, ~g, q, C.apply(~ca, p, a))) : C.Change.of(cb)}

# It follows that:

# LAW: lift(g) is correct for every change, if g is correct for every
# single edit.
law lift_ok:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~g: C.Inc<ca, C.complete(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.complete(~cb), g)
  C.Inc.ok(C.complete(~ca), C.complete(~cb), C.lift(~ca, ~cb, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the changed value.
law recompute:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~f: C.Value(ca) -> C.Value(cb)
  {C.recompute(~ca, ~cb, ~f) == C.Inc{f, a => d => C.replace(cb, f(C.Edits.apply(ca)(d, a)))} : C.Inc<ca, C.complete(~cb)>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~ca: C.Edits
  for ~cb: C.Edits
  for ~f: C.Value(ca) -> C.Value(cb)
  C.Inc.ok(ca, C.complete(~cb), C.recompute(~ca, ~cb, ~f))
