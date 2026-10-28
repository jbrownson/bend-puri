import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# How values are edited
# ---------------------
# An edit structure says how values are edited: values of type Value, by
# edits of type Edit, which `apply` applies. A change structure is an edit
# structure with the proof that one edit gets from any value to any other;
# C.complete makes one from any edit structure.

# LAW: Value is the type of the values.
law value:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Value(C.EditStructure{V, D, f}) == V : Data}

# LAW: Edit is the type of their edits.
law edit_type:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.Edit(C.EditStructure{V, D, f}) == D : Data}

# LAW: EditStructure.apply applies an edit by its function.
law structure_apply:
  for ~V: Data
  for ~D: Data
  for ~f: D -> V -> V
  {C.EditStructure.apply(C.EditStructure{V, D, f}) == f : D -> V -> V}

# LAW: an edit structure reaches when one edit gets from any value to any
# other.
law reaches:
  for -ce: C.EditStructure
  {C.reaches(ce) == (@a: C.Value(ce) -> @b: C.Value(ce) -> &d: C.Edit(ce) -> {C.EditStructure.apply(ce)(d, a) == b : C.Value(ce)}) : Type}

# LAW: a change structure's edit structure is the one it was made from.
law change_structure:
  for ~s: C.EditStructure
  for r: C.reaches(s)
  {C.ChangeStructure.structure(C.ChangeStructure{s, r}) == s : C.EditStructure}

# Changes to any value
# --------------------
# A type supplies its edits, ce. A Change of ce's edits, C.Change.of(ce),
# is a run of edits after an optional new value to start from.
# C.changes(ce) is the edit structure they make, and C.complete(ce) the
# change structure.

# LAW: a Change of ce's edits is a Change of its values and edits.
law change_of:
  for -ce: C.EditStructure
  {C.Change.of(ce) == C.Change<C.Value(ce), C.Edit(ce)> : Data}

# LAW: a change with no new value and no edits changes nothing.
law apply_nil:
  for ~ce: C.EditStructure
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{None{}, Nil{}}, a) == a : C.Value(ce)}

# LAW: a new value replaces the old one, and the edits follow.
law apply_start:
  for ~ce: C.EditStructure
  for x: C.Value(ce)
  for es: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{Some{x}, es}, a) == C.apply(~ce, C.Change{None{}, es}, x) : C.Value(ce)}

# LAW: the edits apply in order, as ce says.
law apply_con:
  for ~ce: C.EditStructure
  for e: C.Edit(ce)
  for es: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.apply(~ce, C.Change{None{}, e <> es}, a) == C.apply(~ce, C.Change{None{}, es}, C.EditStructure.apply(ce)(e, a)) : C.Value(ce)}

# LAW: keep has no new value and no edits.
law keep:
  for -ce: C.EditStructure
  {C.keep(ce) == C.Change{None{}, Nil{}} : C.Change.of(ce)}

# LAW: replace(x) has x as its new value, and no edits.
law replace:
  for -ce: C.EditStructure
  for x: C.Value(ce)
  {C.replace(ce, x) == C.Change{Some{x}, Nil{}} : C.Change.of(ce)}

# LAW: edit(e) is the single edit e.
law edit:
  for -ce: C.EditStructure
  for e: C.Edit(ce)
  {C.edit(ce, e) == C.Change{None{}, [e]} : C.Change.of(ce)}

# LAW: p then a change that starts over is that change.
law then_start:
  for -ce: C.EditStructure
  for p: C.Change.of(ce)
  for y: C.Value(ce)
  for es: List<&2, C.Edit(ce)>
  {C.then(ce, p, C.Change{Some{y}, es}) == C.Change{Some{y}, es} : C.Change.of(ce)}

# LAW: p then a change that doesn't start over runs its edits after p's.
law then_edits:
  for -ce: C.EditStructure
  for s: Maybe<&2, C.Value(ce)>
  for ps: List<&2, C.Edit(ce)>
  for qs: List<&2, C.Edit(ce)>
  {C.then(ce, C.Change{s, ps}, C.Change{None{}, qs}) == C.Change{s, List.append(&2, C.Edit(ce), ps, qs)} : C.Change.of(ce)}

# LAW: Changes of ce's edits change ce's values by C.apply.
law changes:
  for ~ce: C.EditStructure
  {C.changes(~ce) == C.EditStructure{C.Value(ce), C.Change.of(ce), d => a => C.apply(~ce, d, a)} : C.EditStructure}

# LAW: completing ce gives the change structure of its Changes.
law complete:
  for ~ce: C.EditStructure
  {C.ChangeStructure.structure(C.complete(~ce)) == C.changes(~ce) : C.EditStructure}

# LAW: values that change only as a whole have no edits of their own.
law whole:
  for ~A: Data
  {C.whole(~A) == C.EditStructure{A, Empty, e => a => Empty.absurd(A, e)} : C.EditStructure}

# It follows that:

# LAW: keeping changes nothing.
law apply_keep:
  for ~ce: C.EditStructure
  for a: C.Value(ce)
  {C.apply(~ce, C.keep(ce), a) == a : C.Value(ce)}

# LAW: replacing gives the new value.
law apply_replace:
  for ~ce: C.EditStructure
  for x: C.Value(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.replace(ce, x), a) == x : C.Value(ce)}

# LAW: an edit is applied as ce says.
law apply_edit:
  for ~ce: C.EditStructure
  for e: C.Edit(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.edit(ce, e), a) == C.EditStructure.apply(ce)(e, a) : C.Value(ce)}

# LAW: p then q applies p, then q.
law apply_then:
  for ~ce: C.EditStructure
  for p: C.Change.of(ce)
  for q: C.Change.of(ce)
  for a: C.Value(ce)
  {C.apply(~ce, C.then(ce, p, q), a) == C.apply(~ce, q, C.apply(~ce, p, a)) : C.Value(ce)}

# LAW: keeping first is the same change.
law then_keep_left:
  for -ce: C.EditStructure
  for q: C.Change.of(ce)
  {C.then(ce, C.keep(ce), q) == q : C.Change.of(ce)}

# LAW: keeping last is the same change.
law then_keep_right:
  for -ce: C.EditStructure
  for p: C.Change.of(ce)
  {C.then(ce, p, C.keep(ce)) == p : C.Change.of(ce)}

# LAW: grouping doesn't matter.
law then_assoc:
  for -ce: C.EditStructure
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
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)
  {C.Inc.f(ca, cb, C.Inc{f, df}) == f : C.Value(ca) -> C.Value(cb)}

# LAW: Inc.df gives the derivative.
law inc_df:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  for ~df: C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)
  {C.Inc.df(ca, cb, C.Inc{f, df}) == df : C.Value(ca) -> C.Edit(ca) -> C.Edit(cb)}

# LAW: an Inc is correct when applying its derivative's change to f(a)
# gives f of the changed value.
law inc_ok:
  for -ca: C.EditStructure
  for -cb: C.EditStructure
  for -g: C.Inc<ca, cb>
  {C.Inc.ok(ca, cb, g) == (@a: C.Value(ca) -> @d: C.Edit(ca) -> {C.EditStructure.apply(cb)(C.Inc.df(ca, cb, g)(a, d), C.Inc.f(ca, cb, g)(a)) == C.Inc.f(ca, cb, g)(C.EditStructure.apply(ca)(d, a)) : C.Value(cb)}) : Type}

# Lifting
# -------
# lift turns g, whose derivative handles one edit as ca says, into an Inc
# whose derivative handles any change.

# LAW: lift(g) has g's function, and lift.df for its derivative.
law lift:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  {C.lift(~ca, ~cb, ~g) == C.Inc{C.Inc.f(ca, C.changes(~cb), g), a => d => C.lift.df(~ca, ~cb, ~g, d, a)} : C.Inc<C.changes(~ca), C.changes(~cb)>}

# LAW: keeping the input keeps the result.
law lift_keep:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.keep(ca), a) == C.keep(cb) : C.Change.of(cb)}

# LAW: replacing the input replaces the result, with f of the new value.
law lift_replace:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for x: C.Value(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.replace(ca, x), a) == C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)) : C.Change.of(cb)}

# LAW: one edit gives g's change.
law lift_edit:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for e: C.Edit(ca)
  for a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.edit(ca, e), a) == C.Inc.df(ca, C.changes(~cb), g)(a, e) : C.Change.of(cb)}

# LAW: p then q lifts q from the value p produced.
law lift_then:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for p: C.Change.of(ca)
  for q: C.Change.of(ca)
  for +a: C.Value(ca)
  {C.lift.df(~ca, ~cb, ~g, C.then(ca, p, q), a) == C.then(cb, C.lift.df(~ca, ~cb, ~g, p, a), C.lift.df(~ca, ~cb, ~g, q, C.apply(~ca, p, a))) : C.Change.of(cb)}

# It follows that:

# LAW: lift(g) is correct for every change, if g is correct for every
# single edit.
law lift_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.changes(~cb), g)
  C.Inc.ok(C.changes(~ca), C.changes(~cb), C.lift(~ca, ~cb, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the changed value.
law recompute:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  {C.recompute(~ca, ~cb, ~f) == C.Inc{f, a => d => C.replace(cb, f(C.EditStructure.apply(ca)(d, a)))} : C.Inc<ca, C.changes(~cb)>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  C.Inc.ok(ca, C.changes(~cb), C.recompute(~ca, ~cb, ~f))
