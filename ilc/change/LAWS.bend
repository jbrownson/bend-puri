import Base
import ./change.bend as C

# What edits promise; PROOF.bend proves it.

# How values are edited
# ---------------------
# An edit structure says how values are edited: values of type Value, by
# edits of type Edit, which `apply` applies. A change structure is an edit
# structure with the proof that one edit gets from any value to any other.

# LAW: an edit structure reaches when one edit gets from any value to any
# other.
law reaches:
  for -ce: C.EditStructure
  {C.reaches(ce) == (@a: C.Value(ce) -> @b: C.Value(ce) -> &d: C.Edit(ce) -> {C.EditStructure.apply(ce)(d, a) == b : C.Value(ce)}) : Type}

# LAW: values with no edits of their own have Empty for edits.
law none:
  for ~A: Data
  {C.none(~A) == C.EditStructure{A, Empty, e => a => Empty.absurd(A, e)} : C.EditStructure}

# Runs
# ----
# runs(ce) edits a value by a run of ce's edits, applied in order.

# LAW: a run of no edits leaves the value as it is.
law run_nil:
  for ~ce: C.EditStructure
  for a: C.Value(ce)
  {C.run(~ce, Nil{}, a) == a : C.Value(ce)}

# LAW: a run applies its first edit, then the rest.
law run_con:
  for ~ce: C.EditStructure
  for e: C.Edit(ce)
  for es: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.run(~ce, e <> es, a) == C.run(~ce, es, C.EditStructure.apply(ce)(e, a)) : C.Value(ce)}

# LAW: runs of ce's edits edit ce's values by C.run.
law runs:
  for ~ce: C.EditStructure
  {C.runs(~ce) == C.EditStructure{C.Value(ce), List<&2, C.Edit(ce)>, es => a => C.run(~ce, es, a)} : C.EditStructure}

# It follows that:

# LAW: one run then another runs the first, then the second.
law run_append:
  for ~ce: C.EditStructure
  for xs: List<&2, C.Edit(ce)>
  for ys: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.run(~ce, List.append(&2, C.Edit(ce), xs, ys), a) == C.run(~ce, ys, C.run(~ce, xs, a)) : C.Value(ce)}

# Whole
# -----
# whole(ce) edits a value by one of ce's edits, or by replacing it whole.

# LAW: whole(ce)'s edits are Wholes of ce's values and edits, which
# whole.apply applies.
law whole:
  for ~ce: C.EditStructure
  {C.whole(~ce) == C.EditStructure{C.Value(ce), C.Whole<ce>, w => a => C.whole.apply(~ce, w, a)} : C.EditStructure}

# LAW: replacing gives the new value.
law whole_replace:
  for ~ce: C.EditStructure
  for x: C.Value(ce)
  for a: C.Value(ce)
  {C.whole.apply(~ce, C.Replace{x}, a) == x : C.Value(ce)}

# LAW: one of ce's edits applies as ce says.
law whole_apply:
  for ~ce: C.EditStructure
  for e: C.Edit(ce)
  for a: C.Value(ce)
  {C.whole.apply(~ce, C.Apply{e}, a) == C.EditStructure.apply(ce)(e, a) : C.Value(ce)}

# LAW: whole(ce) is a change structure, whatever ce is.
law whole_change_structure:
  for ~ce: C.EditStructure
  {C.ChangeStructure.structure(C.whole.change_structure(~ce)) == C.whole(~ce) : C.EditStructure}

# Incremental functions
# ---------------------
# An Inc<ca, cb> is a function from values edited as ca says to values
# edited as cb says, with its derivative: from a value and its edit, the
# edit to the function's result.

# LAW: an Inc is correct when applying its derivative's edit to f(a) gives
# f of the edited value.
law inc_ok:
  for -ca: C.EditStructure
  for -cb: C.EditStructure
  for -g: C.Inc<ca, cb>
  {C.Inc.ok(ca, cb, g) == (@a: C.Value(ca) -> @d: C.Edit(ca) -> {C.EditStructure.apply(cb)(C.Inc.df(ca, cb, g)(a, d), C.Inc.f(ca, cb, g)(a)) == C.Inc.f(ca, cb, g)(C.EditStructure.apply(ca)(d, a)) : C.Value(cb)}) : Type}

# Lifting
# -------
# g is an Inc<ca, runs(cb)>: a function, and a derivative that gives a
# run of cb's edits for one of ca's. lift(g) handles runs of ca's edits.

# LAW: lift(g) is g's function, with lift.run for its derivative.
law lift:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  {C.lift(~ca, ~cb, ~g) == C.Inc{C.Inc.f(ca, C.runs(~cb), g), a => es => C.lift.run(~ca, ~cb, ~g, es, a)} : C.Inc<C.runs(~ca), C.runs(~cb)>}

# LAW: no edits give no edits.
law lift_nil:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  for a: C.Value(ca)
  {C.lift.run(~ca, ~cb, ~g, Nil{}, a) == Nil{} : List<&2, C.Edit(cb)>}

# LAW: an edit gives g's run, then the rest give theirs from the value
# after it.
law lift_con:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  for e: C.Edit(ca)
  for es: List<&2, C.Edit(ca)>
  for +a: C.Value(ca)
  {C.lift.run(~ca, ~cb, ~g, e <> es, a) == List.append(&2, C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, es, C.EditStructure.apply(ca)(e, a))) : List<&2, C.Edit(cb)>}

# It follows that:

# LAW: one run then another gives the first's edits, then the second's
# from the value the first left.
law lift_append:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  for +xs: List<&2, C.Edit(ca)>
  for +ys: List<&2, C.Edit(ca)>
  for +a: C.Value(ca)
  {C.lift.run(~ca, ~cb, ~g, List.append(&2, C.Edit(ca), xs, ys), a) == List.append(&2, C.Edit(cb), C.lift.run(~ca, ~cb, ~g, xs, a), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, xs, a))) : List<&2, C.Edit(cb)>}

# LAW: lift(g) is correct for every run, if g is correct for every edit.
law lift_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.runs(~cb), g)
  C.Inc.ok(C.runs(~ca), C.runs(~cb), C.lift(~ca, ~cb, ~g))

# Lifting through whole
# ---------------------

# LAW: whole.lift(g) is g's function, with whole.lift.df for its
# derivative.
law whole_lift:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  {C.whole.lift(~ca, ~cb, ~g) == C.Inc{C.Inc.f(ca, cb, g), a => w => C.whole.lift.df(~ca, ~cb, ~g, w, a)} : C.Inc<C.whole(~ca), C.whole(~cb)>}

# LAW: replacing the input replaces the result, with f of the new value.
law whole_lift_replace:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for x: C.Value(ca)
  for a: C.Value(ca)
  {C.whole.lift.df(~ca, ~cb, ~g, C.Replace{x}, a) == C.Replace{C.Inc.f(ca, cb, g)(x)} : C.Whole<cb>}

# LAW: an edit gives g's edit.
law whole_lift_apply:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for e: C.Edit(ca)
  for a: C.Value(ca)
  {C.whole.lift.df(~ca, ~cb, ~g, C.Apply{e}, a) == C.Apply{C.Inc.df(ca, cb, g)(a, e)} : C.Whole<cb>}

# It follows that:

# LAW: whole.lift(g) is correct, if g is.
law whole_lift_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  C.Inc.ok(C.whole(~ca), C.whole(~cb), C.whole.lift(~ca, ~cb, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the edited value.
law recompute:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  {C.recompute(~ca, ~cb, ~f) == C.Inc{f, a => e => C.Replace{f(C.EditStructure.apply(ca)(e, a))}} : C.Inc<ca, C.whole(~cb)>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~f: C.Value(ca) -> C.Value(cb)
  C.Inc.ok(ca, C.whole(~cb), C.recompute(~ca, ~cb, ~f))

# Mapping edits
# -------------

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
