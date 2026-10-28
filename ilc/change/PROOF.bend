import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# How values are edited
# ---------------------

def Laws.reaches(ce):
  {==}

def Laws.none(A):
  {==}

# Runs
# ----

def Laws.run_nil(ce, a):
  {==}

def Laws.run_con(ce, e, es, a):
  {==}

def Laws.runs(ce):
  {==}

def Laws.run_append(ce, xs, ys, a):
  C.run_append(~ce, xs, ys, a)

# Whole
# -----

def Laws.whole(ce):
  {==}

def Laws.whole_replace(ce, x, a):
  {==}

def Laws.whole_apply(ce, e, a):
  {==}

def Laws.whole_change_structure(ce):
  {==}

# Incremental functions
# ---------------------

def Laws.inc_ok(ca, cb, g):
  {==}

# Lifting
# -------

def Laws.lift(ca, cb, g):
  {==}

def Laws.lift_nil(ca, cb, g, a):
  {==}

def Laws.lift_con(ca, cb, g, e, es, a):
  {==}

# Lemma: grouping appends doesn't matter.
law append_assoc:
  for -E: Data
  for xs: List<&2, E>
  for ys: List<&2, E>
  for zs: List<&2, E>
  {List.append(&2, E, List.append(&2, E, xs, ys), zs) == List.append(&2, E, xs, List.append(&2, E, ys, zs)) : List<&2, E>}

def append_assoc(E, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_assoc(E, t, ys, zs) : {h <> List.append(&2, E, List.append(&2, E, t, ys), zs) == h <> _ : List<&2, E>}
      {==}

def Laws.lift_append(ca, cb, g, xs, ys, a):
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(List<&2, C.Edit(cb)>, C.lift.run(~ca, ~cb, ~g, List.append(&2, C.Edit(ca), t, ys), C.EditStructure.apply(ca)(e, a)), List.append(&2, C.Edit(cb), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))), Laws.lift_append(~ca, ~cb, ~g, t, ys, C.EditStructure.apply(ca)(e, a))) : {List.append(&2, C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), _) == List.append(&2, C.Edit(cb), List.append(&2, C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))) : List<&2, C.Edit(cb)>}
      %append_assoc(C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))) : {_ == List.append(&2, C.Edit(cb), List.append(&2, C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))) : List<&2, C.Edit(cb)>}
      {==}

# Lemma: lift's derivative is correct for a run of edits, if g is for
# each edit.
law lift_run_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.runs(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.runs(~cb), g)
  for es: List<&2, C.Edit(ca)>
  for +a: C.Value(ca)
  {C.run(~cb, C.lift.run(~ca, ~cb, ~g, es, a), C.Inc.f(ca, C.runs(~cb), g)(a)) == C.Inc.f(ca, C.runs(~cb), g)(C.run(~ca, es, a)) : C.Value(cb)}

def lift_run_ok(ca, cb, g, g_ok, es, a):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(C.Value(cb), C.run(~cb, List.append(&2, C.Edit(cb), C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.Inc.f(ca, C.runs(~cb), g)(a)), C.run(~cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.run(~cb, C.Inc.df(ca, C.runs(~cb), g)(a, e), C.Inc.f(ca, C.runs(~cb), g)(a))), C.run_append(~cb, C.Inc.df(ca, C.runs(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.Inc.f(ca, C.runs(~cb), g)(a))) : {_ == C.Inc.f(ca, C.runs(~cb), g)(C.run(~ca, t, C.EditStructure.apply(ca)(e, a))) : C.Value(cb)}
      %Equal.sym(C.Value(cb), C.run(~cb, C.Inc.df(ca, C.runs(~cb), g)(a, e), C.Inc.f(ca, C.runs(~cb), g)(a)), C.Inc.f(ca, C.runs(~cb), g)(C.EditStructure.apply(ca)(e, a)), g_ok(a, e)) : {C.run(~cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), _) == C.Inc.f(ca, C.runs(~cb), g)(C.run(~ca, t, C.EditStructure.apply(ca)(e, a))) : C.Value(cb)}
      lift_run_ok(~ca, ~cb, ~g, ~g_ok, t, C.EditStructure.apply(ca)(e, a))

def Laws.lift_ok(ca, cb, g, g_ok):
  a => es => lift_run_ok(~ca, ~cb, ~g, ~g_ok, es, a)

# Lifting through whole
# ---------------------

def Laws.whole_lift(ca, cb, g):
  {==}

def Laws.whole_lift_replace(ca, cb, g, x, a):
  {==}

def Laws.whole_lift_apply(ca, cb, g, e, a):
  {==}

# Lemma: whole.lift's derivative is correct at every edit, if g is.
law whole_lift_df_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for w: C.Whole<ca>
  for a: C.Value(ca)
  {C.whole.apply(~cb, C.whole.lift.df(~ca, ~cb, ~g, w, a), C.Inc.f(ca, cb, g)(a)) == C.Inc.f(ca, cb, g)(C.whole.apply(~ca, w, a)) : C.Value(cb)}

def whole_lift_df_ok(ca, cb, g, g_ok, w, a):
  match w:
    case C.Replace{x}:
      {==}
    case C.Apply{e}:
      g_ok(a, e)

def Laws.whole_lift_ok(ca, cb, g, g_ok):
  a => w => whole_lift_df_ok(~ca, ~cb, ~g, ~g_ok, w, a)

# Recomputing
# -----------

def Laws.recompute(ca, cb, f):
  {==}

def Laws.recompute_ok(ca, cb, f):
  a => e => {==}

# Mapping edits
# -------------

def Laws.map_edits_nil(EA, EB, fe):
  {==}

def Laws.map_edits_con(EA, EB, fe, e, es):
  {==}
