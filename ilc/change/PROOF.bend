import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# How values change
# -----------------

def Laws.value(V, D, f):
  {==}

def Laws.edit_type(V, D, f):
  {==}

def Laws.structure_apply(V, D, f):
  {==}

def Laws.reaches(ce):
  {==}

def Laws.change_structure(s, r):
  {==}

# Changes to any value
# --------------------

def Laws.change_of(ce):
  {==}

def Laws.apply_nil(ce, a):
  {==}

def Laws.apply_start(ce, x, es, a):
  {==}

def Laws.apply_con(ce, e, es, a):
  {==}

def Laws.keep(ce):
  {==}

def Laws.replace(ce, x):
  {==}

def Laws.edit(ce, e):
  {==}

def Laws.then_start(ce, p, y, es):
  match p:
    case C.Change{ps, pes}:
      {==}

def Laws.then_edits(ce, s, ps, qs):
  {==}

def Laws.changes(ce):
  {==}

def Laws.complete(ce):
  {==}

def Laws.whole(A):
  {==}

def Laws.apply_keep(ce, a):
  {==}

def Laws.apply_replace(ce, x, a):
  {==}

def Laws.apply_edit(ce, e, a):
  {==}

# Lemma: running appended edits runs the first, then the second.
law run_append:
  for ~ce: C.EditStructure
  for xs: List<&2, C.Edit(ce)>
  for ys: List<&2, C.Edit(ce)>
  for a: C.Value(ce)
  {C.run(~ce, List.append(&2, C.Edit(ce), xs, ys), a) == C.run(~ce, ys, C.run(~ce, xs, a)) : C.Value(ce)}

def run_append(ce, xs, ys, a):
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      run_append(~ce, t, ys, C.EditStructure.apply(ce)(e, a))

def Laws.apply_then(ce, p, q, a):
  match p:
    case C.Change{ps, pes}:
      match q:
        case C.Change{qs, qes}:
          match qs:
            case Some{y}:
              {==}
            case None{}:
              run_append(~ce, pes, qes, C.start(C.Value(ce), ps, a))

def Laws.then_keep_left(ce, q):
  match q:
    case C.Change{qs, qes}:
      match qs:
        case Some{y}:
          {==}
        case None{}:
          {==}

# Lemma: appending nothing leaves a list as it was.
law append_nil:
  for -E: Data
  for xs: List<&2, E>
  {List.append(&2, E, xs, Nil{}) == xs : List<&2, E>}

def append_nil(E, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(List<&2, E>, List.append(&2, E, t, Nil{}), t, append_nil(E, t)) : {h <> _ == h <> t : List<&2, E>}
      {==}

def Laws.then_keep_right(ce, p):
  match p:
    case C.Change{ps, pes}:
      %Equal.sym(List<&2, C.Edit(ce)>, List.append(&2, C.Edit(ce), pes, Nil{}), pes, append_nil(C.Edit(ce), pes)) : {C.Change{ps, _} == C.Change{ps, pes} : C.Change.of(ce)}
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
      %Equal.sym(List<&2, E>, List.append(&2, E, List.append(&2, E, t, ys), zs), List.append(&2, E, t, List.append(&2, E, ys, zs)), append_assoc(E, t, ys, zs)) : {h <> _ == h <> List.append(&2, E, t, List.append(&2, E, ys, zs)) : List<&2, E>}
      {==}

def Laws.then_assoc(ce, p, q, r):
  match p:
    case C.Change{ps, pes}:
      match q:
        case C.Change{qs, qes}:
          match qs:
            case Some{y}:
              match r:
                case C.Change{rs, res}:
                  match rs:
                    case Some{z}:
                      {==}
                    case None{}:
                      {==}
            case None{}:
              match r:
                case C.Change{rs, res}:
                  match rs:
                    case Some{z}:
                      {==}
                    case None{}:
                      %Equal.sym(List<&2, C.Edit(ce)>, List.append(&2, C.Edit(ce), List.append(&2, C.Edit(ce), pes, qes), res), List.append(&2, C.Edit(ce), pes, List.append(&2, C.Edit(ce), qes, res)), append_assoc(C.Edit(ce), pes, qes, res)) : {C.Change{ps, _} == C.Change{ps, List.append(&2, C.Edit(ce), pes, List.append(&2, C.Edit(ce), qes, res))} : C.Change.of(ce)}
                      {==}

# Mapping a change
# ----------------

def Laws.map(A, EA, B, EB, fa, fe, s, es):
  {==}

def Laws.map_start_none(A, B, fa):
  {==}

def Laws.map_start_some(A, B, fa, x):
  {==}

def Laws.map_edits_nil(EA, EB, fe):
  {==}

def Laws.map_edits_con(EA, EB, fe, e, es):
  {==}

# Incremental functions
# ---------------------

def Laws.inc_f(ca, cb, f, df):
  {==}

def Laws.inc_df(ca, cb, f, df):
  {==}

def Laws.inc_ok(ca, cb, g):
  {==}

# Lifting
# -------

def Laws.lift(ca, cb, g):
  {==}

def Laws.lift_keep(ca, cb, g, a):
  {==}

def Laws.lift_replace(ca, cb, g, x, a):
  {==}

def Laws.lift_edit(ca, cb, g, e, a):
  Laws.then_keep_right(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e))

# Lemma: anything, then a change that starts over, is that change.
law then_restart:
  for -ce: C.EditStructure
  for p: C.Change.of(ce)
  for z: C.Value(ce)
  for w: C.Change.of(ce)
  {C.then(ce, p, C.then(ce, C.replace(ce, z), w)) == C.then(ce, C.replace(ce, z), w) : C.Change.of(ce)}

def then_restart(ce, p, z, w):
  match p:
    case C.Change{ps, pes}:
      match w:
        case C.Change{ws, wes}:
          match ws:
            case Some{y}:
              {==}
            case None{}:
              {==}

# Lemma: lifting appended edits lifts the first, then the second from the
# value the first produced.
law lift_run_append:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for +xs: List<&2, C.Edit(ca)>
  for +ys: List<&2, C.Edit(ca)>
  for +a: C.Value(ca)
  {C.lift.run(~ca, ~cb, ~g, List.append(&2, C.Edit(ca), xs, ys), a) == C.then(cb, C.lift.run(~ca, ~cb, ~g, xs, a), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, xs, a))) : C.Change.of(cb)}

def lift_run_append(ca, cb, g, xs, ys, a):
  match xs:
    case Nil{}:
      Equal.sym(C.Change.of(cb), C.then(cb, C.keep(cb), C.lift.run(~ca, ~cb, ~g, ys, a)), C.lift.run(~ca, ~cb, ~g, ys, a), Laws.then_keep_left(cb, C.lift.run(~ca, ~cb, ~g, ys, a)))
    case Con{+e, +t}:
      %Equal.sym(C.Change.of(cb), C.lift.run(~ca, ~cb, ~g, List.append(&2, C.Edit(ca), t, ys), C.EditStructure.apply(ca)(e, a)), C.then(cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))), lift_run_append(~ca, ~cb, ~g, t, ys, C.EditStructure.apply(ca)(e, a))) : {C.then(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), _) == C.then(cb, C.then(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))) : C.Change.of(cb)}
      Equal.sym(C.Change.of(cb), C.then(cb, C.then(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))), C.then(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.then(cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a))))), Laws.then_assoc(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.lift.run(~ca, ~cb, ~g, ys, C.run(~ca, t, C.EditStructure.apply(ca)(e, a)))))

def Laws.lift_then(ca, cb, g, p, q, a):
  match p:
    case C.Change{ps, +pes}:
      match ps:
        case None{}:
          match q:
            case C.Change{qs, +qes}:
              match qs:
                case Some{+y}:
                  Equal.sym(C.Change.of(cb), C.then(cb, C.lift.df(~ca, ~cb, ~g, C.Change{None{}, pes}, a), C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(y)), C.lift.run(~ca, ~cb, ~g, qes, y))), C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(y)), C.lift.run(~ca, ~cb, ~g, qes, y)), then_restart(cb, C.lift.df(~ca, ~cb, ~g, C.Change{None{}, pes}, a), C.Inc.f(ca, C.changes(~cb), g)(y), C.lift.run(~ca, ~cb, ~g, qes, y)))
                case None{}:
                  lift_run_append(~ca, ~cb, ~g, pes, qes, a)
        case Some{+x}:
          match q:
            case C.Change{qs, +qes}:
              match qs:
                case Some{+y}:
                  Equal.sym(C.Change.of(cb), C.then(cb, C.lift.df(~ca, ~cb, ~g, C.Change{Some{x}, pes}, a), C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(y)), C.lift.run(~ca, ~cb, ~g, qes, y))), C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(y)), C.lift.run(~ca, ~cb, ~g, qes, y)), then_restart(cb, C.lift.df(~ca, ~cb, ~g, C.Change{Some{x}, pes}, a), C.Inc.f(ca, C.changes(~cb), g)(y), C.lift.run(~ca, ~cb, ~g, qes, y)))
                case None{}:
                  %Equal.sym(C.Change.of(cb), C.lift.run(~ca, ~cb, ~g, List.append(&2, C.Edit(ca), pes, qes), x), C.then(cb, C.lift.run(~ca, ~cb, ~g, pes, x), C.lift.run(~ca, ~cb, ~g, qes, C.run(~ca, pes, x))), lift_run_append(~ca, ~cb, ~g, pes, qes, x)) : {C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), _) == C.then(cb, C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.lift.run(~ca, ~cb, ~g, pes, x)), C.lift.run(~ca, ~cb, ~g, qes, C.run(~ca, pes, x))) : C.Change.of(cb)}
                  Equal.sym(C.Change.of(cb), C.then(cb, C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.lift.run(~ca, ~cb, ~g, pes, x)), C.lift.run(~ca, ~cb, ~g, qes, C.run(~ca, pes, x))), C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.then(cb, C.lift.run(~ca, ~cb, ~g, pes, x), C.lift.run(~ca, ~cb, ~g, qes, C.run(~ca, pes, x)))), Laws.then_assoc(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.lift.run(~ca, ~cb, ~g, pes, x), C.lift.run(~ca, ~cb, ~g, qes, C.run(~ca, pes, x))))

# Lemma: lift's derivative is correct for a run of edits, if g is for
# each edit.
law lift_run_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.changes(~cb), g)
  for es: List<&2, C.Edit(ca)>
  for +a: C.Value(ca)
  {C.apply(~cb, C.lift.run(~ca, ~cb, ~g, es, a), C.Inc.f(ca, C.changes(~cb), g)(a)) == C.Inc.f(ca, C.changes(~cb), g)(C.run(~ca, es, a)) : C.Value(cb)}

def lift_run_ok(ca, cb, g, g_ok, es, a):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(C.Value(cb), C.apply(~cb, C.then(cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a))), C.Inc.f(ca, C.changes(~cb), g)(a)), C.apply(~cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.apply(~cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.Inc.f(ca, C.changes(~cb), g)(a))), Laws.apply_then(~cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), C.Inc.f(ca, C.changes(~cb), g)(a))) : {_ == C.Inc.f(ca, C.changes(~cb), g)(C.run(~ca, t, C.EditStructure.apply(ca)(e, a))) : C.Value(cb)}
      %Equal.sym(C.Value(cb), C.apply(~cb, C.Inc.df(ca, C.changes(~cb), g)(a, e), C.Inc.f(ca, C.changes(~cb), g)(a)), C.Inc.f(ca, C.changes(~cb), g)(C.EditStructure.apply(ca)(e, a)), g_ok(a, e)) : {C.apply(~cb, C.lift.run(~ca, ~cb, ~g, t, C.EditStructure.apply(ca)(e, a)), _) == C.Inc.f(ca, C.changes(~cb), g)(C.run(~ca, t, C.EditStructure.apply(ca)(e, a))) : C.Value(cb)}
      lift_run_ok(~ca, ~cb, ~g, ~g_ok, t, C.EditStructure.apply(ca)(e, a))

# Lemma: lift's derivative is correct at every change, if g is at every
# edit.
law lift_df_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, C.changes(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.changes(~cb), g)
  for d: C.Change.of(ca)
  for +a: C.Value(ca)
  {C.apply(~cb, C.lift.df(~ca, ~cb, ~g, d, a), C.Inc.f(ca, C.changes(~cb), g)(a)) == C.Inc.f(ca, C.changes(~cb), g)(C.apply(~ca, d, a)) : C.Value(cb)}

def lift_df_ok(ca, cb, g, g_ok, d, a):
  match d:
    case C.Change{s, +es}:
      match s:
        case None{}:
          lift_run_ok(~ca, ~cb, ~g, ~g_ok, es, a)
        case Some{+x}:
          %Equal.sym(C.Value(cb), C.apply(~cb, C.then(cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.lift.run(~ca, ~cb, ~g, es, x)), C.Inc.f(ca, C.changes(~cb), g)(a)), C.apply(~cb, C.lift.run(~ca, ~cb, ~g, es, x), C.apply(~cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.Inc.f(ca, C.changes(~cb), g)(a))), Laws.apply_then(~cb, C.replace(cb, C.Inc.f(ca, C.changes(~cb), g)(x)), C.lift.run(~ca, ~cb, ~g, es, x), C.Inc.f(ca, C.changes(~cb), g)(a))) : {_ == C.Inc.f(ca, C.changes(~cb), g)(C.run(~ca, es, x)) : C.Value(cb)}
          lift_run_ok(~ca, ~cb, ~g, ~g_ok, es, x)

def Laws.lift_ok(ca, cb, g, g_ok):
  a => d => lift_df_ok(~ca, ~cb, ~g, ~g_ok, d, a)

# Recomputing
# -----------

def Laws.recompute(ca, cb, f):
  {==}

def Laws.recompute_ok(ca, cb, f):
  a => d => {==}
