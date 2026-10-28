import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# How values change
# -----------------

def Laws.value(V, D, f):
  {==}

def Laws.delta(V, D, f):
  {==}

def Laws.structure_apply(V, D, f):
  {==}

# Changes to any value
# --------------------

def Laws.change_of(ce):
  {==}

def Laws.apply_keep(ce, a):
  {==}

def Laws.apply_replace(ce, x, a):
  {==}

def Laws.apply_edit(ce, e, a):
  {==}

def Laws.apply_then(ce, p, q, a):
  {==}

def Laws.change_structure(ce):
  {==}

def Laws.then_keep_left(ce, q, a):
  {==}

def Laws.then_keep_right(ce, p, a):
  {==}

def Laws.then_assoc(ce, p, q, r, a):
  {==}

# Mapping a change
# ----------------

def Laws.map_keep(A, EA, B, EB, fa, fe):
  {==}

def Laws.map_replace(A, EA, B, EB, fa, fe, x):
  {==}

def Laws.map_edit(A, EA, B, EB, fa, fe, e):
  {==}

def Laws.map_then(A, EA, B, EB, fa, fe, p, q):
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
  {==}

def Laws.lift_then(ca, cb, g, p, q, a):
  {==}

# Lemma: lift's derivative is correct at every change, if g's is at every
# edit.
law lift_df_ok:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, C.Change.structure(~cb)>
  for ~g_ok: C.Inc.ok(ca, C.Change.structure(~cb), g)
  for d: C.Change.of(ca)
  for +a: C.Value(ca)
  {C.apply(~cb, C.lift.df(~ca, ~cb, ~g, d, a), C.Inc.f(ca, C.Change.structure(~cb), g)(a)) == C.Inc.f(ca, C.Change.structure(~cb), g)(C.apply(~ca, d, a)) : C.Value(cb)}

# By induction on the change: after the first part of a Then, the lifted
# derivative of the rest starts from the value the first part produced.
def lift_df_ok(ca, cb, g, g_ok, d, a):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{x}:
      {==}
    case C.Edit{e}:
      g_ok(a, e)
    case C.Then{+p, q}:
      %Equal.sym(C.Value(cb), C.apply(~cb, C.lift.df(~ca, ~cb, ~g, p, a), C.Inc.f(ca, C.Change.structure(~cb), g)(a)), C.Inc.f(ca, C.Change.structure(~cb), g)(C.apply(~ca, p, a)), lift_df_ok(~ca, ~cb, ~g, ~g_ok, p, a)) : {C.apply(~cb, C.lift.df(~ca, ~cb, ~g, q, C.apply(~ca, p, a)), _) == C.Inc.f(ca, C.Change.structure(~cb), g)(C.apply(~ca, q, C.apply(~ca, p, a))) : C.Value(cb)}
      lift_df_ok(~ca, ~cb, ~g, ~g_ok, q, C.apply(~ca, p, a))

def Laws.lift_ok(ca, cb, g, g_ok):
  a => d => lift_df_ok(~ca, ~cb, ~g, ~g_ok, d, a)

# Recomputing
# -----------

def Laws.recompute(ca, cb, f):
  {==}

def Laws.recompute_ok(ca, cb, f):
  a => d => {==}
