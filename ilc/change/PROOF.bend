import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# How values change
# -----------------

def Laws.changes_apply(A, DA, f):
  {==}

# Changes to any value
# --------------------

def Laws.apply_keep(A, E, ce, a):
  {==}

def Laws.apply_replace(A, E, ce, x, a):
  {==}

def Laws.apply_edit(A, E, ce, e, a):
  {==}

def Laws.apply_then(A, E, ce, p, q, a):
  {==}

def Laws.then_keep_left(A, E, ce, q, a):
  {==}

def Laws.then_keep_right(A, E, ce, p, a):
  {==}

def Laws.then_assoc(A, E, ce, p, q, r, a):
  {==}

def Laws.changes(A, E, ce, d, a):
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

def Laws.inc_f(A, DA, B, DB, f, df):
  {==}

def Laws.inc_df(A, DA, B, DB, f, df):
  {==}

def Laws.inc_ok(A, DA, B, DB, ca, cb, g):
  {==}

# Lifting
# -------

def Laws.lift(A, EA, B, EB, ca, g):
  {==}

def Laws.lift_keep(A, EA, B, EB, ca, g, a):
  {==}

def Laws.lift_replace(A, EA, B, EB, ca, g, x, a):
  {==}

def Laws.lift_edit(A, EA, B, EB, ca, g, e, a):
  {==}

def Laws.lift_then(A, EA, B, EB, ca, g, p, q, a):
  {==}

# Lemma: lift's derivative is correct at every change, if g's is at every
# edit.
law lift_df_ok:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~cb: C.Changes<B, EB>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for ~g_ok: C.Inc.ok(A, EA, B, C.Change<B, EB>, ca, C.changes(~B, ~EB, ~cb), g)
  for d: C.Change<A, EA>
  for +a: A
  {C.apply(~B, ~EB, ~cb, C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, d, a), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(a)) == C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ca, d, a)) : B}

# By induction on the change: after the first part of a Then, the lifted
# derivative of the rest starts from the value the first part produced.
def lift_df_ok(A, EA, B, EB, ca, cb, g, g_ok, d, a):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{x}:
      {==}
    case C.Edit{e}:
      g_ok(a, e)
    case C.Then{+p, q}:
      %Equal.sym(B, C.apply(~B, ~EB, ~cb, C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, p, a), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(a)), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ca, p, a)), lift_df_ok(~A, ~EA, ~B, ~EB, ~ca, ~cb, ~g, ~g_ok, p, a)) : {C.apply(~B, ~EB, ~cb, C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, q, C.apply(~A, ~EA, ~ca, p, a)), _) == C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ca, q, C.apply(~A, ~EA, ~ca, p, a))) : B}
      lift_df_ok(~A, ~EA, ~B, ~EB, ~ca, ~cb, ~g, ~g_ok, q, C.apply(~A, ~EA, ~ca, p, a))

def Laws.lift_ok(A, EA, B, EB, ca, cb, g, g_ok):
  a => d => lift_df_ok(~A, ~EA, ~B, ~EB, ~ca, ~cb, ~g, ~g_ok, d, a)

# Recomputing
# -----------

def Laws.recompute(A, DA, B, EB, ca, f):
  {==}

def Laws.recompute_ok(A, DA, B, EB, ca, cb, f):
  a => d => {==}
