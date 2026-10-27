import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# Changes to any value
# --------------------

def Laws.apply_keep(A, E, ea, a):
  {==}

def Laws.apply_replace(A, E, ea, x, a):
  {==}

def Laws.apply_edit(A, E, ea, e, a):
  {==}

def Laws.apply_then(A, E, ea, p, q, a):
  {==}

def Laws.then_keep_left(A, E, ea, q, a):
  {==}

def Laws.then_keep_right(A, E, ea, p, a):
  {==}

def Laws.then_assoc(A, E, ea, p, q, r, a):
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

def Laws.inc_ok(A, DA, B, DB, pa, pb, g):
  {==}

# Lifting
# -------

def Laws.lift(A, EA, B, EB, ea, g):
  {==}

def Laws.lift_keep(A, EA, B, EB, ea, g, a):
  {==}

def Laws.lift_replace(A, EA, B, EB, ea, g, x, a):
  {==}

def Laws.lift_edit(A, EA, B, EB, ea, g, e, a):
  {==}

def Laws.lift_then(A, EA, B, EB, ea, g, p, q, a):
  {==}

# Lemma: lift's derivative is correct at every change, if g's is at every
# edit.
law lift_df_ok:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~eb: EB -> B -> B
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for ~g_ok: C.Inc.ok(A, EA, B, C.Change<B, EB>, ea, (d => b => C.apply(~B, ~EB, ~eb, d, b)), g)
  for d: C.Change<A, EA>
  for +a: A
  {C.apply(~B, ~EB, ~eb, C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, d, a), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(a)) == C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ea, d, a)) : B}

# By induction on the change: after the first part of a Then, the lifted
# derivative of the rest starts from the value the first part produced.
def lift_df_ok(A, EA, B, EB, ea, eb, g, g_ok, d, a):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{x}:
      {==}
    case C.Edit{e}:
      g_ok(a, e)
    case C.Then{+p, q}:
      %Equal.sym(B, C.apply(~B, ~EB, ~eb, C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, p, a), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(a)), C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ea, p, a)), lift_df_ok(~A, ~EA, ~B, ~EB, ~ea, ~eb, ~g, ~g_ok, p, a)) : {C.apply(~B, ~EB, ~eb, C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, q, C.apply(~A, ~EA, ~ea, p, a)), _) == C.Inc.f(A, EA, B, C.Change<B, EB>, g)(C.apply(~A, ~EA, ~ea, q, C.apply(~A, ~EA, ~ea, p, a))) : B}
      lift_df_ok(~A, ~EA, ~B, ~EB, ~ea, ~eb, ~g, ~g_ok, q, C.apply(~A, ~EA, ~ea, p, a))

def Laws.lift_ok(A, EA, B, EB, ea, eb, g, g_ok):
  a => d => lift_df_ok(~A, ~EA, ~B, ~EB, ~ea, ~eb, ~g, ~g_ok, d, a)

# Recomputing
# -----------

def Laws.recompute(A, DA, B, EB, pa, f):
  {==}

def Laws.recompute_ok(A, DA, B, EB, pa, eb, f):
  a => d => {==}
