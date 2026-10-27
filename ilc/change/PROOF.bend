import Base
import ./change.bend as C
import ./LAWS.bend as Laws

# Changes to any value
# --------------------

def Laws.apply_keep(A, E, edit, a):
  {==}

def Laws.apply_replace(A, E, edit, x, a):
  {==}

def Laws.apply_edit(A, E, edit, e, a):
  {==}

def Laws.apply_then(A, E, edit, p, q, a):
  {==}

def Laws.then_keep_left(A, E, edit, q, a):
  {==}

def Laws.then_keep_right(A, E, edit, p, a):
  {==}

def Laws.then_assoc(A, E, edit, p, q, r, a):
  {==}

# Derivatives
# -----------

# By induction on the change: after the first part of a Then, the lifted
# derivative of the rest starts from the value the first part produced.
def Laws.lift(A, EA, B, EB, ea, eb, f, fe, fe_ok, d, a):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{x}:
      {==}
    case C.Edit{e}:
      fe_ok(a, e)
    case C.Then{+p, q}:
      %Equal.sym(B, C.apply(~B, ~EB, ~eb, C.lift(~A, ~EA, ~B, ~EB, ~ea, ~f, ~fe, p, a), f(a)), f(C.apply(~A, ~EA, ~ea, p, a)), Laws.lift(~A, ~EA, ~B, ~EB, ~ea, ~eb, ~f, ~fe, ~fe_ok, p, a)) : {C.apply(~B, ~EB, ~eb, C.lift(~A, ~EA, ~B, ~EB, ~ea, ~f, ~fe, q, C.apply(~A, ~EA, ~ea, p, a)), _) == f(C.apply(~A, ~EA, ~ea, q, C.apply(~A, ~EA, ~ea, p, a))) : B}
      Laws.lift(~A, ~EA, ~B, ~EB, ~ea, ~eb, ~f, ~fe, ~fe_ok, q, C.apply(~A, ~EA, ~ea, p, a))

def Laws.recompute(A, DA, B, EB, pa, eb, f, a, d):
  {==}
