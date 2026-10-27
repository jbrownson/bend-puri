import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# Changes to any value
# --------------------
# A type supplies its edits E and `edit`, how to apply one.

# LAW: keeping changes nothing.
law apply_keep:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for a: A
  {C.apply(~A, ~E, ~edit, C.Keep{}, a) == a : A}

# LAW: replacing gives the new value.
law apply_replace:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for x: A
  for a: A
  {C.apply(~A, ~E, ~edit, C.Replace{x}, a) == x : A}

# LAW: an edit is applied by `edit`.
law apply_edit:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for e: E
  for a: A
  {C.apply(~A, ~E, ~edit, C.Edit{e}, a) == edit(e, a) : A}

# LAW: one change then another applies the first, then the second.
law apply_then:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~edit, C.Then{p, q}, a) == C.apply(~A, ~E, ~edit, q, C.apply(~A, ~E, ~edit, p, a)) : A}

# It follows that:

# LAW: keeping first does nothing.
law then_keep_left:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~edit, C.Then{C.Keep{}, q}, a) == C.apply(~A, ~E, ~edit, q, a) : A}

# LAW: keeping last does nothing.
law then_keep_right:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for p: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~edit, C.Then{p, C.Keep{}}, a) == C.apply(~A, ~E, ~edit, p, a) : A}

# LAW: grouping doesn't matter.
law then_assoc:
  for ~A: Data
  for ~E: Data
  for ~edit: E -> A -> A
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for r: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~edit, C.Then{C.Then{p, q}, r}, a) == C.apply(~A, ~E, ~edit, C.Then{p, C.Then{q, r}}, a) : A}

# Derivatives
# -----------
# A derivative of f: A -> B takes a value and its change, and gives the
# change to f's result. It is correct when applying that change to f(a)
# gives f of the changed value.

# LAW: a derivative lifted from single edits is correct for every change,
# if it is correct for every single edit.
law lift:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~eb: EB -> B -> B
  for ~f: A -> B
  for ~fe: A -> EA -> C.Change<B, EB>
  for ~fe_ok: (@a: A -> @e: EA -> {C.apply(~B, ~EB, ~eb, fe(a, e), f(a)) == f(ea(e, a)) : B})
  for d: C.Change<A, EA>
  for +a: A
  {C.apply(~B, ~EB, ~eb, C.lift(~A, ~EA, ~B, ~EB, ~ea, ~f, ~fe, d, a), f(a)) == f(C.apply(~A, ~EA, ~ea, d, a)) : B}

# LAW: recomputing is a correct derivative of any function, for changes of
# any type DA, applied by `pa`.
law recompute:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~EB: Data
  for ~pa: DA -> A -> A
  for ~eb: EB -> B -> B
  for ~f: A -> B
  for a: A
  for d: DA
  {C.apply(~B, ~EB, ~eb, C.recompute(~A, ~DA, ~B, ~EB, ~pa, ~f, a, d), f(a)) == f(pa(d, a)) : B}
