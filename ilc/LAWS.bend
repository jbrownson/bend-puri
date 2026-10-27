import Base
import ./change.bend as C
import ./list.bend as L

# What the ILC layer promises; PROOF.bend proves it. The laws say what
# applying each change returns, case by case. A derivative turns a change
# to a function's input into the change to its result; the laws say when
# one is correct and when it is local.
#
# Bend doesn't infer type arguments, so each law starts with a `for` per
# type it mentions. A `~` before a name (a template) lets the law use it
# any number of times; it is how functions and hypotheses are passed.

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
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~eb: F -> B -> B
  for ~f: A -> B
  for ~fe: A -> E -> C.Change<B, F>
  for ~fe_ok: (@a: A -> @e: E -> {C.apply(~B, ~F, ~eb, fe(a, e), f(a)) == f(ea(e, a)) : B})
  for d: C.Change<A, E>
  for +a: A
  {C.apply(~B, ~F, ~eb, C.lift(~A, ~E, ~B, ~F, ~ea, ~f, ~fe, d, a), f(a)) == f(C.apply(~A, ~E, ~ea, d, a)) : B}

# LAW: recomputing is a correct derivative of any function.
law recompute:
  for ~A: Data
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~eb: F -> B -> B
  for ~f: A -> B
  for a: A
  for d: C.Change<A, E>
  {C.apply(~B, ~F, ~eb, C.recompute(~A, ~E, ~B, ~F, ~ea, ~f, a, d), f(a)) == f(C.apply(~A, ~E, ~ea, d, a)) : B}

# Lists
# -----
# List.take(xs, i) is the first i elements (all of them when i is past the
# end), List.drop(xs, i) the rest, and List.get(xs, i) the element at i, or
# None past the end. `ea` applies the elements' edits.

# LAW: a list change is applied edit by edit.
law patch:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for d: C.Change<List<&2, A>, L.Edit<A, E>>
  for xs: List<&2, A>
  {L.patch(~A, ~E, ~ea, d, xs) == C.apply(~List<&2, A>, ~L.Edit<A, E>, ~(e => ys => L.edit(~A, ~E, ~ea, e, ys)), d, xs) : List<&2, A>}

# LAW: inserting at i puts x before the element at i, or at the end when i
# is past it.
law edit_insert:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.edit(~A, ~E, ~ea, L.Insert{i, x}, xs) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, i)) : List<&2, A>}

# LAW: deleting at i removes the element at i, or nothing when i is past
# the end.
law edit_delete:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  {L.edit(~A, ~E, ~ea, L.Delete{i}, xs) == List.append(&2, A, List.take(&2, A, xs, i), List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: updating the element at i applies the change to it, in place.
law edit_update_inside:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: C.Change<A, E>
  for x: A
  for at: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.edit(~A, ~E, ~ea, L.Update{i, d}, xs) == List.append(&2, A, List.take(&2, A, xs, i), C.apply(~A, ~E, ~ea, d, x) <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: updating past the end changes nothing.
law edit_update_outside:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: C.Change<A, E>
  for past: {List.get(&2, A, xs, i) == None{} : Maybe<&2, A>}
  {L.edit(~A, ~E, ~ea, L.Update{i, d}, xs) == xs : List<&2, A>}

# Mapping
# -------

# LAW: mapping the empty list gives the empty list.
law map_nil:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  {L.map(~A, ~B, ~f, Nil{}) == Nil{} : List<&2, B>}

# LAW: mapping h <> t gives f(h) <> map(t).
law map_con:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for h: A
  for t: List<&2, A>
  {L.map(~A, ~B, ~f, h <> t) == f(h) <> L.map(~A, ~B, ~f, t) : List<&2, B>}

# The derivative of map
# ---------------------
# map.change carries inserts and deletes over, and updates the same
# position by df, a derivative of f.

# LAW: map.change is correct, if df is.
law map_change:
  for ~A: Data
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~eb: F -> B -> B
  for ~f: A -> B
  for ~df: A -> C.Change<A, E> -> C.Change<B, F>
  for ~df_ok: (@x: A -> @d: C.Change<A, E> -> {C.apply(~B, ~F, ~eb, df(x, d), f(x)) == f(C.apply(~A, ~E, ~ea, d, x)) : B})
  for d: C.Change<List<&2, A>, L.Edit<A, E>>
  for +xs: List<&2, A>
  {L.patch(~B, ~F, ~eb, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, d, xs), L.map(~A, ~B, ~f, xs)) == L.map(~A, ~B, ~f, L.patch(~A, ~E, ~ea, d, xs)) : List<&2, B>}

# LAW: map.change is local: it acts exactly where the change acts.
law map_change_local:
  for ~A: Data
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~f: A -> B
  for ~df: A -> C.Change<A, E> -> C.Change<B, F>
  for d: C.Change<List<&2, A>, L.Edit<A, E>>
  for +xs: List<&2, A>
  {L.shape(~B, ~F, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, d, xs)) == L.shape(~A, ~E, d) : C.Shape<L.Where>}
