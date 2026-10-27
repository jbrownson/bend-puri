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

# Lists
# -----
# A list's elements change by any type DA, applied by `pa`: a whole value
# changes by C.Change<A, C.Whole> and C.apply, a list by a list change.
# List.take(xs, i) is the first i elements (all of them when i is past the
# end), List.drop(xs, i) the rest, and List.get(xs, i) the element at i, or
# None past the end.

# LAW: a list change is applied edit by edit.
law patch:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for d: C.Change<List<&2, A>, L.Edit<A, DA>>
  for xs: List<&2, A>
  {L.patch(~A, ~DA, ~pa, d, xs) == C.apply(~List<&2, A>, ~L.Edit<A, DA>, ~(e => ys => L.edit(~A, ~DA, ~pa, e, ys)), d, xs) : List<&2, A>}

# LAW: inserting at i puts x before the element at i, or at the end when i
# is past it.
law edit_insert:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.edit(~A, ~DA, ~pa, L.Insert{i, x}, xs) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, i)) : List<&2, A>}

# LAW: deleting at i removes the element at i, or nothing when i is past
# the end.
law edit_delete:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  {L.edit(~A, ~DA, ~pa, L.Delete{i}, xs) == List.append(&2, A, List.take(&2, A, xs, i), List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: updating the element at i applies the change to it, in place.
law edit_update_inside:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: DA
  for x: A
  for at: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.edit(~A, ~DA, ~pa, L.Update{i, d}, xs) == List.append(&2, A, List.take(&2, A, xs, i), pa(d, x) <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: updating past the end changes nothing.
law edit_update_outside:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: DA
  for past: {List.get(&2, A, xs, i) == None{} : Maybe<&2, A>}
  {L.edit(~A, ~DA, ~pa, L.Update{i, d}, xs) == xs : List<&2, A>}

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
# position by df, a derivative of f: it turns an element's change DA into
# its image's change DB, applied by `pb`. `kb` stands in for an update past
# the end, which changes nothing whatever it carries.

# LAW: map.change is correct, if df is.
law map_change:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~pb: DB -> B -> B
  for ~f: A -> B
  for ~df: A -> DA -> DB
  for ~kb: DB
  for ~df_ok: (@x: A -> @d: DA -> {pb(df(x, d), f(x)) == f(pa(d, x)) : B})
  for d: C.Change<List<&2, A>, L.Edit<A, DA>>
  for +xs: List<&2, A>
  {L.patch(~B, ~DB, ~pb, L.map.change(~A, ~DA, ~B, ~DB, ~pa, ~f, ~df, ~kb, d, xs), L.map(~A, ~B, ~f, xs)) == L.map(~A, ~B, ~f, L.patch(~A, ~DA, ~pa, d, xs)) : List<&2, B>}

# LAW: map.change is local: it acts exactly where the change acts.
law map_change_local:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~f: A -> B
  for ~df: A -> DA -> DB
  for ~kb: DB
  for d: C.Change<List<&2, A>, L.Edit<A, DA>>
  for +xs: List<&2, A>
  {L.shape(~B, ~DB, L.map.change(~A, ~DA, ~B, ~DB, ~pa, ~f, ~df, ~kb, d, xs)) == L.shape(~A, ~DA, d) : C.Shape<L.Where>}
