import Base
import ../change/change.bend as C
import ./list.bend as L

# What a list's changes promise; PROOF.bend proves it.

# Edits
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

# LAW: mapping an insert maps the inserted element.
law edit_map_insert:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~fa: A -> B
  for ~fd: DA -> DB
  for i: Nat
  for x: A
  {L.Edit.map(~A, ~DA, ~B, ~DB, ~fa, ~fd, L.Insert{i, x}) == L.Insert{i, fa(x)} : L.Edit<B, DB>}

# LAW: mapping a delete leaves it as it is.
law edit_map_delete:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~fa: A -> B
  for ~fd: DA -> DB
  for i: Nat
  {L.Edit.map(~A, ~DA, ~B, ~DB, ~fa, ~fd, L.Delete{i}) == L.Delete{i} : L.Edit<B, DB>}

# LAW: mapping an update maps the element's change.
law edit_map_update:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~fa: A -> B
  for ~fd: DA -> DB
  for i: Nat
  for d: DA
  {L.Edit.map(~A, ~DA, ~B, ~DB, ~fa, ~fd, L.Update{i, d}) == L.Update{i, fd(d)} : L.Edit<B, DB>}

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

# LAW: a list change's shape is the change with every value replaced by
# Unit{}: what remains is each edit's kind and position.
law shape:
  for ~A: Data
  for ~DA: Data
  for d: C.Change<List<&2, A>, L.Edit<A, DA>>
  {L.shape(~A, ~DA, d) == C.map(~List<&2, A>, ~L.Edit<A, DA>, ~Unit, ~L.Edit<Unit, Unit>, ~(xs => Unit{}), ~(e => L.Edit.map(~A, ~DA, ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d) : C.Change<Unit, L.Edit<Unit, Unit>>}

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
  {L.shape(~B, ~DB, L.map.change(~A, ~DA, ~B, ~DB, ~pa, ~f, ~df, ~kb, d, xs)) == L.shape(~A, ~DA, d) : C.Change<Unit, L.Edit<Unit, Unit>>}
