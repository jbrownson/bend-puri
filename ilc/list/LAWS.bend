import Base
import ../change/change.bend as C
import ./list.bend as L

# What a list's edits promise; PROOF.bend proves it.

# Positions in range
# ------------------
# has(xs, i): i is one of xs's positions, from 0 up to but not including
# its length. gap(xs, i): i is one of its gaps, where an insert can go,
# from 0 up to and including its length. valid(es, xs): each edit's
# position is in range for the list it applies to. The laws below say
# nothing about edits that aren't valid.

def has(-A: Data, xs: List<&2, A>, i: Nat) -> Data:
  match xs i:
    case Nil{} _:
      Empty
    case Con{h, t} 0n:
      Unit
    case Con{h, t} 1n+p:
      has(A, t, p)

def gap(-A: Data, xs: List<&2, A>, i: Nat) -> Data:
  match xs i:
    case Nil{} 0n:
      Unit
    case Nil{} 1n+p:
      Empty
    case Con{h, t} 0n:
      Unit
    case Con{h, t} 1n+p:
      gap(A, t, p)

def valid.edit(~ca: C.EditStructure, e: L.Edit.of(ca), +xs: List<&2, C.Value(ca)>) -> Data:
  match e:
    case L.Insert{i, x}:
      gap(C.Value(ca), xs, i)
    case L.Delete{i}:
      has(C.Value(ca), xs, i)
    case L.Update{i, u}:
      has(C.Value(ca), xs, i)

def valid(~ca: C.EditStructure, es: List<&2, L.Edit.of(ca)>, +xs: List<&2, C.Value(ca)>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{+e, t}:
      valid.edit(~ca, e, xs) & valid(~ca, t, L.edit(~ca, e, xs))

# Edits
# -----
# A list's elements are edited as ca says: a value that only changes
# whole by C.whole(~C.none(~A)), a list by C.runs(~L.edit_structure(~cb)).
# L.edit_structure(ca) is a list's own edit structure, one L.Edit.of(ca)
# at a time, which isn't a change structure; runs of them are, without
# replacing. List.take(xs, i) is the first i elements, List.drop(xs, i)
# the rest, and List.get(xs, i) the element at i, or None past the end.

# LAW: a list's edits are made of its elements' values and edits.
law edit_of:
  for -ca: C.EditStructure
  {L.Edit.of(ca) == L.Edit<C.Value(ca), C.Edit(ca)> : Data}

# LAW: a list changes by one edit as L.edit says.
law edit_structure:
  for ~ca: C.EditStructure
  {L.edit_structure(~ca) == C.EditStructure{List<&2, C.Value(ca)>, L.Edit.of(ca), e => xs => L.edit(~ca, e, xs)} : C.EditStructure}

# LAW: patching applies a run of edits, in order.
law patch:
  for ~ca: C.EditStructure
  for es: List<&2, L.Edit.of(ca)>
  for xs: List<&2, C.Value(ca)>
  {L.patch(~ca, es, xs) == C.run(~L.edit_structure(~ca), es, xs) : List<&2, C.Value(ca)>}

# LAW: inserting at i puts x before the element at i, or at the end.
law edit_insert:
  for ~ca: C.EditStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for x: C.Value(ca)
  for v: gap(C.Value(ca), xs, i)
  {L.edit(~ca, L.Insert{i, x}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), x <> List.drop(&2, C.Value(ca), xs, i)) : List<&2, C.Value(ca)>}

# LAW: deleting at i removes the element at i.
law edit_delete:
  for ~ca: C.EditStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for v: has(C.Value(ca), xs, i)
  {L.edit(~ca, L.Delete{i}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

# LAW: updating the element at i applies the edit to it, in place.
law edit_update_inside:
  for ~ca: C.EditStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Edit(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.edit(~ca, L.Update{i, d}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), C.EditStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

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

# LAW: mapping an update maps the element's edit.
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

# LAW: a run's shape is its edits with every value replaced by Unit{}:
# what remains is each edit's kind and position.
law shape:
  for ~ca: C.EditStructure
  for es: List<&2, L.Edit.of(ca)>
  {L.shape(~ca, es) == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), es) : List<&2, L.Edit<Unit, Unit>>}

# Getting from any list to any other
# ----------------------------------
# One edit can't get from any list to any other, but a run can: diff
# clears the list, then fills it with the other.

# LAW: a list's own edits are not a change structure, if it has elements
# at all: no one edit gets from the empty list to a list of two, so they
# don't reach.
law edits_not_change_structure:
  for ~ca: C.EditStructure
  for +x: C.Value(ca)
  for h: C.reaches(L.edit_structure(~ca))
  Empty

# LAW: diff clears xs, then fills with ys.
law diff:
  for ~ca: C.EditStructure
  for xs: List<&2, C.Value(ca)>
  for ys: List<&2, C.Value(ca)>
  {L.diff(~ca, xs, ys) == List.append(&2, L.Edit.of(ca), L.clear(~ca, xs), L.fill(~ca, ys)) : List<&2, L.Edit.of(ca)>}

# LAW: a list's change structure is runs of its edits.
law change_structure:
  for ~ca: C.EditStructure
  {C.ChangeStructure.structure(L.change_structure(~ca)) == C.runs(~L.edit_structure(~ca)) : C.EditStructure}

# It follows that:

# LAW: diff gets from xs to ys.
law diff_ok:
  for ~ca: C.EditStructure
  for +xs: List<&2, C.Value(ca)>
  for +ys: List<&2, C.Value(ca)>
  {L.patch(~ca, L.diff(~ca, xs, ys), xs) == ys : List<&2, C.Value(ca)>}

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
# g is an Inc<ca, cb>: a function on elements and its derivative.
# map.inc(g) maps g's function over a list, and its derivative, dmap,
# turns a run of edits to the list into a run of edits to the mapped list:
# it carries inserts and deletes over, and updates the same position by
# g's derivative.

# LAW: map.inc(g) maps g's function, with dmap for its derivative.
law map_inc:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  {L.map.inc(~ca, ~cb, ~g) == C.Inc{xs => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), xs => es => L.dmap(~ca, ~cb, ~g, es, xs)} : C.Inc<C.runs(~L.edit_structure(~ca)), C.runs(~L.edit_structure(~cb))>}

# LAW: no edits give no edits.
law dmap_nil:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, Nil{}, xs) == Nil{} : List<&2, L.Edit.of(cb)>}

# LAW: inserting x inserts its image at the same position.
law dmap_insert:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for x: C.Value(ca)
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, [L.Insert{i, x}], xs) == [L.Insert{i, C.Inc.f(ca, cb, g)(x)}] : List<&2, L.Edit.of(cb)>}

# LAW: deleting deletes at the same position.
law dmap_delete:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, [L.Delete{i}], xs) == [L.Delete{i}] : List<&2, L.Edit.of(cb)>}

# LAW: updating the element x at i updates its image at i, by g's
# derivative.
law dmap_update_inside:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Edit(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.dmap(~ca, ~cb, ~g, [L.Update{i, d}], xs) == [L.Update{i, C.Inc.df(ca, cb, g)(x, d)}] : List<&2, L.Edit.of(cb)>}

# LAW: one run then another maps the second from the list the first
# produced.
law dmap_append:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for +p: List<&2, L.Edit.of(ca)>
  for +q: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, List.append(&2, L.Edit.of(ca), p, q), xs) == List.append(&2, L.Edit.of(cb), L.dmap(~ca, ~cb, ~g, p, xs), L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs))) : List<&2, L.Edit.of(cb)>}

# It follows that:

# LAW: map.inc(g) is correct, if g is.
law map_inc_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  C.Inc.ok(C.runs(~L.edit_structure(~ca)), C.runs(~L.edit_structure(~cb)), L.map.inc(~ca, ~cb, ~g))

# LAW: dmap is local: it acts exactly where valid edits act.
law dmap_local:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for es: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  for v: valid(~ca, es, xs)
  {L.shape(~cb, L.dmap(~ca, ~cb, ~g, es, xs)) == L.shape(~ca, es) : List<&2, L.Edit<Unit, Unit>>}

# LAW: dmap keeps edits valid, if g is correct: valid edits give edits
# valid for the mapped list.
law dmap_valid:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for es: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  for v: valid(~ca, es, xs)
  valid(~cb, L.dmap(~ca, ~cb, ~g, es, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
