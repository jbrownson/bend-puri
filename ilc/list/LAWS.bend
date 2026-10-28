import Base
import ../change/change.bend as C
import ./list.bend as L

# What a list's changes promise; PROOF.bend proves it.

# Positions in range
# ------------------
# has(xs, i): i is one of xs's positions, from 0 up to but not including
# its length. gap(xs, i): i is one of its gaps, where an insert can go,
# from 0 up to and including its length. valid(d, xs): each edit's
# position is in range for the list it applies to, after d's new value if
# it has one. The laws below say nothing about changes that aren't valid.

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

def valid.edit(~ca: C.ChangeStructure, e: L.Edit.of(ca), +xs: List<&2, C.Value(ca)>) -> Data:
  match e:
    case L.Insert{i, x}:
      gap(C.Value(ca), xs, i)
    case L.Delete{i}:
      has(C.Value(ca), xs, i)
    case L.Update{i, u}:
      has(C.Value(ca), xs, i)

def valid.edits(~ca: C.ChangeStructure, es: List<&2, L.Edit.of(ca)>, +xs: List<&2, C.Value(ca)>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{+e, t}:
      valid.edit(~ca, e, xs) & valid.edits(~ca, t, L.edit(~ca, e, xs))

def valid(~ca: C.ChangeStructure, d: C.Change.of(L.structure(~ca)), +xs: List<&2, C.Value(ca)>) -> Type:
  match d:
    case C.Change{s, es}:
      valid.edits(~ca, es, C.start(List<&2, C.Value(ca)>, s, xs))

# Edits
# -----
# A list's elements change as ca says: a value that only changes whole by
# C.complete(~C.Whole.structure(~A)), a list by
# C.complete(~L.structure(~cb)). L.structure(ca) says how a list changes
# by one edit, L.Edit.of(ca); its completion adds keeping, replacing and
# one change then another. List.take(xs, i) is the first i elements,
# List.drop(xs, i) the rest, and List.get(xs, i) the element at i, or None
# past the end.

# LAW: a list's edits are made of its elements' values and changes.
law edit_of:
  for -ca: C.ChangeStructure
  {L.Edit.of(ca) == L.Edit<C.Value(ca), C.Delta(ca)> : Data}

# LAW: a list changes by one edit as L.edit says.
law structure:
  for ~ca: C.ChangeStructure
  {L.structure(~ca) == C.ChangeStructure{List<&2, C.Value(ca)>, L.Edit.of(ca), e => xs => L.edit(~ca, e, xs)} : C.ChangeStructure}

# LAW: patching applies a list change, edit by edit.
law patch:
  for ~ca: C.ChangeStructure
  for d: C.Change.of(L.structure(~ca))
  for xs: List<&2, C.Value(ca)>
  {L.patch(~ca, d, xs) == C.apply(~L.structure(~ca), d, xs) : List<&2, C.Value(ca)>}

# LAW: inserting at i puts x before the element at i, or at the end.
law edit_insert:
  for ~ca: C.ChangeStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for x: C.Value(ca)
  for v: gap(C.Value(ca), xs, i)
  {L.edit(~ca, L.Insert{i, x}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), x <> List.drop(&2, C.Value(ca), xs, i)) : List<&2, C.Value(ca)>}

# LAW: deleting at i removes the element at i.
law edit_delete:
  for ~ca: C.ChangeStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for v: has(C.Value(ca), xs, i)
  {L.edit(~ca, L.Delete{i}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

# LAW: updating the element at i applies the change to it, in place.
law edit_update_inside:
  for ~ca: C.ChangeStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Delta(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.edit(~ca, L.Update{i, d}, xs) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), C.ChangeStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

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

# LAW: a list change's shape is the change with every value replaced by
# Unit{}: what remains is whether it starts over, and each edit's kind
# and position.
law shape:
  for ~ca: C.ChangeStructure
  for d: C.Change.of(L.structure(~ca))
  {L.shape(~ca, d) == C.map(~List<&2, C.Value(ca)>, ~L.Edit.of(ca), ~Unit, ~L.Edit<Unit, Unit>, ~(xs => Unit{}), ~(e => L.Edit.map(~C.Value(ca), ~C.Delta(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d) : C.Change<Unit, L.Edit<Unit, Unit>>}

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
# turns a change to the list into the change to the mapped list: it
# carries inserts and deletes over, and updates the same position by g's
# derivative.

# LAW: map.inc(g) maps g's function, with dmap for its derivative.
law map_inc:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  {L.map.inc(~ca, ~cb, ~g) == C.Inc{xs => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), xs => d => L.dmap(~ca, ~cb, ~g, d, xs)} : C.Inc<C.complete(~L.structure(~ca)), C.complete(~L.structure(~cb))>}

# LAW: keeping the list keeps the mapped list.
law dmap_keep:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.keep(L.structure(~ca)), xs) == C.keep(L.structure(~cb)) : C.Change.of(L.structure(~cb))}

# LAW: replacing the list replaces the mapped list, with the new list
# mapped.
law dmap_replace:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ys: List<&2, C.Value(ca)>
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.replace(L.structure(~ca), ys), xs) == C.replace(L.structure(~cb), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys)) : C.Change.of(L.structure(~cb))}

# LAW: inserting x inserts its image at the same position.
law dmap_insert:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for x: C.Value(ca)
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.edit(L.structure(~ca), L.Insert{i, x}), xs) == C.edit(L.structure(~cb), L.Insert{i, C.Inc.f(ca, cb, g)(x)}) : C.Change.of(L.structure(~cb))}

# LAW: deleting deletes at the same position.
law dmap_delete:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.edit(L.structure(~ca), L.Delete{i}), xs) == C.edit(L.structure(~cb), L.Delete{i}) : C.Change.of(L.structure(~cb))}

# LAW: updating the element x at i updates its image at i, by g's
# derivative.
law dmap_update_inside:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Delta(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.dmap(~ca, ~cb, ~g, C.edit(L.structure(~ca), L.Update{i, d}), xs) == C.edit(L.structure(~cb), L.Update{i, C.Inc.df(ca, cb, g)(x, d)}) : C.Change.of(L.structure(~cb))}

# LAW: one change then another maps the second from the list the first
# produced.
law dmap_then:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for p: C.Change.of(L.structure(~ca))
  for q: C.Change.of(L.structure(~ca))
  for +xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.then(L.structure(~ca), p, q), xs) == C.then(L.structure(~cb), L.dmap(~ca, ~cb, ~g, p, xs), L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs))) : C.Change.of(L.structure(~cb))}

# It follows that:

# LAW: map.inc(g) is correct, if g is.
law map_inc_ok:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  C.Inc.ok(C.complete(~L.structure(~ca)), C.complete(~L.structure(~cb)), L.map.inc(~ca, ~cb, ~g))

# LAW: dmap is local: it acts exactly where a valid change acts.
law dmap_local:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for d: C.Change.of(L.structure(~ca))
  for +xs: List<&2, C.Value(ca)>
  for v: valid(~ca, d, xs)
  {L.shape(~cb, L.dmap(~ca, ~cb, ~g, d, xs)) == L.shape(~ca, d) : C.Change<Unit, L.Edit<Unit, Unit>>}

# LAW: dmap keeps changes valid, if g is correct: a valid change gives one
# valid for the mapped list.
law dmap_valid:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for d: C.Change.of(L.structure(~ca))
  for +xs: List<&2, C.Value(ca)>
  for v: valid(~ca, d, xs)
  valid(~cb, L.dmap(~ca, ~cb, ~g, d, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
