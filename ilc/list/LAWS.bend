import Base
import ../change/change.bend as C
import ./list.bend as L

# What a list's changes promise; PROOF.bend proves it.

# Positions in range
# ------------------
# has(xs, i): i is one of xs's positions, from 0 up to but not including
# its length. gap(xs, i): i is one of its gaps, where an insert can go,
# from 0 up to and including its length. valid(d, xs): each position in d
# is in range for the list it applies to. The laws below say nothing about
# changes that aren't valid.

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

def valid(~ca: C.ChangeStructure, d: L.Change.of(ca), +xs: List<&2, C.Value(ca)>) -> Type:
  match d:
    case C.Keep{}:
      Unit
    case C.Replace{ys}:
      Unit
    case C.Edit{e}:
      match e:
        case L.Insert{i, x}:
          gap(C.Value(ca), xs, i)
        case L.Delete{i}:
          has(C.Value(ca), xs, i)
        case L.Update{i, u}:
          has(C.Value(ca), xs, i)
    case C.Then{+p, q}:
      valid(~ca, p, xs) & valid(~ca, q, L.patch(~ca, p, xs))

# Edits
# -----
# A list's elements change as ca says: a value that only changes whole by
# C.Change.structure(~C.Whole.structure(~A)), a list by
# L.Change.structure(~cb). L.Edit.of(ca) and L.Change.of(ca) are a list's
# edits and changes when its elements change as ca says. List.take(xs, i)
# is the first i elements, List.drop(xs, i) the rest, and List.get(xs, i)
# the element at i, or None past the end.

# LAW: a list's edits are made of its elements' values and changes.
law edit_of:
  for -ca: C.ChangeStructure
  {L.Edit.of(ca) == L.Edit<C.Value(ca), C.Delta(ca)> : Data}

# LAW: its changes are Changes of lists, made of its edits.
law change_of:
  for -ca: C.ChangeStructure
  {L.Change.of(ca) == C.Change<List<&2, C.Value(ca)>, L.Edit.of(ca)> : Data}

# LAW: a list changes by one edit as L.edit says.
law edit_structure:
  for ~ca: C.ChangeStructure
  {L.Edit.structure(~ca) == C.ChangeStructure{List<&2, C.Value(ca)>, L.Edit.of(ca), e => xs => L.edit(~ca, e, xs)} : C.ChangeStructure}

# LAW: a list changes by a change as Change says, with a list's edits.
law change_structure:
  for ~ca: C.ChangeStructure
  {L.Change.structure(~ca) == C.Change.structure(~L.Edit.structure(~ca)) : C.ChangeStructure}

# LAW: patching applies a list change, edit by edit.
law patch:
  for ~ca: C.ChangeStructure
  for d: L.Change.of(ca)
  for xs: List<&2, C.Value(ca)>
  {L.patch(~ca, d, xs) == C.apply(~L.Edit.structure(~ca), d, xs) : List<&2, C.Value(ca)>}

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
# Unit{}: what remains is each edit's kind and position.
law shape:
  for ~ca: C.ChangeStructure
  for d: L.Change.of(ca)
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
  {L.map.inc(~ca, ~cb, ~g) == C.Inc{xs => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), xs => d => L.dmap(~ca, ~cb, ~g, d, xs)} : C.Inc<L.Change.structure(~ca), L.Change.structure(~cb)>}

# LAW: keeping the list keeps the mapped list.
law dmap_keep:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.Keep{}, xs) == C.Keep{} : L.Change.of(cb)}

# LAW: replacing the list replaces the mapped list, with the new list
# mapped.
law dmap_replace:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ys: List<&2, C.Value(ca)>
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.Replace{ys}, xs) == C.Replace{L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys)} : L.Change.of(cb)}

# LAW: inserting x inserts its image at the same position.
law dmap_insert:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for x: C.Value(ca)
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.Edit{L.Insert{i, x}}, xs) == C.Edit{L.Insert{i, C.Inc.f(ca, cb, g)(x)}} : L.Change.of(cb)}

# LAW: deleting deletes at the same position.
law dmap_delete:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.Edit{L.Delete{i}}, xs) == C.Edit{L.Delete{i}} : L.Change.of(cb)}

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
  {L.dmap(~ca, ~cb, ~g, C.Edit{L.Update{i, d}}, xs) == C.Edit{L.Update{i, C.Inc.df(ca, cb, g)(x, d)}} : L.Change.of(cb)}

# LAW: one change then another maps the second from the list the first
# produced.
law dmap_then:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for p: L.Change.of(ca)
  for q: L.Change.of(ca)
  for +xs: List<&2, C.Value(ca)>
  {L.dmap(~ca, ~cb, ~g, C.Then{p, q}, xs) == C.Then{L.dmap(~ca, ~cb, ~g, p, xs), L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs))} : L.Change.of(cb)}

# It follows that:

# LAW: map.inc(g) is correct, if g is.
law map_inc_ok:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  C.Inc.ok(L.Change.structure(~ca), L.Change.structure(~cb), L.map.inc(~ca, ~cb, ~g))

# LAW: dmap is local: it acts exactly where a valid change acts.
law dmap_local:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for d: L.Change.of(ca)
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
  for d: L.Change.of(ca)
  for +xs: List<&2, C.Value(ca)>
  for v: valid(~ca, d, xs)
  valid(~cb, L.dmap(~ca, ~cb, ~g, d, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
