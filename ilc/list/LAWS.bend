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

def valid(~A: Data, ~DA: Data, ~pa: DA -> A -> A, d: L.Change(A, DA), +xs: List<&2, A>) -> Type:
  match d:
    case C.Keep{}:
      Unit
    case C.Replace{ys}:
      Unit
    case C.Edit{e}:
      match e:
        case L.Insert{i, x}:
          gap(A, xs, i)
        case L.Delete{i}:
          has(A, xs, i)
        case L.Update{i, u}:
          has(A, xs, i)
    case C.Then{+p, q}:
      valid(~A, ~DA, ~pa, p, xs) & valid(~A, ~DA, ~pa, q, L.patch(~A, ~DA, ~pa, p, xs))

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
  for d: L.Change(A, DA)
  for xs: List<&2, A>
  {L.patch(~A, ~DA, ~pa, d, xs) == C.apply(~List<&2, A>, ~L.Edit<A, DA>, ~(e => ys => L.edit(~A, ~DA, ~pa, e, ys)), d, xs) : List<&2, A>}

# LAW: inserting at i puts x before the element at i, or at the end.
law edit_insert:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for x: A
  for v: gap(A, xs, i)
  {L.edit(~A, ~DA, ~pa, L.Insert{i, x}, xs) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, i)) : List<&2, A>}

# LAW: deleting at i removes the element at i.
law edit_delete:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for v: has(A, xs, i)
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
  for ~A: Data
  for ~DA: Data
  for d: L.Change(A, DA)
  {L.shape(~A, ~DA, d) == C.map(~List<&2, A>, ~L.Edit<A, DA>, ~Unit, ~L.Edit<Unit, Unit>, ~(xs => Unit{}), ~(e => L.Edit.map(~A, ~DA, ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d) : C.Change<Unit, L.Edit<Unit, Unit>>}

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
# g is an Inc<A, DA, B, DB>: a function on elements and its derivative.
# map.inc(g) maps g's function over a list, and its derivative, dmap,
# turns a change to the list into the change to the mapped list: it
# carries inserts and deletes over, and updates the same position by g's
# derivative.

# LAW: map.inc(g) maps g's function, with dmap for its derivative.
law map_inc:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  {L.map.inc(~A, ~DA, ~B, ~DB, ~pa, ~g) == C.Inc{xs => L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs), xs => d => L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, d, xs)} : C.Inc<List<&2, A>, L.Change(A, DA), List<&2, B>, L.Change(B, DB)>}

# LAW: keeping the list keeps the mapped list.
law dmap_keep:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for xs: List<&2, A>
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Keep{}, xs) == C.Keep{} : L.Change(B, DB)}

# LAW: replacing the list replaces the mapped list, with the new list
# mapped.
law dmap_replace:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for ys: List<&2, A>
  for xs: List<&2, A>
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Replace{ys}, xs) == C.Replace{L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), ys)} : L.Change(B, DB)}

# LAW: inserting x inserts its image at the same position.
law dmap_insert:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for i: Nat
  for x: A
  for xs: List<&2, A>
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Edit{L.Insert{i, x}}, xs) == C.Edit{L.Insert{i, C.Inc.f(A, DA, B, DB, g)(x)}} : L.Change(B, DB)}

# LAW: deleting deletes at the same position.
law dmap_delete:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for i: Nat
  for xs: List<&2, A>
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Edit{L.Delete{i}}, xs) == C.Edit{L.Delete{i}} : L.Change(B, DB)}

# LAW: updating the element x at i updates its image at i, by g's
# derivative.
law dmap_update_inside:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for xs: List<&2, A>
  for i: Nat
  for d: DA
  for x: A
  for at: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Edit{L.Update{i, d}}, xs) == C.Edit{L.Update{i, C.Inc.df(A, DA, B, DB, g)(x, d)}} : L.Change(B, DB)}

# LAW: one change then another maps the second from the list the first
# produced.
law dmap_then:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for p: L.Change(A, DA)
  for q: L.Change(A, DA)
  for +xs: List<&2, A>
  {L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, C.Then{p, q}, xs) == C.Then{L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, p, xs), L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, q, L.patch(~A, ~DA, ~pa, p, xs))} : L.Change(B, DB)}

# It follows that:

# LAW: map.inc(g) is correct, if g is.
law map_inc_ok:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for ~g_ok: C.Inc.ok(A, DA, B, DB, pa, pb, g)
  C.Inc.ok(List<&2, A>, L.Change(A, DA), List<&2, B>, L.Change(B, DB), (d => xs => L.patch(~A, ~DA, ~pa, d, xs)), (d => ys => L.patch(~B, ~DB, ~pb, d, ys)), L.map.inc(~A, ~DA, ~B, ~DB, ~pa, ~g))

# LAW: dmap is local: it acts exactly where a valid change acts.
law dmap_local:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~g: C.Inc<A, DA, B, DB>
  for d: L.Change(A, DA)
  for +xs: List<&2, A>
  for v: valid(~A, ~DA, ~pa, d, xs)
  {L.shape(~B, ~DB, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, d, xs)) == L.shape(~A, ~DA, d) : C.Change<Unit, L.Edit<Unit, Unit>>}

# LAW: dmap keeps changes valid, if g is correct: a valid change gives one
# valid for the mapped list.
law dmap_valid:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for ~g_ok: C.Inc.ok(A, DA, B, DB, pa, pb, g)
  for d: L.Change(A, DA)
  for +xs: List<&2, A>
  for v: valid(~A, ~DA, ~pa, d, xs)
  valid(~B, ~DB, ~pb, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, d, xs), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs))
