import Base
import ../change/change.bend as C

# A list's own edits, and mapping a function over a list and over its
# changes. Positions count from 0. The elements change as `ca` says, by
# changes of any kind, so an update changes an element in place.
# The laws cover changes whose positions are in range; past the end, these
# functions still give an answer (an insert appends, a delete or an update
# does nothing), which nothing relies on.

type Edit<-A: Data, -DA: Data> is Data:
  Insert{at: Nat, x: A}
  Delete{at: Nat}
  Update{at: Nat, d: DA}

# An edit of a list whose elements change as ca says.
def Edit.of(-ca: C.ChangeStructure) -> Data:
  Edit<C.Value(ca), C.Delta(ca)>

# A change to a list whose elements change as ca says.
def Change.of(-ca: C.ChangeStructure) -> Data:
  C.Change<List<&2, C.Value(ca)>, Edit.of(ca)>

def insert(-A: Data, xs: List<&2, A>, i: Nat, x: A) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      [x]
    case Con{h, t} 0n:
      x <> h <> t
    case Con{h, t} 1n+p:
      h <> insert(A, t, p, x)

def remove(-A: Data, xs: List<&2, A>, i: Nat) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      t
    case Con{h, t} 1n+p:
      h <> remove(A, t, p)

def update(~ca: C.ChangeStructure, xs: List<&2, C.Value(ca)>, i: Nat, d: C.Delta(ca)) -> List<&2, C.Value(ca)>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      C.ChangeStructure.apply(ca)(d, h) <> t
    case Con{h, t} 1n+p:
      h <> update(~ca, t, p, d)

# The list after one edit.
def edit(~ca: C.ChangeStructure, e: Edit.of(ca), xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  match e:
    case Insert{i, x}:
      insert(C.Value(ca), xs, i, x)
    case Delete{i}:
      remove(C.Value(ca), xs, i)
    case Update{i, d}:
      update(~ca, xs, i, d)

# How a list changes by one edit, given how its elements change.
def Edit.structure(~ca: C.ChangeStructure) -> C.ChangeStructure:
  C.ChangeStructure{List<&2, C.Value(ca)>, Edit.of(ca), e => xs => edit(~ca, e, xs)}

# How a list changes by a change: Change's apply, with a list's edits.
def Change.structure(~ca: C.ChangeStructure) -> C.ChangeStructure:
  C.Change.structure(~Edit.structure(~ca))

# The list after a change.
def patch(~ca: C.ChangeStructure, d: Change.of(ca), xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  C.apply(~Edit.structure(~ca), d, xs)

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The change an update at i makes to the mapped list, given the element
# at i: its image, updated by g's derivative. Past the end there is no
# element, and the update changes nothing.
def map.at(~ca: C.ChangeStructure, ~cb: C.ChangeStructure, ~g: C.Inc<ca, cb>, i: Nat, m: Maybe<&2, C.Value(ca)>,
  d: C.Delta(ca)) -> Change.of(cb):
  match m:
    case None{}:
      C.Keep{}
    case Some{x}:
      C.Edit{Update{i, C.Inc.df(ca, cb, g)(x, d)}}

# map's derivative for one edit, from the list before it: an insert or a
# delete carries over, and an update updates the same position by g's
# derivative.
def map.edit(~ca: C.ChangeStructure, ~cb: C.ChangeStructure, ~g: C.Inc<ca, cb>, xs: List<&2, C.Value(ca)>,
  e: Edit.of(ca)) -> Change.of(cb):
  match e:
    case Insert{i, x}:
      C.Edit{Insert{i, C.Inc.f(ca, cb, g)(x)}}
    case Delete{i}:
      C.Edit{Delete{i}}
    case Update{+i, d}:
      map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d)

# map's derivative: the change to the list g maps to, from the list and its
# change, lifted from map.edit.
def dmap(~ca: C.ChangeStructure, ~cb: C.ChangeStructure, ~g: C.Inc<ca, cb>, d: Change.of(ca), +xs: List<&2, C.Value(ca)>) ->
  Change.of(cb):
  C.lift.df(~Edit.structure(~ca), ~Edit.structure(~cb),
    ~C.Inc{ys => map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => map.edit(~ca, ~cb, ~g, ys, e)},
    d, xs)

# map, as an incremental function: g's function mapped over a list, with
# dmap as its derivative.
def map.inc(~ca: C.ChangeStructure, ~cb: C.ChangeStructure, ~g: C.Inc<ca, cb>) -> C.Inc<Change.structure(~ca), Change.structure(~cb)>:
  C.Inc{xs => map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), xs => d => dmap(~ca, ~cb, ~g, d, xs)}

# An edit with its element mapped by fa and its element change by fd.
def Edit.map(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~fa: A -> B, ~fd: DA -> DB,
  e: Edit<A, DA>) -> Edit<B, DB>:
  match e:
    case Insert{i, x}:
      Insert{i, fa(x)}
    case Delete{i}:
      Delete{i}
    case Update{i, d}:
      Update{i, fd(d)}

# Where a list change acts: the change with its values left out.
def shape(~ca: C.ChangeStructure, d: Change.of(ca)) -> C.Change<Unit, Edit<Unit, Unit>>:
  C.map(~List<&2, C.Value(ca)>, ~Edit.of(ca), ~Unit, ~Edit<Unit, Unit>, ~(xs => Unit{}),
    ~(e => Edit.map(~C.Value(ca), ~C.Delta(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d)
