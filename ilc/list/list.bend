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
def Edit.of(-ca: C.EditStructure) -> Data:
  Edit<C.Value(ca), C.Edit(ca)>

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

def update(~ca: C.EditStructure, xs: List<&2, C.Value(ca)>, i: Nat, d: C.Edit(ca)) -> List<&2, C.Value(ca)>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      C.EditStructure.apply(ca)(d, h) <> t
    case Con{h, t} 1n+p:
      h <> update(~ca, t, p, d)

# The list after one edit.
def edit(~ca: C.EditStructure, e: Edit.of(ca), xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  match e:
    case Insert{i, x}:
      insert(C.Value(ca), xs, i, x)
    case Delete{i}:
      remove(C.Value(ca), xs, i)
    case Update{i, d}:
      update(~ca, xs, i, d)

# A list's edit structure, given how its elements are edited: one edit at
# a time, which is not a change structure. C.complete(~edit_structure(~ca))
# makes one, adding keeping, replacing and one change then another.
def edit_structure(~ca: C.EditStructure) -> C.EditStructure:
  C.EditStructure{List<&2, C.Value(ca)>, Edit.of(ca), e => xs => edit(~ca, e, xs)}

# The list after a change.
def patch(~ca: C.EditStructure, d: C.Change.of(edit_structure(~ca)), xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  C.apply(~edit_structure(~ca), d, xs)

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The change an update at i makes to the mapped list, given the element
# at i: its image, updated by g's derivative. Past the end there is no
# element, and the update changes nothing.
def map.at(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, i: Nat, m: Maybe<&2, C.Value(ca)>,
  d: C.Edit(ca)) -> C.Change.of(edit_structure(~cb)):
  match m:
    case None{}:
      C.keep(edit_structure(~cb))
    case Some{x}:
      C.edit(edit_structure(~cb), Update{i, C.Inc.df(ca, cb, g)(x, d)})

# map's derivative for one edit, from the list before it: an insert or a
# delete carries over, and an update updates the same position by g's
# derivative.
def map.edit(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, xs: List<&2, C.Value(ca)>,
  e: Edit.of(ca)) -> C.Change.of(edit_structure(~cb)):
  match e:
    case Insert{i, x}:
      C.edit(edit_structure(~cb), Insert{i, C.Inc.f(ca, cb, g)(x)})
    case Delete{i}:
      C.edit(edit_structure(~cb), Delete{i})
    case Update{+i, d}:
      map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d)

# map's derivative: the change to the list g maps to, from the list and its
# change, lifted from map.edit.
def dmap(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, d: C.Change.of(edit_structure(~ca)), +xs: List<&2, C.Value(ca)>) ->
  C.Change.of(edit_structure(~cb)):
  C.lift.df(~edit_structure(~ca), ~edit_structure(~cb),
    ~C.Inc{ys => map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => map.edit(~ca, ~cb, ~g, ys, e)},
    d, xs)

# map, as an incremental function: g's function mapped over a list, with
# dmap as its derivative.
def map.inc(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>) -> C.Inc<C.complete(~edit_structure(~ca)), C.complete(~edit_structure(~cb))>:
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
def shape(~ca: C.EditStructure, d: C.Change.of(edit_structure(~ca))) -> C.Change<Unit, Edit<Unit, Unit>>:
  C.map(~List<&2, C.Value(ca)>, ~Edit.of(ca), ~Unit, ~Edit<Unit, Unit>, ~(xs => Unit{}),
    ~(e => Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d)
