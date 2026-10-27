import Base
import ../change/change.bend as C

# A list's own edits, and mapping a function over a list and over its
# changes. Positions count from 0. DA is the elements' change type, of any
# kind, and `pa` applies one, so an update changes an element in place. A
# position past the end inserts at the end, and deletes or updates nothing.

type Edit<-A: Data, -DA: Data> is Data:
  Insert{at: Nat, x: A}
  Delete{at: Nat}
  Update{at: Nat, d: DA}

# A change to a list whose elements change by DA.
def Change(-A: Data, -DA: Data) -> Data:
  C.Change<List<&2, A>, Edit<A, DA>>

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

def update(~A: Data, ~DA: Data, ~pa: DA -> A -> A, xs: List<&2, A>, i: Nat, d: DA) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      pa(d, h) <> t
    case Con{h, t} 1n+p:
      h <> update(~A, ~DA, ~pa, t, p, d)

# The list after one edit.
def edit(~A: Data, ~DA: Data, ~pa: DA -> A -> A, e: Edit<A, DA>, xs: List<&2, A>) -> List<&2, A>:
  match e:
    case Insert{i, x}:
      insert(A, xs, i, x)
    case Delete{i}:
      remove(A, xs, i)
    case Update{i, d}:
      update(~A, ~DA, ~pa, xs, i, d)

# The list after a change: Change's apply, with a list's edits.
def patch(~A: Data, ~DA: Data, ~pa: DA -> A -> A, d: Change(A, DA), xs: List<&2, A>) -> List<&2, A>:
  C.apply(~List<&2, A>, ~Edit<A, DA>, ~(e => ys => edit(~A, ~DA, ~pa, e, ys)), d, xs)

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The change to the image of the element at a position, from g's
# derivative. Where the list has no element the update changes nothing,
# so any change of B will do: `kb`.
def map.at(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~g: C.Inc<A, DA, B, DB>, ~kb: DB,
  m: Maybe<&2, A>, d: DA) -> DB:
  match m:
    case None{}:
      kb
    case Some{x}:
      C.Inc.df(A, DA, B, DB, g)(x, d)

# map's derivative for one edit, from the list before it: an insert or a
# delete carries over, and an update updates the same position by g's
# derivative.
def map.edit(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~g: C.Inc<A, DA, B, DB>, ~kb: DB,
  xs: List<&2, A>, e: Edit<A, DA>) -> Change(B, DB):
  match e:
    case Insert{i, x}:
      C.Edit{Insert{i, C.Inc.f(A, DA, B, DB, g)(x)}}
    case Delete{i}:
      C.Edit{Delete{i}}
    case Update{+i, d}:
      C.Edit{Update{i, map.at(~A, ~DA, ~B, ~DB, ~g, ~kb, List.get(&2, A, xs, i), d)}}

# map's derivative: the change to the list g maps to, from the list and its
# change, lifted from map.edit.
def dmap(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~pa: DA -> A -> A, ~g: C.Inc<A, DA, B, DB>,
  ~kb: DB, d: Change(A, DA), +xs: List<&2, A>) -> Change(B, DB):
  C.lift.df(~List<&2, A>, ~Edit<A, DA>, ~List<&2, B>, ~Edit<B, DB>, ~(e => ys => edit(~A, ~DA, ~pa, e, ys)),
    ~C.Inc{ys => map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), ys), ys => e => map.edit(~A, ~DA, ~B, ~DB, ~g, ~kb, ys, e)},
    d, xs)

# map, as an incremental function: g's function mapped over a list, with
# dmap as its derivative.
def map.inc(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~pa: DA -> A -> A, ~g: C.Inc<A, DA, B, DB>,
  ~kb: DB) -> C.Inc<List<&2, A>, Change(A, DA), List<&2, B>, Change(B, DB)>:
  C.Inc{xs => map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs), xs => d => dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, ~kb, d, xs)}

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
def shape(~A: Data, ~DA: Data, d: Change(A, DA)) -> C.Change<Unit, Edit<Unit, Unit>>:
  C.map(~List<&2, A>, ~Edit<A, DA>, ~Unit, ~Edit<Unit, Unit>, ~(xs => Unit{}),
    ~(e => Edit.map(~A, ~DA, ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), d)
