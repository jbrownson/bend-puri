import Base
import ./change.bend as C

# A list's own edits, and mapping a function over a list and over its
# changes. Positions count from 0. E is the element type's edits, so an
# update changes an element in place. A position past the end inserts at
# the end, and deletes or updates nothing.

type Edit<-A: Data, -E: Data> is Data:
  Insert{at: Nat, x: A}
  Delete{at: Nat}
  Update{at: Nat, d: C.Change<A, E>}

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

def update(~A: Data, ~E: Data, ~edit: E -> A -> A, xs: List<&2, A>, i: Nat, d: C.Change<A, E>) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      C.apply(~A, ~E, ~edit, d, h) <> t
    case Con{h, t} 1n+p:
      h <> update(~A, ~E, ~edit, t, p, d)

# The list after one edit, given how to apply the elements' edits.
def edit(~A: Data, ~E: Data, ~ea: E -> A -> A, e: Edit<A, E>, xs: List<&2, A>) -> List<&2, A>:
  match e:
    case Insert{i, x}:
      insert(A, xs, i, x)
    case Delete{i}:
      remove(A, xs, i)
    case Update{i, d}:
      update(~A, ~E, ~ea, xs, i, d)

# The list after a change: Change's apply, with a list's edits.
def patch(~A: Data, ~E: Data, ~ea: E -> A -> A, d: C.Change<List<&2, A>, Edit<A, E>>, xs: List<&2, A>) -> List<&2, A>:
  C.apply(~List<&2, A>, ~Edit<A, E>, ~(e => ys => edit(~A, ~E, ~ea, e, ys)), d, xs)

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The change to the image of the element at a position, from f's
# derivative df; nothing where the list has no element.
def map.at(~A: Data, ~E: Data, ~B: Data, ~F: Data, ~df: A -> C.Change<A, E> -> C.Change<B, F>,
  m: Maybe<&2, A>, d: C.Change<A, E>) -> C.Change<B, F>:
  match m:
    case None{}:
      C.Keep{}
    case Some{x}:
      df(x, d)

# map's derivative for one edit, from the list before it: an insert or a
# delete carries over, and an update updates the same position by f's
# derivative.
def map.edit(~A: Data, ~E: Data, ~B: Data, ~F: Data, ~f: A -> B, ~df: A -> C.Change<A, E> -> C.Change<B, F>,
  xs: List<&2, A>, e: Edit<A, E>) -> C.Change<List<&2, B>, Edit<B, F>>:
  match e:
    case Insert{i, x}:
      C.Edit{Insert{i, f(x)}}
    case Delete{i}:
      C.Edit{Delete{i}}
    case Update{+i, d}:
      C.Edit{Update{i, map.at(~A, ~E, ~B, ~F, ~df, List.get(&2, A, xs, i), d)}}

# map's derivative: the change to the mapped list, from the list and its
# change, lifted from map.edit.
def map.change(~A: Data, ~E: Data, ~B: Data, ~F: Data, ~ea: E -> A -> A, ~f: A -> B,
  ~df: A -> C.Change<A, E> -> C.Change<B, F>, d: C.Change<List<&2, A>, Edit<A, E>>, +xs: List<&2, A>) ->
  C.Change<List<&2, B>, Edit<B, F>>:
  C.lift(~List<&2, A>, ~Edit<A, E>, ~List<&2, B>, ~Edit<B, F>, ~(e => ys => edit(~A, ~E, ~ea, e, ys)),
    ~(ys => map(~A, ~B, ~f, ys)), ~(ys => e => map.edit(~A, ~E, ~B, ~F, ~f, ~df, ys, e)), d, xs)

# Where one edit acts.
type Where is Data:
  AtInsert{at: Nat}
  AtDelete{at: Nat}
  AtUpdate{at: Nat}

def place(~A: Data, ~E: Data, e: Edit<A, E>) -> Where:
  match e:
    case Insert{i, x}:
      AtInsert{i}
    case Delete{i}:
      AtDelete{i}
    case Update{i, d}:
      AtUpdate{i}

# Where a list change acts.
def shape(~A: Data, ~E: Data, d: C.Change<List<&2, A>, Edit<A, E>>) -> C.Shape<Where>:
  C.shape(~List<&2, A>, ~Edit<A, E>, ~Where, ~(e => place(~A, ~E, e)), d)
