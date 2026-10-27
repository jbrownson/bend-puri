import Base

# Changes to a list, and mapping a function over a list and over its
# changes. Positions count from 0. A position past the end inserts at the
# end, and deletes or sets nothing.

type Change<-A: Data> is Data:
  Keep{}
  Insert{at: Nat, x: A}
  Delete{at: Nat}
  Set{at: Nat, x: A}
  Replace{xs: List<&2, A>}
  Then{first: Change<A>, next: Change<A>}

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

def set(-A: Data, xs: List<&2, A>, i: Nat, x: A) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      x <> t
    case Con{h, t} 1n+p:
      h <> set(A, t, p, x)

# The list after a change.
def patch(-A: Data, dx: Change<A>, xs: List<&2, A>) -> List<&2, A>:
  match dx:
    case Keep{}:
      xs
    case Insert{i, x}:
      insert(A, xs, i, x)
    case Delete{i}:
      remove(A, xs, i)
    case Set{i, x}:
      set(A, xs, i, x)
    case Replace{ys}:
      ys
    case Then{a, b}:
      patch(A, b, patch(A, a, xs))

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The change to a mapped list, from the change to the list. It needs only
# the change, not the list, so it costs as much as the change does.
def map.change(~A: Data, ~B: Data, ~f: A -> B, dx: Change<A>) -> Change<B>:
  match dx:
    case Keep{}:
      Keep{}
    case Insert{i, x}:
      Insert{i, f(x)}
    case Delete{i}:
      Delete{i}
    case Set{i, x}:
      Set{i, f(x)}
    case Replace{ys}:
      Replace{map(~A, ~B, ~f, ys)}
    case Then{a, b}:
      Then{map.change(~A, ~B, ~f, a), map.change(~A, ~B, ~f, b)}

# Where a change acts, with its values left out: the positions it
# touches, and a replacement's length.
type Shape is Data:
  SKeep{}
  SInsert{at: Nat}
  SDelete{at: Nat}
  SSet{at: Nat}
  SReplace{length: Nat}
  SThen{first: Shape, next: Shape}

def shape(-A: Data, dx: Change<A>) -> Shape:
  match dx:
    case Keep{}:
      SKeep{}
    case Insert{i, x}:
      SInsert{i}
    case Delete{i}:
      SDelete{i}
    case Set{i, x}:
      SSet{i}
    case Replace{ys}:
      SReplace{List.length(&2, A, ys)}
    case Then{a, b}:
      SThen{shape(A, a), shape(A, b)}
