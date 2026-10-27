import Base

# Changes to any value. A type supplies its own edits and how to apply one;
# Change adds what every type has: no change, starting over with a new
# value, and one change then another.
type Change<-A: Data, -E: Data> is Data:
  Keep{}
  Replace{x: A}
  Edit{e: E}
  Then{first: Change<A, E>, next: Change<A, E>}

# The edits of a type that has none of its own: its values change only by
# replacement.
type Whole is Data:

def Whole.apply(~A: Data, e: Whole, a: A) -> A:
  match e:

# The value after a change, given how to apply one edit.
def apply(~A: Data, ~E: Data, ~edit: E -> A -> A, d: Change<A, E>, a: A) -> A:
  match d:
    case Keep{}:
      a
    case Replace{x}:
      x
    case Edit{e}:
      edit(e, a)
    case Then{p, q}:
      apply(~A, ~E, ~edit, q, apply(~A, ~E, ~edit, p, a))

# A derivative of f, lifted from single edits. `fe` gives the change one
# edit makes to f's result, from the value before the edit; lift gives the
# change any change makes. A replacement replaces the result.
def lift(~A: Data, ~E: Data, ~B: Data, ~F: Data, ~edit: E -> A -> A, ~f: A -> B,
  ~fe: A -> E -> Change<B, F>, d: Change<A, E>, +a: A) -> Change<B, F>:
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{f(x)}
    case Edit{e}:
      fe(a, e)
    case Then{+p, q}:
      Then{lift(~A, ~E, ~B, ~F, ~edit, ~f, ~fe, p, a),
        lift(~A, ~E, ~B, ~F, ~edit, ~f, ~fe, q, apply(~A, ~E, ~edit, p, a))}

# The derivative that recomputes: whatever the change, replace the result.
def recompute(~A: Data, ~E: Data, ~B: Data, ~F: Data, ~edit: E -> A -> A, ~f: A -> B,
  a: A, d: Change<A, E>) -> Change<B, F>:
  Replace{f(apply(~A, ~E, ~edit, d, a))}

# Where a change acts, with its values left out. S says where one edit
# acts.
type Shape<-S: Data> is Data:
  SKeep{}
  SReplace{}
  SEdit{s: S}
  SThen{first: Shape<S>, next: Shape<S>}

def shape(~A: Data, ~E: Data, ~S: Data, ~at: E -> S, d: Change<A, E>) -> Shape<S>:
  match d:
    case Keep{}:
      SKeep{}
    case Replace{x}:
      SReplace{}
    case Edit{e}:
      SEdit{at(e)}
    case Then{p, q}:
      SThen{shape(~A, ~E, ~S, ~at, p), shape(~A, ~E, ~S, ~at, q)}
