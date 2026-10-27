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
def lift(~A: Data, ~EA: Data, ~B: Data, ~EB: Data, ~ea: EA -> A -> A, ~f: A -> B,
  ~fe: A -> EA -> Change<B, EB>, d: Change<A, EA>, +a: A) -> Change<B, EB>:
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{f(x)}
    case Edit{e}:
      fe(a, e)
    case Then{+p, q}:
      Then{lift(~A, ~EA, ~B, ~EB, ~ea, ~f, ~fe, p, a),
        lift(~A, ~EA, ~B, ~EB, ~ea, ~f, ~fe, q, apply(~A, ~EA, ~ea, p, a))}

# The derivative that recomputes: whatever the change, replace the result.
# The input's changes DA can be of any type, applied by `pa`.
def recompute(~A: Data, ~DA: Data, ~B: Data, ~EB: Data, ~pa: DA -> A -> A, ~f: A -> B,
  a: A, d: DA) -> Change<B, EB>:
  Replace{f(pa(d, a))}

# A change with its values mapped by fa and its edits by fe: the same
# changes, in the same order.
def map(~A: Data, ~EA: Data, ~B: Data, ~EB: Data, ~fa: A -> B, ~fe: EA -> EB,
  d: Change<A, EA>) -> Change<B, EB>:
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{fa(x)}
    case Edit{e}:
      Edit{fe(e)}
    case Then{p, q}:
      Then{map(~A, ~EA, ~B, ~EB, ~fa, ~fe, p), map(~A, ~EA, ~B, ~EB, ~fa, ~fe, q)}
