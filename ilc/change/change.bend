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

# An incremental function: a function f, and its derivative df, which
# gives the change to f's result from a value and the value's change.
type Inc<-A: Data, -DA: Data, -B: Data, -DB: Data> is Type:
  Inc{f: A -> B, df: A -> DA -> DB}

def Inc.f(-A: Data, -DA: Data, -B: Data, -DB: Data, g: Inc<A, DA, B, DB>) -> A -> B:
  match g:
    case Inc{f, df}:
      f

def Inc.df(-A: Data, -DA: Data, -B: Data, -DB: Data, g: Inc<A, DA, B, DB>) -> A -> DA -> DB:
  match g:
    case Inc{f, df}:
      df

# g's derivative is correct, for changes applied by pa and pb: applying
# its change to f(a) gives f of the changed value.
def Inc.ok(-A: Data, -DA: Data, -B: Data, -DB: Data, pa: DA -> A -> A, pb: DB -> B -> B,
  g: Inc<A, DA, B, DB>) -> Type:
  @a: A -> @d: DA -> {pb(Inc.df(A, DA, B, DB, g)(a, d), Inc.f(A, DA, B, DB, g)(a)) == Inc.f(A, DA, B, DB, g)(pa(d, a)) : B}

# The derivative lift builds from g's: one edit is g's, a replacement
# replaces the result, and one change then another lifts the second from
# the value the first produced.
def lift.df(~A: Data, ~EA: Data, ~B: Data, ~EB: Data, ~ea: EA -> A -> A,
  ~g: Inc<A, EA, B, Change<B, EB>>, d: Change<A, EA>, +a: A) -> Change<B, EB>:
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{Inc.f(A, EA, B, Change<B, EB>, g)(x)}
    case Edit{e}:
      Inc.df(A, EA, B, Change<B, EB>, g)(a, e)
    case Then{+p, q}:
      Then{lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, p, a),
        lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, q, apply(~A, ~EA, ~ea, p, a))}

# Lifts an incremental function whose derivative handles single edits to
# one whose derivative handles any change.
def lift(~A: Data, ~EA: Data, ~B: Data, ~EB: Data, ~ea: EA -> A -> A,
  ~g: Inc<A, EA, B, Change<B, EB>>) -> Inc<A, Change<A, EA>, B, Change<B, EB>>:
  Inc{Inc.f(A, EA, B, Change<B, EB>, g), a => d => lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, d, a)}

# f, with the derivative that recomputes: whatever the change, replace the
# result.
def recompute(~A: Data, ~DA: Data, ~B: Data, ~EB: Data, ~pa: DA -> A -> A, ~f: A -> B) ->
  Inc<A, DA, B, Change<B, EB>>:
  Inc{f, a => d => Replace{f(pa(d, a))}}

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
