import Base

# How values change: values of type Value change by changes of type Delta,
# and `apply` applies one. This is only the apply part of what the theory
# calls a change structure; Change below adds the rest.
type Changes is Type:
  Changes{Value: Data, Delta: Data, apply: Delta -> Value -> Value}

def Value(c: Changes) -> Data:
  match c:
    case Changes{v, d, f}:
      v

def Delta(c: Changes) -> Data:
  match c:
    case Changes{v, d, f}:
      d

def Changes.apply(c: Changes) -> Delta(c) -> Value(c) -> Value(c):
  match c:
    case Changes{v, d, f}:
      f

# Changes to any value. A type supplies its own edits, and how one
# applies; Change adds what every type has: no change, starting over with
# a new value, and one change then another. Those make it a full change
# structure: a change that does nothing, a change from any value to any
# other, and composition.
type Change<-A: Data, -E: Data> is Data:
  Keep{}
  Replace{x: A}
  Edit{e: E}
  Then{first: Change<A, E>, next: Change<A, E>}

# The Change made of ce's edits.
def Change.of(-ce: Changes) -> Data:
  Change<Value(ce), Delta(ce)>

# The edits of a type that has none of its own: its values change only by
# replacement.
type Whole is Data:

def Whole.apply(~A: Data, e: Whole, a: A) -> A:
  match e:

def Whole.changes(~A: Data) -> Changes:
  Changes{A, Whole, e => a => Whole.apply(~A, e, a)}

# The value after a change, given how its edits apply.
def apply(~ce: Changes, d: Change.of(ce), a: Value(ce)) -> Value(ce):
  match d:
    case Keep{}:
      a
    case Replace{x}:
      x
    case Edit{e}:
      Changes.apply(ce)(e, a)
    case Then{p, q}:
      apply(~ce, q, apply(~ce, p, a))

# How a Change of ce's edits changes values.
def changes(~ce: Changes) -> Changes:
  Changes{Value(ce), Change.of(ce), d => a => apply(~ce, d, a)}

# An incremental function, from values that change as ca says to values
# that change as cb says: a function f, and its derivative df, which gives
# the change to f's result from a value and the value's change.
type Inc<-ca: Changes, -cb: Changes> is Type:
  Inc{f: Value(ca) -> Value(cb), df: Value(ca) -> Delta(ca) -> Delta(cb)}

def Inc.f(-ca: Changes, -cb: Changes, g: Inc<ca, cb>) -> Value(ca) -> Value(cb):
  match g:
    case Inc{f, df}:
      f

def Inc.df(-ca: Changes, -cb: Changes, g: Inc<ca, cb>) -> Value(ca) -> Delta(ca) -> Delta(cb):
  match g:
    case Inc{f, df}:
      df

# g's derivative is correct: applying its change to f(a) gives f of the
# changed value.
def Inc.ok(-ca: Changes, -cb: Changes, g: Inc<ca, cb>) -> Type:
  @a: Value(ca) -> @d: Delta(ca) -> {Changes.apply(cb)(Inc.df(ca, cb, g)(a, d), Inc.f(ca, cb, g)(a)) == Inc.f(ca, cb, g)(Changes.apply(ca)(d, a)) : Value(cb)}

# The derivative lift builds from g's: one edit is g's, a replacement
# replaces the result, and one change then another lifts the second from
# the value the first produced.
def lift.df(~ca: Changes, ~cb: Changes, ~g: Inc<ca, changes(~cb)>, d: Change.of(ca), +a: Value(ca)) ->
  Change.of(cb):
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{Inc.f(ca, changes(~cb), g)(x)}
    case Edit{e}:
      Inc.df(ca, changes(~cb), g)(a, e)
    case Then{+p, q}:
      Then{lift.df(~ca, ~cb, ~g, p, a), lift.df(~ca, ~cb, ~g, q, apply(~ca, p, a))}

# Lifts g, whose derivative handles one edit as ca says, to an Inc whose
# derivative handles any change.
def lift(~ca: Changes, ~cb: Changes, ~g: Inc<ca, changes(~cb)>) -> Inc<changes(~ca), changes(~cb)>:
  Inc{Inc.f(ca, changes(~cb), g), a => d => lift.df(~ca, ~cb, ~g, d, a)}

# f, with the derivative that recomputes: whatever the change, replace the
# result.
def recompute(~ca: Changes, ~cb: Changes, ~f: Value(ca) -> Value(cb)) -> Inc<ca, changes(~cb)>:
  Inc{f, a => d => Replace{f(Changes.apply(ca)(d, a))}}

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
