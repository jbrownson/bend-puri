import Base

# A change structure: values of type Value change by changes of type
# Delta, and `apply` applies one. The theory's change structures also
# have a change that does nothing, a change between any two values, and
# composition; Change below adds those.
type ChangeStructure is Type:
  ChangeStructure{Value: Data, Delta: Data, apply: Delta -> Value -> Value}

def Value(c: ChangeStructure) -> Data:
  match c:
    case ChangeStructure{v, d, f}:
      v

def Delta(c: ChangeStructure) -> Data:
  match c:
    case ChangeStructure{v, d, f}:
      d

def ChangeStructure.apply(c: ChangeStructure) -> Delta(c) -> Value(c) -> Value(c):
  match c:
    case ChangeStructure{v, d, f}:
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
def Change.of(-ce: ChangeStructure) -> Data:
  Change<Value(ce), Delta(ce)>

# The edits of a type that has none of its own: its values change only by
# replacement.
type Whole is Data:

def Whole.apply(~A: Data, e: Whole, a: A) -> A:
  match e:

def Whole.structure(~A: Data) -> ChangeStructure:
  ChangeStructure{A, Whole, e => a => Whole.apply(~A, e, a)}

# The value after a change, given how its edits apply.
def apply(~ce: ChangeStructure, d: Change.of(ce), a: Value(ce)) -> Value(ce):
  match d:
    case Keep{}:
      a
    case Replace{x}:
      x
    case Edit{e}:
      ChangeStructure.apply(ce)(e, a)
    case Then{p, q}:
      apply(~ce, q, apply(~ce, p, a))

# How a Change of ce's edits changes values.
def Change.structure(~ce: ChangeStructure) -> ChangeStructure:
  ChangeStructure{Value(ce), Change.of(ce), d => a => apply(~ce, d, a)}

# An incremental function, from values that change as ca says to values
# that change as cb says: a function f, and its derivative df, which gives
# the change to f's result from a value and the value's change.
type Inc<-ca: ChangeStructure, -cb: ChangeStructure> is Type:
  Inc{f: Value(ca) -> Value(cb), df: Value(ca) -> Delta(ca) -> Delta(cb)}

def Inc.f(-ca: ChangeStructure, -cb: ChangeStructure, g: Inc<ca, cb>) -> Value(ca) -> Value(cb):
  match g:
    case Inc{f, df}:
      f

def Inc.df(-ca: ChangeStructure, -cb: ChangeStructure, g: Inc<ca, cb>) -> Value(ca) -> Delta(ca) -> Delta(cb):
  match g:
    case Inc{f, df}:
      df

# g's derivative is correct: applying its change to f(a) gives f of the
# changed value.
def Inc.ok(-ca: ChangeStructure, -cb: ChangeStructure, g: Inc<ca, cb>) -> Type:
  @a: Value(ca) -> @d: Delta(ca) -> {ChangeStructure.apply(cb)(Inc.df(ca, cb, g)(a, d), Inc.f(ca, cb, g)(a)) == Inc.f(ca, cb, g)(ChangeStructure.apply(ca)(d, a)) : Value(cb)}

# The derivative lift builds from g's: one edit is g's, a replacement
# replaces the result, and one change then another lifts the second from
# the value the first produced.
def lift.df(~ca: ChangeStructure, ~cb: ChangeStructure, ~g: Inc<ca, Change.structure(~cb)>, d: Change.of(ca), +a: Value(ca)) ->
  Change.of(cb):
  match d:
    case Keep{}:
      Keep{}
    case Replace{x}:
      Replace{Inc.f(ca, Change.structure(~cb), g)(x)}
    case Edit{e}:
      Inc.df(ca, Change.structure(~cb), g)(a, e)
    case Then{+p, q}:
      Then{lift.df(~ca, ~cb, ~g, p, a), lift.df(~ca, ~cb, ~g, q, apply(~ca, p, a))}

# Lifts g, whose derivative handles one edit as ca says, to an Inc whose
# derivative handles any change.
def lift(~ca: ChangeStructure, ~cb: ChangeStructure, ~g: Inc<ca, Change.structure(~cb)>) -> Inc<Change.structure(~ca), Change.structure(~cb)>:
  Inc{Inc.f(ca, Change.structure(~cb), g), a => d => lift.df(~ca, ~cb, ~g, d, a)}

# f, with the derivative that recomputes: whatever the change, replace the
# result.
def recompute(~ca: ChangeStructure, ~cb: ChangeStructure, ~f: Value(ca) -> Value(cb)) -> Inc<ca, Change.structure(~cb)>:
  Inc{f, a => d => Replace{f(ChangeStructure.apply(ca)(d, a))}}

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
