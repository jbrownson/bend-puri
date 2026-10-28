import Base

# How values are edited: values of type Value, edits of type Edit, and
# `apply`, which applies one. These are the edits a type supplies; they
# needn't get from every value to every other, include one that does
# nothing, or compose. C.complete adds those.
type Edits is Type:
  Edits{Value: Data, Edit: Data, apply: Edit -> Value -> Value}

def Value(c: Edits) -> Data:
  match c:
    case Edits{v, d, f}:
      v

def Edit(c: Edits) -> Data:
  match c:
    case Edits{v, d, f}:
      d

def Edits.apply(c: Edits) -> Edit(c) -> Value(c) -> Value(c):
  match c:
    case Edits{v, d, f}:
      f

# Edits are a change structure when one edit gets from any value to any
# other.
def ChangeStructure(-ce: Edits) -> Type:
  @a: Value(ce) -> @b: Value(ce) -> &d: Edit(ce) -> {Edits.apply(ce)(d, a) == b : Value(ce)}

# Changes to any value: a Change is a run of a type's edits, after an
# optional new value to start from. Changes make a change structure
# whatever the edits are: replace gets from any value to any other, keep
# (no new value, no edits) does nothing, and then composes two changes.
type Change<-A: Data, -E: Data> is Data:
  Change{start: Maybe<&2, A>, edits: List<&2, E>}

# The Change made of ce's edits.
def Change.of(-ce: Edits) -> Data:
  Change<Value(ce), Edit(ce)>

# No change.
def keep(-ce: Edits) -> Change.of(ce):
  Change{None{}, Nil{}}

# Starting over with x.
def replace(-ce: Edits, x: Value(ce)) -> Change.of(ce):
  Change{Some{x}, Nil{}}

# One edit.
def edit(-ce: Edits, e: Edit(ce)) -> Change.of(ce):
  Change{None{}, [e]}

# p, then q: q's edits after p's, unless q starts over, which discards p.
def then(-ce: Edits, p: Change.of(ce), q: Change.of(ce)) -> Change.of(ce):
  match p:
    case Change{ps, pes}:
      match q:
        case Change{qs, qes}:
          match qs:
            case Some{y}:
              Change{Some{y}, qes}
            case None{}:
              Change{ps, List.append(&2, Edit(ce), pes, qes)}

# The edits of values that have none of their own: they change only as a
# whole, by the replacement C.complete adds.
def whole(~A: Data) -> Edits:
  Edits{A, Empty, e => a => Empty.absurd(A, e)}

# The value a run of edits leaves, applied in order.
def run(~ce: Edits, es: List<&2, Edit(ce)>, a: Value(ce)) -> Value(ce):
  match es:
    case Nil{}:
      a
    case Con{e, t}:
      run(~ce, t, Edits.apply(ce)(e, a))

# The value a change starts from: its new value if it has one, else a.
def start(-A: Data, m: Maybe<&2, A>, a: A) -> A:
  match m:
    case None{}:
      a
    case Some{x}:
      x

# The value after a change, given how its edits apply.
def apply(~ce: Edits, d: Change.of(ce), a: Value(ce)) -> Value(ce):
  match d:
    case Change{s, es}:
      run(~ce, es, start(Value(ce), s, a))

# Completes ce into a change structure: its edits are Changes of ce's
# edits, which C.apply applies.
def complete(~ce: Edits) -> Edits:
  Edits{Value(ce), Change.of(ce), d => a => apply(~ce, d, a)}

# An incremental function, from values that change as ca says to values
# that change as cb says: a function f, and its derivative df, which gives
# the change to f's result from a value and the value's change.
type Inc<-ca: Edits, -cb: Edits> is Type:
  Inc{f: Value(ca) -> Value(cb), df: Value(ca) -> Edit(ca) -> Edit(cb)}

def Inc.f(-ca: Edits, -cb: Edits, g: Inc<ca, cb>) -> Value(ca) -> Value(cb):
  match g:
    case Inc{f, df}:
      f

def Inc.df(-ca: Edits, -cb: Edits, g: Inc<ca, cb>) -> Value(ca) -> Edit(ca) -> Edit(cb):
  match g:
    case Inc{f, df}:
      df

# g's derivative is correct: applying its change to f(a) gives f of the
# changed value.
def Inc.ok(-ca: Edits, -cb: Edits, g: Inc<ca, cb>) -> Type:
  @a: Value(ca) -> @d: Edit(ca) -> {Edits.apply(cb)(Inc.df(ca, cb, g)(a, d), Inc.f(ca, cb, g)(a)) == Inc.f(ca, cb, g)(Edits.apply(ca)(d, a)) : Value(cb)}

# The derivative lift builds from g's, for a run of edits from the value
# before them: each edit's change from g, one after another.
def lift.run(~ca: Edits, ~cb: Edits, ~g: Inc<ca, complete(~cb)>, es: List<&2, Edit(ca)>,
  +a: Value(ca)) -> Change.of(cb):
  match es:
    case Nil{}:
      keep(cb)
    case Con{+e, t}:
      then(cb, Inc.df(ca, complete(~cb), g)(a, e), lift.run(~ca, ~cb, ~g, t, Edits.apply(ca)(e, a)))

# lift's derivative: a new start replaces the result with f of the new
# value, and the edits follow from whichever value they start from.
def lift.df(~ca: Edits, ~cb: Edits, ~g: Inc<ca, complete(~cb)>, d: Change.of(ca), +a: Value(ca)) ->
  Change.of(cb):
  match d:
    case Change{s, es}:
      match s:
        case None{}:
          lift.run(~ca, ~cb, ~g, es, a)
        case Some{+x}:
          then(cb, replace(cb, Inc.f(ca, complete(~cb), g)(x)), lift.run(~ca, ~cb, ~g, es, x))

# Lifts g, whose derivative handles one edit as ca says, to an Inc whose
# derivative handles any change.
def lift(~ca: Edits, ~cb: Edits, ~g: Inc<ca, complete(~cb)>) -> Inc<complete(~ca), complete(~cb)>:
  Inc{Inc.f(ca, complete(~cb), g), a => d => lift.df(~ca, ~cb, ~g, d, a)}

# f, with the derivative that recomputes: whatever the change, replace the
# result.
def recompute(~ca: Edits, ~cb: Edits, ~f: Value(ca) -> Value(cb)) -> Inc<ca, complete(~cb)>:
  Inc{f, a => d => replace(cb, f(Edits.apply(ca)(d, a)))}

# A change's new value mapped by fa, if it has one.
def map.start(~A: Data, ~B: Data, ~fa: A -> B, m: Maybe<&2, A>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{fa(x)}

# Edits mapped by fe, in order.
def map.edits(~EA: Data, ~EB: Data, ~fe: EA -> EB, es: List<&2, EA>) -> List<&2, EB>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      fe(e) <> map.edits(~EA, ~EB, ~fe, t)

# A change with its new value mapped by fa and its edits by fe: the same
# changes, in the same order.
def map(~A: Data, ~EA: Data, ~B: Data, ~EB: Data, ~fa: A -> B, ~fe: EA -> EB,
  d: Change<A, EA>) -> Change<B, EB>:
  match d:
    case Change{s, es}:
      Change{map.start(~A, ~B, ~fa, s), map.edits(~EA, ~EB, ~fe, es)}
