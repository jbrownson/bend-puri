import Base

# How values are edited: values of type Value, edits of type Edit, and
# `apply`, which applies one. These are the edits a type supplies; they
# needn't get from every value to every other. runs and whole add ways to
# get further.
type EditStructure is Type:
  EditStructure{Value: Data, Edit: Data, apply: Edit -> Value -> Value}

def Value(c: EditStructure) -> Data:
  match c:
    case EditStructure{v, d, f}:
      v

def Edit(c: EditStructure) -> Data:
  match c:
    case EditStructure{v, d, f}:
      d

def EditStructure.apply(c: EditStructure) -> Edit(c) -> Value(c) -> Value(c):
  match c:
    case EditStructure{v, d, f}:
      f

# One edit gets from any value to any other.
def reaches(-ce: EditStructure) -> Type:
  @a: Value(ce) -> @b: Value(ce) -> &d: Edit(ce) -> {EditStructure.apply(ce)(d, a) == b : Value(ce)}

# A change structure: an edit structure, with the proof that one edit gets
# from any value to any other. reach is live rather than erased, so the
# proof counts as evidence and its edit can be used. Change structures are
# only passed as templates, so this costs nothing at runtime; revisit if
# one is ever built in a hot path.
type ChangeStructure is Type:
  ChangeStructure{structure: EditStructure, reach: reaches(structure)}

def ChangeStructure.structure(c: ChangeStructure) -> EditStructure:
  match c:
    case ChangeStructure{s, r}:
      s

# The edits of values that have none of their own.
def none(~A: Data) -> EditStructure:
  EditStructure{A, Empty, e => a => Empty.absurd(A, e)}

# The value a run of edits leaves, applied in order.
def run(~ce: EditStructure, es: List<&2, Edit(ce)>, a: Value(ce)) -> Value(ce):
  match es:
    case Nil{}:
      a
    case Con{e, t}:
      run(~ce, t, EditStructure.apply(ce)(e, a))

# Runs of ce's edits, applied in order: no edits leaves a value as it is,
# and one run then another is the two joined.
def runs(~ce: EditStructure) -> EditStructure:
  EditStructure{Value(ce), List<&2, Edit(ce)>, es => a => run(~ce, es, a)}

# Running joined runs runs the first, then the second.
def run_append(~ce: EditStructure, xs: List<&2, Edit(ce)>, ys: List<&2, Edit(ce)>, a: Value(ce)) ->
  {run(~ce, List.append(&2, Edit(ce), xs, ys), a) == run(~ce, ys, run(~ce, xs, a)) : Value(ce)}:
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      run_append(~ce, t, ys, EditStructure.apply(ce)(e, a))

# An edit of a value: a whole new one, or one of its own edits.
type Whole<-ce: EditStructure> is Data:
  Replace{x: Value(ce)}
  Apply{e: Edit(ce)}

def whole.apply(~ce: EditStructure, w: Whole<ce>, a: Value(ce)) -> Value(ce):
  match w:
    case Replace{x}:
      x
    case Apply{e}:
      EditStructure.apply(ce)(e, a)

# ce's edits, and replacing the whole value.
def whole(~ce: EditStructure) -> EditStructure:
  EditStructure{Value(ce), Whole<ce>, w => a => whole.apply(~ce, w, a)}

# whole(ce), which is a change structure whatever ce is: replacing gets
# from any value to any other.
def whole.change_structure(~ce: EditStructure) -> ChangeStructure:
  ChangeStructure{whole(~ce), a => b => (Replace{b}, {==})}

# An incremental function, from values edited as ca says to values edited
# as cb says: a function f, and its derivative df, which gives the edit to
# f's result from a value and the value's edit.
type Inc<-ca: EditStructure, -cb: EditStructure> is Type:
  Inc{f: Value(ca) -> Value(cb), df: Value(ca) -> Edit(ca) -> Edit(cb)}

def Inc.f(-ca: EditStructure, -cb: EditStructure, g: Inc<ca, cb>) -> Value(ca) -> Value(cb):
  match g:
    case Inc{f, df}:
      f

def Inc.df(-ca: EditStructure, -cb: EditStructure, g: Inc<ca, cb>) -> Value(ca) -> Edit(ca) -> Edit(cb):
  match g:
    case Inc{f, df}:
      df

# g's derivative is correct: applying its edit to f(a) gives f of the
# edited value.
def Inc.ok(-ca: EditStructure, -cb: EditStructure, g: Inc<ca, cb>) -> Type:
  @a: Value(ca) -> @d: Edit(ca) -> {EditStructure.apply(cb)(Inc.df(ca, cb, g)(a, d), Inc.f(ca, cb, g)(a)) == Inc.f(ca, cb, g)(EditStructure.apply(ca)(d, a)) : Value(cb)}

# lift's derivative, for a run of edits from the value before them: g's
# run for each edit, joined in order.
def lift.run(~ca: EditStructure, ~cb: EditStructure, ~g: Inc<ca, runs(~cb)>, es: List<&2, Edit(ca)>,
  +a: Value(ca)) -> List<&2, Edit(cb)>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      List.append(&2, Edit(cb), Inc.df(ca, runs(~cb), g)(a, e), lift.run(~ca, ~cb, ~g, t, EditStructure.apply(ca)(e, a)))

# Lifts g, whose derivative gives a run for one edit, to an Inc whose
# derivative handles runs.
def lift(~ca: EditStructure, ~cb: EditStructure, ~g: Inc<ca, runs(~cb)>) -> Inc<runs(~ca), runs(~cb)>:
  Inc{Inc.f(ca, runs(~cb), g), a => es => lift.run(~ca, ~cb, ~g, es, a)}

# whole.lift's derivative: replacing the input replaces the result with f
# of the new value, and an edit gives g's edit.
def whole.lift.df(~ca: EditStructure, ~cb: EditStructure, ~g: Inc<ca, cb>, w: Whole<ca>,
  a: Value(ca)) -> Whole<cb>:
  match w:
    case Replace{x}:
      Replace{Inc.f(ca, cb, g)(x)}
    case Apply{e}:
      Apply{Inc.df(ca, cb, g)(a, e)}

# Lifts g to values that can also be replaced.
def whole.lift(~ca: EditStructure, ~cb: EditStructure, ~g: Inc<ca, cb>) -> Inc<whole(~ca), whole(~cb)>:
  Inc{Inc.f(ca, cb, g), a => w => whole.lift.df(~ca, ~cb, ~g, w, a)}

# f, with the derivative that recomputes: whatever the edit, replace the
# result.
def recompute(~ca: EditStructure, ~cb: EditStructure, ~f: Value(ca) -> Value(cb)) -> Inc<ca, whole(~cb)>:
  Inc{f, a => e => Replace{f(EditStructure.apply(ca)(e, a))}}

# Edits mapped by fe, in order.
def map.edits(~EA: Data, ~EB: Data, ~fe: EA -> EB, es: List<&2, EA>) -> List<&2, EB>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      fe(e) <> map.edits(~EA, ~EB, ~fe, t)
