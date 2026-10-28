import Base
import ../change/change.bend as C

# A list's own edits, and mapping a function over a list and over its
# edits. Positions count from 0. The elements are edited as `ca` says, by
# edits of any kind, so an update changes an element in place.
# The laws cover edits whose positions are in range; past the end, these
# functions still give an answer (an insert appends, a delete or an update
# does nothing), which nothing relies on.

type Edit<-A: Data, -DA: Data> is Data:
  Insert{at: Nat, x: A}
  Delete{at: Nat}
  Update{at: Nat, d: DA}

# An edit of a list whose elements change as ca says.
def Edit.of(-ca: C.EditStructure) -> Data:
  Edit<C.Value(ca), C.Edit(ca)>

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

def update(~ca: C.EditStructure, xs: List<&2, C.Value(ca)>, i: Nat, d: C.Edit(ca)) -> List<&2, C.Value(ca)>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      C.EditStructure.apply(ca)(d, h) <> t
    case Con{h, t} 1n+p:
      h <> update(~ca, t, p, d)

# The list after one edit.
def edit(~ca: C.EditStructure, e: Edit.of(ca), xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  match e:
    case Insert{i, x}:
      insert(C.Value(ca), xs, i, x)
    case Delete{i}:
      remove(C.Value(ca), xs, i)
    case Update{i, d}:
      update(~ca, xs, i, d)

# A list's edit structure, given how its elements are edited: one edit at
# a time, which is not a change structure. Runs of them are; see
# change_structure.
def edit_structure(~ca: C.EditStructure) -> C.EditStructure:
  C.EditStructure{List<&2, C.Value(ca)>, Edit.of(ca), e => xs => edit(~ca, e, xs)}

# The list after a run of edits.
def patch(~ca: C.EditStructure, es: List<&2, Edit.of(ca)>, xs: List<&2, C.Value(ca)>) -> List<&2, C.Value(ca)>:
  C.run(~edit_structure(~ca), es, xs)

# Deletes every element of xs, front first.
def clear(~ca: C.EditStructure, xs: List<&2, C.Value(ca)>) -> List<&2, Edit.of(ca)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Delete{0n} <> clear(~ca, t)

# Builds ys from the empty list: its tail, then its head at the front.
def fill(~ca: C.EditStructure, ys: List<&2, C.Value(ca)>) -> List<&2, Edit.of(ca)>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      List.append(&2, Edit.of(ca), fill(~ca, t), [Insert{0n, y}])

# A run that gets from xs to ys: clear xs, then fill with ys.
def diff(~ca: C.EditStructure, xs: List<&2, C.Value(ca)>, ys: List<&2, C.Value(ca)>) -> List<&2, Edit.of(ca)>:
  List.append(&2, Edit.of(ca), clear(~ca, xs), fill(~ca, ys))

# Why diff gets there: clearing leaves nothing, inserting at 0 puts an
# element at the front, and filling the empty list builds ys.
def clear.ok(~ca: C.EditStructure, +xs: List<&2, C.Value(ca)>) ->
  {patch(~ca, clear(~ca, xs), xs) == Nil{} : List<&2, C.Value(ca)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      clear.ok(~ca, t)

def insert.front(-A: Data, t: List<&2, A>, y: A) -> {insert(A, t, 0n, y) == y <> t : List<&2, A>}:
  match t:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

def fill.ok(~ca: C.EditStructure, ys: List<&2, C.Value(ca)>) ->
  {patch(~ca, fill(~ca, ys), Nil{}) == ys : List<&2, C.Value(ca)>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(List<&2, C.Value(ca)>, patch(~ca, List.append(&2, Edit.of(ca), fill(~ca, t), [Insert{0n, y}]), Nil{}), patch(~ca, [Insert{0n, y}], patch(~ca, fill(~ca, t), Nil{})), C.run_append(~edit_structure(~ca), fill(~ca, t), [Insert{0n, y}], Nil{})) : {_ == y <> t : List<&2, C.Value(ca)>}
      %Equal.sym(List<&2, C.Value(ca)>, patch(~ca, fill(~ca, t), Nil{}), t, fill.ok(~ca, t)) : {patch(~ca, [Insert{0n, y}], _) == y <> t : List<&2, C.Value(ca)>}
      insert.front(C.Value(ca), t, y)

def diff.ok(~ca: C.EditStructure, +xs: List<&2, C.Value(ca)>, +ys: List<&2, C.Value(ca)>) ->
  {patch(~ca, diff(~ca, xs, ys), xs) == ys : List<&2, C.Value(ca)>}:
  %Equal.sym(List<&2, C.Value(ca)>, patch(~ca, diff(~ca, xs, ys), xs), patch(~ca, fill(~ca, ys), patch(~ca, clear(~ca, xs), xs)), C.run_append(~edit_structure(~ca), clear(~ca, xs), fill(~ca, ys), xs)) : {_ == ys : List<&2, C.Value(ca)>}
  %Equal.sym(List<&2, C.Value(ca)>, patch(~ca, clear(~ca, xs), xs), Nil{}, clear.ok(~ca, xs)) : {patch(~ca, fill(~ca, ys), _) == ys : List<&2, C.Value(ca)>}
  fill.ok(~ca, ys)

def diff.reach(~ca: C.EditStructure, +xs: List<&2, C.Value(ca)>, +ys: List<&2, C.Value(ca)>) ->
  &es: List<&2, Edit.of(ca)> -> {patch(~ca, es, xs) == ys : List<&2, C.Value(ca)>}:
  (diff(~ca, xs, ys), diff.ok(~ca, xs, ys))

# A list's change structure: runs of its edits, which get from any list
# to any other by diff.
def change_structure(~ca: C.EditStructure) -> C.ChangeStructure:
  C.ChangeStructure{C.runs(~edit_structure(~ca)), xs => ys => diff.reach(~ca, xs, ys)}

def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> map(~A, ~B, ~f, t)

# The edits an update at i makes to the mapped list, given the element at
# i: an update of its image by g's derivative. Past the end there is no
# element, and no edits.
def map.at(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, i: Nat, m: Maybe<&2, C.Value(ca)>,
  d: C.Edit(ca)) -> List<&2, Edit.of(cb)>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [Update{i, C.Inc.df(ca, cb, g)(x, d)}]

# map's derivative for one edit, from the list before it: an insert or a
# delete carries over, and an update updates the same position by g's
# derivative.
def map.edit(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, xs: List<&2, C.Value(ca)>,
  e: Edit.of(ca)) -> List<&2, Edit.of(cb)>:
  match e:
    case Insert{i, x}:
      [Insert{i, C.Inc.f(ca, cb, g)(x)}]
    case Delete{i}:
      [Delete{i}]
    case Update{+i, d}:
      map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d)

# map's derivative: the edits to the list g maps to, from the list and a
# run of its edits, lifted from map.edit.
def dmap(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, es: List<&2, Edit.of(ca)>, +xs: List<&2, C.Value(ca)>) ->
  List<&2, Edit.of(cb)>:
  C.lift.run(~edit_structure(~ca), ~edit_structure(~cb),
    ~C.Inc{ys => map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => map.edit(~ca, ~cb, ~g, ys, e)},
    es, xs)

# map, as an incremental function: g's function mapped over a list, with
# dmap as its derivative.
def map.inc(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>) -> C.Inc<C.runs(~edit_structure(~ca)), C.runs(~edit_structure(~cb))>:
  C.Inc{xs => map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), xs => es => dmap(~ca, ~cb, ~g, es, xs)}

# An edit with its element mapped by fa and its element's edit by fd.
def Edit.map(~A: Data, ~DA: Data, ~B: Data, ~DB: Data, ~fa: A -> B, ~fd: DA -> DB,
  e: Edit<A, DA>) -> Edit<B, DB>:
  match e:
    case Insert{i, x}:
      Insert{i, fa(x)}
    case Delete{i}:
      Delete{i}
    case Update{i, d}:
      Update{i, fd(d)}

# Where a run of edits acts: the edits with their values left out.
def shape(~ca: C.EditStructure, es: List<&2, Edit.of(ca)>) -> List<&2, Edit<Unit, Unit>>:
  C.map.edits(~Edit.of(ca), ~Edit<Unit, Unit>,
    ~(e => Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), es)
