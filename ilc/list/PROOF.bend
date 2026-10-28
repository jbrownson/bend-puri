import Base
import ../change/change.bend as C
import ./list.bend as L
import ./LAWS.bend as Laws
import ../change/LAWS.bend as CL
import ../change/PROOF.bend as CP

# Helpers
# -------

def Maybe.holds(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{v}:
      Unit

# Helper: something is not nothing.
law some_none:
  for -A: Data
  for -x: A
  for e: {Some{x} == None{} : Maybe<&2, A>}
  Empty

def some_none(A, x, e):
  %e : Maybe.holds(A, _)
  Unit{}

# Helper: dropping nothing gives the list back.
law drop_zero:
  for -A: Data
  for t: List<&2, A>
  {List.drop(&2, A, t, 0n) == t : List<&2, A>}

def drop_zero(A, t):
  match t:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

# Edits
# -----

def Laws.edit_of(ca):
  {==}

def Laws.edit_structure(ca):
  {==}

def at_most_one(-A: Data, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      match t:
        case Nil{}:
          Unit
        case Con{h2, t2}:
          Empty

# Lemma: one edit of the empty list leaves at most one element.
law edit_nil:
  for ~ca: C.EditStructure
  for e: L.Edit.of(ca)
  at_most_one(C.Value(ca), L.edit(~ca, e, Nil{}))

def edit_nil(ca, e):
  match e:
    case L.Insert{i, x}:
      Unit{}
    case L.Delete{i}:
      Unit{}
    case L.Update{i, d}:
      Unit{}

# Lemma: no one edit gets from the empty list to [x, x].
law edit_nil_two:
  for ~ca: C.EditStructure
  for -x: C.Value(ca)
  for r: &e: L.Edit.of(ca) -> {L.edit(~ca, e, Nil{}) == [x, x] : List<&2, C.Value(ca)>}
  Empty

def edit_nil_two(ca, x, r):
  match r:
    case (e, at):
      %at : at_most_one(C.Value(ca), _)
      edit_nil(~ca, e)

def Laws.edits_not_change_structure(ca, x, h):
  edit_nil_two(~ca, x, h(Nil{}, [x, x]))

# Deletes every element of xs, front first.
def clear(~ca: C.EditStructure, xs: List<&2, C.Value(ca)>) -> List<&2, L.Edit.of(ca)>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      L.Delete{0n} <> clear(~ca, t)

# Builds ys from the empty list: its tail, then its head at the front.
def fill(~ca: C.EditStructure, ys: List<&2, C.Value(ca)>) -> List<&2, L.Edit.of(ca)>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      List.append(&2, L.Edit.of(ca), fill(~ca, t), [L.Insert{0n, y}])

# Lemma: clearing a list leaves nothing.
law run_clear:
  for ~ca: C.EditStructure
  for +xs: List<&2, C.Value(ca)>
  {C.run(~L.edit_structure(~ca), clear(~ca, xs), xs) == Nil{} : List<&2, C.Value(ca)>}

def run_clear(ca, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      run_clear(~ca, t)

# Lemma: inserting at 0 puts y at the front.
law insert_front:
  for -A: Data
  for t: List<&2, A>
  for y: A
  {L.insert(A, t, 0n, y) == y <> t : List<&2, A>}

def insert_front(A, t, y):
  match t:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

# Lemma: filling the empty list with ys gives ys.
law run_fill:
  for ~ca: C.EditStructure
  for ys: List<&2, C.Value(ca)>
  {C.run(~L.edit_structure(~ca), fill(~ca, ys), Nil{}) == ys : List<&2, C.Value(ca)>}

def run_fill(ca, ys):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(List<&2, C.Value(ca)>, C.run(~L.edit_structure(~ca), List.append(&2, L.Edit.of(ca), fill(~ca, t), [L.Insert{0n, y}]), Nil{}), C.run(~L.edit_structure(~ca), [L.Insert{0n, y}], C.run(~L.edit_structure(~ca), fill(~ca, t), Nil{})), CP.run_append(~L.edit_structure(~ca), fill(~ca, t), [L.Insert{0n, y}], Nil{})) : {_ == y <> t : List<&2, C.Value(ca)>}
      %Equal.sym(List<&2, C.Value(ca)>, C.run(~L.edit_structure(~ca), fill(~ca, t), Nil{}), t, run_fill(~ca, t)) : {C.run(~L.edit_structure(~ca), [L.Insert{0n, y}], _) == y <> t : List<&2, C.Value(ca)>}
      insert_front(C.Value(ca), t, y)

# Lemma: clearing xs and then filling with ys gets from xs to ys.
law clear_fill:
  for ~ca: C.EditStructure
  for +xs: List<&2, C.Value(ca)>
  for +ys: List<&2, C.Value(ca)>
  {C.run(~L.edit_structure(~ca), List.append(&2, L.Edit.of(ca), clear(~ca, xs), fill(~ca, ys)), xs) == ys : List<&2, C.Value(ca)>}

def clear_fill(ca, xs, ys):
  %Equal.sym(List<&2, C.Value(ca)>, C.run(~L.edit_structure(~ca), List.append(&2, L.Edit.of(ca), clear(~ca, xs), fill(~ca, ys)), xs), C.run(~L.edit_structure(~ca), fill(~ca, ys), C.run(~L.edit_structure(~ca), clear(~ca, xs), xs)), CP.run_append(~L.edit_structure(~ca), clear(~ca, xs), fill(~ca, ys), xs)) : {_ == ys : List<&2, C.Value(ca)>}
  %Equal.sym(List<&2, C.Value(ca)>, C.run(~L.edit_structure(~ca), clear(~ca, xs), xs), Nil{}, run_clear(~ca, xs)) : {C.run(~L.edit_structure(~ca), fill(~ca, ys), _) == ys : List<&2, C.Value(ca)>}
  run_fill(~ca, ys)

# Lemma: one run gets from xs to ys.
law runs_reach_at:
  for ~ca: C.EditStructure
  for +xs: List<&2, C.Value(ca)>
  for +ys: List<&2, C.Value(ca)>
  exs es: List<&2, L.Edit.of(ca)>
  {C.run(~L.edit_structure(~ca), es, xs) == ys : List<&2, C.Value(ca)>}

def runs_reach_at(ca, xs, ys):
  (List.append(&2, L.Edit.of(ca), clear(~ca, xs), fill(~ca, ys)), clear_fill(~ca, xs, ys))

def Laws.runs_reach(ca):
  xs => ys => runs_reach_at(~ca, xs, ys)

def Laws.patch(ca, d, xs):
  {==}

# Lemma: insert puts x between the first i elements and the rest.
law insert_split:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.insert(A, xs, i, x) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, i)) : List<&2, A>}

def insert_split(A, xs, i, x):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.insert(A, t, p, x), List.append(&2, A, List.take(&2, A, t, p), x <> List.drop(&2, A, t, p)), insert_split(A, t, p, x)) : {h <> _ == h <> List.append(&2, A, List.take(&2, A, t, p), x <> List.drop(&2, A, t, p)) : List<&2, A>}
      {==}

# Lemma: remove joins the first i elements to what follows the one at i.
law remove_split:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  {L.remove(A, xs, i) == List.append(&2, A, List.take(&2, A, xs, i), List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

def remove_split(A, xs, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      Equal.sym(List<&2, A>, List.drop(&2, A, t, 0n), t, drop_zero(A, t))
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.remove(A, t, p), List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, 1n+p)), remove_split(A, t, p)) : {h <> _ == h <> List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, 1n+p)) : List<&2, A>}
      {==}

def Laws.edit_insert(ca, xs, i, x, v):
  insert_split(C.Value(ca), xs, i, x)

def Laws.edit_delete(ca, xs, i, v):
  remove_split(C.Value(ca), xs, i)

# Lemma: update at a position holding x puts the changed x in its place.
law update_inside:
  for ~ca: C.EditStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Edit(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.update(~ca, xs, i, d) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), C.EditStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

def update_inside(ca, xs, i, d, x, at):
  match xs i:
    case Nil{} _:
      Empty.absurd({L.update(~ca, Nil{}, i, d) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), Nil{}, i), C.EditStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), Nil{}, 1n+i)) : List<&2, C.Value(ca)>},
        some_none(C.Value(ca), x, Equal.sym(Maybe<&2, C.Value(ca)>, None{}, Some{x}, at)))
    case Con{h, t} 0n:
      %Equal.cong(Maybe<&2, C.Value(ca)>, C.Value(ca), m => Maybe.default(&2, C.Value(ca), m, h), Some{h}, Some{x}, at) : {C.EditStructure.apply(ca)(d, h) <> t == C.EditStructure.apply(ca)(d, _) <> List.drop(&2, C.Value(ca), t, 0n) : List<&2, C.Value(ca)>}
      %Equal.sym(List<&2, C.Value(ca)>, List.drop(&2, C.Value(ca), t, 0n), t, drop_zero(C.Value(ca), t)) : {C.EditStructure.apply(ca)(d, h) <> t == C.EditStructure.apply(ca)(d, h) <> _ : List<&2, C.Value(ca)>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, C.Value(ca)>, L.update(~ca, t, p, d), List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), t, p), C.EditStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), t, 1n+p)), update_inside(~ca, t, p, d, x, at)) : {h <> _ == h <> List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), t, p), C.EditStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), t, 1n+p)) : List<&2, C.Value(ca)>}
      {==}

def Laws.edit_update_inside(ca, xs, i, d, x, at):
  update_inside(~ca, xs, i, d, x, at)

def Laws.edit_map_insert(A, DA, B, DB, fa, fd, i, x):
  {==}

def Laws.edit_map_delete(A, DA, B, DB, fa, fd, i):
  {==}

def Laws.edit_map_update(A, DA, B, DB, fa, fd, i, d):
  {==}

def Laws.shape(ca, d):
  {==}

def Laws.map_nil(A, B, f):
  {==}

def Laws.map_con(A, B, f, h, t):
  {==}

# Positions in range
# ------------------

# Lemma: a position of a list holds an element.
law has_get:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for v: Laws.has(A, xs, i)
  Maybe.holds(A, List.get(&2, A, xs, i))

def has_get(A, xs, i, v):
  match xs i:
    case Nil{} _:
      v
    case Con{h, t} 0n:
      v
    case Con{h, t} 1n+p:
      has_get(A, t, p, v)

# Lemma: mapping keeps a list's positions.
law has_map:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  for v: Laws.has(A, xs, i)
  Laws.has(B, L.map(~A, ~B, ~f, xs), i)

def has_map(A, B, f, xs, i, v):
  match xs i:
    case Nil{} _:
      v
    case Con{h, t} 0n:
      v
    case Con{h, t} 1n+p:
      has_map(~A, ~B, ~f, t, p, v)

# Lemma: mapping keeps a list's gaps.
law gap_map:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  for v: Laws.gap(A, xs, i)
  Laws.gap(B, L.map(~A, ~B, ~f, xs), i)

def gap_map(A, B, f, xs, i, v):
  match xs i:
    case Nil{} 0n:
      v
    case Nil{} 1n+p:
      v
    case Con{h, t} 0n:
      v
    case Con{h, t} 1n+p:
      gap_map(~A, ~B, ~f, t, p, v)

# Lemma: edits valid for a list, then edits valid for the list they
# produce, are valid together.
law valid_append:
  for ~ca: C.EditStructure
  for es: List<&2, L.Edit.of(ca)>
  for fs: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  for v: Laws.valid.edits(~ca, es, xs)
  for w: Laws.valid.edits(~ca, fs, C.run(~L.edit_structure(~ca), es, xs))
  Laws.valid.edits(~ca, List.append(&2, L.Edit.of(ca), es, fs), xs)

def valid_append(ca, es, fs, xs, v, w):
  match es:
    case Nil{}:
      w
    case Con{+e, t}:
      (ve, vt) = v
      (ve, valid_append(~ca, t, fs, L.edit(~ca, e, xs), vt, w))

# Lemma: edits valid for a list are valid for an equal one.
law valid_eq:
  for ~ca: C.EditStructure
  for es: List<&2, L.Edit.of(ca)>
  for xs: List<&2, C.Value(ca)>
  for ys: List<&2, C.Value(ca)>
  for e: {xs == ys : List<&2, C.Value(ca)>}
  for v: Laws.valid.edits(~ca, es, ys)
  Laws.valid.edits(~ca, es, xs)

def valid_eq(ca, es, xs, ys, e, v):
  %Equal.sym(List<&2, C.Value(ca)>, xs, ys, e) : Laws.valid.edits(~ca, es, _)
  v

# The derivative of map
# ---------------------

# Lemma: mapping after an insert inserts the mapped element.
law map_insert:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.insert(B, L.map(~A, ~B, ~f, xs), i, f(x)) == L.map(~A, ~B, ~f, L.insert(A, xs, i, x)) : List<&2, B>}

def map_insert(A, B, f, xs, i, x):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.insert(B, L.map(~A, ~B, ~f, t), p, f(x)), L.map(~A, ~B, ~f, L.insert(A, t, p, x)), map_insert(~A, ~B, ~f, t, p, x)) : {f(h) <> _ == f(h) <> L.map(~A, ~B, ~f, L.insert(A, t, p, x)) : List<&2, B>}
      {==}

# Lemma: mapping after a delete deletes from the mapped list.
law map_remove:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  {L.remove(B, L.map(~A, ~B, ~f, xs), i) == L.map(~A, ~B, ~f, L.remove(A, xs, i)) : List<&2, B>}

def map_remove(A, B, f, xs, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.remove(B, L.map(~A, ~B, ~f, t), p), L.map(~A, ~B, ~f, L.remove(A, t, p)), map_remove(~A, ~B, ~f, t, p)) : {f(h) <> _ == f(h) <> L.map(~A, ~B, ~f, L.remove(A, t, p)) : List<&2, B>}
      {==}

# Lemma: an update one further along a longer list passes over its head.
law at_shift:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for p: Nat
  for m: Maybe<&2, C.Value(ca)>
  for d: C.Edit(ca)
  for y: C.Value(cb)
  for ys: List<&2, C.Value(cb)>
  {L.patch(~cb, L.map.at(~ca, ~cb, ~g, 1n+p, m, d), y <> ys) == y <> L.patch(~cb, L.map.at(~ca, ~cb, ~g, p, m, d), ys) : List<&2, C.Value(cb)>}

def at_shift(ca, cb, g, p, m, d, y, ys):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Lemma: mapping after an update updates the mapped element by g's
# derivative, if g is correct.
law map_update:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for +xs: List<&2, C.Value(ca)>
  for +i: Nat
  for +d: C.Edit(ca)
  {L.patch(~cb, L.map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) == L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, xs, i, d)) : List<&2, C.Value(cb)>}

def map_update(ca, cb, g, g_ok, xs, i, d):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %Equal.sym(C.Value(cb), C.EditStructure.apply(cb)(C.Inc.df(ca, cb, g)(h, d), C.Inc.f(ca, cb, g)(h)), C.Inc.f(ca, cb, g)(C.EditStructure.apply(ca)(d, h)), g_ok(h, d)) : {_ <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t) == C.Inc.f(ca, cb, g)(C.EditStructure.apply(ca)(d, h)) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t) : List<&2, C.Value(cb)>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, C.Value(cb)>, L.patch(~cb, L.map.at(~ca, ~cb, ~g, 1n+p, List.get(&2, C.Value(ca), t, p), d), C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), C.Inc.f(ca, cb, g)(h) <> L.patch(~cb, L.map.at(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), at_shift(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d, C.Inc.f(ca, cb, g)(h), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t))) : {_ == C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)) : List<&2, C.Value(cb)>}
      %Equal.sym(List<&2, C.Value(cb)>, L.patch(~cb, L.map.at(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)), map_update(~ca, ~cb, ~g, ~g_ok, t, p, d)) : {C.Inc.f(ca, cb, g)(h) <> _ == C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)) : List<&2, C.Value(cb)>}
      {==}

# Lemma: map.edit is correct for every single edit, if g is.
law map_edit_ok:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for xs: List<&2, C.Value(ca)>
  for e: L.Edit.of(ca)
  {L.patch(~cb, L.map.edit(~ca, ~cb, ~g, xs, e), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) == L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.edit(~ca, e, xs)) : List<&2, C.Value(cb)>}

def map_edit_ok(ca, cb, g, g_ok, xs, e):
  match e:
    case L.Insert{i, x}:
      map_insert(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, x)
    case L.Delete{i}:
      map_remove(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i)
    case L.Update{i, d}:
      map_update(~ca, ~cb, ~g, ~g_ok, xs, i, d)

# dmap's edits
# ------------
# dmap never starts over except where its change does, so what it
# produces is a run of edits: out(xs, e) for one edit, which map.edit
# gives, and out.run(es, xs) for a run.

def out.at(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, i: Nat, m: Maybe<&2, C.Value(ca)>,
  d: C.Edit(ca)) -> List<&2, L.Edit.of(cb)>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [L.Update{i, C.Inc.df(ca, cb, g)(x, d)}]

def out(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, xs: List<&2, C.Value(ca)>, e: L.Edit.of(ca)) ->
  List<&2, L.Edit.of(cb)>:
  match e:
    case L.Insert{i, x}:
      [L.Insert{i, C.Inc.f(ca, cb, g)(x)}]
    case L.Delete{i}:
      [L.Delete{i}]
    case L.Update{+i, d}:
      out.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d)

def out.run(~ca: C.EditStructure, ~cb: C.EditStructure, ~g: C.Inc<ca, cb>, es: List<&2, L.Edit.of(ca)>, +xs: List<&2, C.Value(ca)>) ->
  List<&2, L.Edit.of(cb)>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      List.append(&2, L.Edit.of(cb), out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))

# Lemma: an update's change to the mapped list is out.at's edits.
law at_out:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for m: Maybe<&2, C.Value(ca)>
  for d: C.Edit(ca)
  {L.map.at(~ca, ~cb, ~g, i, m, d) == C.Change{None{}, out.at(~ca, ~cb, ~g, i, m, d)} : C.Change.of(L.edit_structure(~cb))}

def at_out(ca, cb, g, i, m, d):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Lemma: map.edit's change is out's edits.
law edit_out:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  for e: L.Edit.of(ca)
  {L.map.edit(~ca, ~cb, ~g, xs, e) == C.Change{None{}, out(~ca, ~cb, ~g, xs, e)} : C.Change.of(L.edit_structure(~cb))}

def edit_out(ca, cb, g, xs, e):
  match e:
    case L.Insert{i, x}:
      {==}
    case L.Delete{i}:
      {==}
    case L.Update{+i, d}:
      at_out(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d)

# Lemma: dmap's change for a run of edits is out.run's edits.
law lift_run_out:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for es: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  {C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, es, xs) == C.Change{None{}, out.run(~ca, ~cb, ~g, es, xs)} : C.Change.of(L.edit_structure(~cb))}

def lift_run_out(ca, cb, g, es, xs):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(C.Change.of(L.edit_structure(~cb)), C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, t, L.edit(~ca, e, xs)), C.Change{None{}, out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs))}, lift_run_out(~ca, ~cb, ~g, t, L.edit(~ca, e, xs))) : {C.then(L.edit_structure(~cb), L.map.edit(~ca, ~cb, ~g, xs, e), _) == C.Change{None{}, List.append(&2, L.Edit.of(cb), out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))} : C.Change.of(L.edit_structure(~cb))}
      %Equal.sym(C.Change.of(L.edit_structure(~cb)), L.map.edit(~ca, ~cb, ~g, xs, e), C.Change{None{}, out(~ca, ~cb, ~g, xs, e)}, edit_out(~ca, ~cb, ~g, xs, e)) : {C.then(L.edit_structure(~cb), _, C.Change{None{}, out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs))}) == C.Change{None{}, List.append(&2, L.Edit.of(cb), out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))} : C.Change.of(L.edit_structure(~cb))}
      {==}

# Lemma: out's edits take the mapped list to the edited list, mapped, if
# g is correct.
law run_out:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for +xs: List<&2, C.Value(ca)>
  for +e: L.Edit.of(ca)
  {C.run(~L.edit_structure(~cb), out(~ca, ~cb, ~g, xs, e), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) == L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.edit(~ca, e, xs)) : List<&2, C.Value(cb)>}

def run_out(ca, cb, g, g_ok, xs, e):
  %edit_out(~ca, ~cb, ~g, xs, e) : {L.patch(~cb, _, L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) == L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.edit(~ca, e, xs)) : List<&2, C.Value(cb)>}
  map_edit_ok(~ca, ~cb, ~g, ~g_ok, xs, e)

# Lemma: mapping appended edits maps each part.
law map_edits_append:
  for ~EA: Data
  for ~EB: Data
  for ~fe: EA -> EB
  for es: List<&2, EA>
  for fs: List<&2, EA>
  {C.map.edits(~EA, ~EB, ~fe, List.append(&2, EA, es, fs)) == List.append(&2, EB, C.map.edits(~EA, ~EB, ~fe, es), C.map.edits(~EA, ~EB, ~fe, fs)) : List<&2, EB>}

def map_edits_append(EA, EB, fe, es, fs):
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      %Equal.sym(List<&2, EB>, C.map.edits(~EA, ~EB, ~fe, List.append(&2, EA, t, fs)), List.append(&2, EB, C.map.edits(~EA, ~EB, ~fe, t), C.map.edits(~EA, ~EB, ~fe, fs)), map_edits_append(~EA, ~EB, ~fe, t, fs)) : {fe(e) <> _ == fe(e) <> List.append(&2, EB, C.map.edits(~EA, ~EB, ~fe, t), C.map.edits(~EA, ~EB, ~fe, fs)) : List<&2, EB>}
      {==}

# Lemma: an update at a position holding an element maps to an update at
# the same position.
law at_shape:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for i: Nat
  for m: Maybe<&2, C.Value(ca)>
  for d: C.Edit(ca)
  for h: Maybe.holds(C.Value(ca), m)
  {C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.at(~ca, ~cb, ~g, i, m, d)) == [L.Update{i, Unit{}}] : List<&2, L.Edit<Unit, Unit>>}

def at_shape(ca, cb, g, i, m, d, h):
  match m:
    case None{}:
      match h:
    case Some{x}:
      {==}

# Lemma: a valid edit maps to one edit of the same kind at the same
# position.
law out_shape:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for +xs: List<&2, C.Value(ca)>
  for e: L.Edit.of(ca)
  for v: Laws.valid.edit(~ca, e, xs)
  {C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out(~ca, ~cb, ~g, xs, e)) == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), [e]) : List<&2, L.Edit<Unit, Unit>>}

def out_shape(ca, cb, g, xs, e, v):
  match e:
    case L.Insert{i, x}:
      {==}
    case L.Delete{i}:
      {==}
    case L.Update{+i, d}:
      at_shape(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d, has_get(C.Value(ca), xs, i, v))

# Lemma: valid edits map to edits of the same kinds at the same
# positions.
law shape_run:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for es: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  for v: Laws.valid.edits(~ca, es, xs)
  {C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, es, xs)) == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), es) : List<&2, L.Edit<Unit, Unit>>}

def shape_run(ca, cb, g, es, xs, v):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      (ve, vt) = v
      %Equal.sym(List<&2, L.Edit<Unit, Unit>>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), List.append(&2, L.Edit.of(cb), out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))), List.append(&2, L.Edit<Unit, Unit>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out(~ca, ~cb, ~g, xs, e)), C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))), map_edits_append(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))) : {_ == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), e <> t) : List<&2, L.Edit<Unit, Unit>>}
      %Equal.sym(List<&2, L.Edit<Unit, Unit>>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out(~ca, ~cb, ~g, xs, e)), C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), [e]), out_shape(~ca, ~cb, ~g, xs, e, ve)) : {List.append(&2, L.Edit<Unit, Unit>, _, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)))) == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), e <> t) : List<&2, L.Edit<Unit, Unit>>}
      %Equal.sym(List<&2, L.Edit<Unit, Unit>>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs))), C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), t), shape_run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs), vt)) : {List.append(&2, L.Edit<Unit, Unit>, C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), [e]), _) == C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), e <> t) : List<&2, L.Edit<Unit, Unit>>}
      {==}

# Lemma: an update at a position holding an element maps to an update
# valid for a list with that position.
law at_valid:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ys: List<&2, C.Value(cb)>
  for i: Nat
  for m: Maybe<&2, C.Value(ca)>
  for d: C.Edit(ca)
  for h: Maybe.holds(C.Value(ca), m)
  for w: Laws.has(C.Value(cb), ys, i)
  Laws.valid.edits(~cb, out.at(~ca, ~cb, ~g, i, m, d), ys)

def at_valid(ca, cb, g, ys, i, m, d, h, w):
  match m:
    case None{}:
      match h:
    case Some{x}:
      (w, Unit{})

# Lemma: a valid edit maps to edits valid for the mapped list.
law out_valid:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for +xs: List<&2, C.Value(ca)>
  for e: L.Edit.of(ca)
  for +v: Laws.valid.edit(~ca, e, xs)
  Laws.valid.edits(~cb, out(~ca, ~cb, ~g, xs, e), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))

def out_valid(ca, cb, g, xs, e, v):
  match e:
    case L.Insert{i, x}:
      (gap_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v), Unit{})
    case L.Delete{i}:
      (has_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v), Unit{})
    case L.Update{+i, d}:
      at_valid(~ca, ~cb, ~g, L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), i, List.get(&2, C.Value(ca), xs, i), d, has_get(C.Value(ca), xs, i, v), has_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v))

# Lemma: valid edits map to edits valid for the mapped list, if g is
# correct: each edit's edits are valid for the mapped list as the edits
# before it left it, which is the list they left, mapped.
law valid_run:
  for ~ca: C.EditStructure
  for ~cb: C.EditStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for es: List<&2, L.Edit.of(ca)>
  for +xs: List<&2, C.Value(ca)>
  for v: Laws.valid.edits(~ca, es, xs)
  Laws.valid.edits(~cb, out.run(~ca, ~cb, ~g, es, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))

def valid_run(ca, cb, g, g_ok, es, xs, v):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (ve, vt) = v
      valid_append(~cb, out(~ca, ~cb, ~g, xs, e), out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), out_valid(~ca, ~cb, ~g, xs, e, ve),
        valid_eq(~cb, out.run(~ca, ~cb, ~g, t, L.edit(~ca, e, xs)), C.run(~L.edit_structure(~cb), out(~ca, ~cb, ~g, xs, e), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.edit(~ca, e, xs)), run_out(~ca, ~cb, ~g, ~g_ok, xs, e),
          valid_run(~ca, ~cb, ~g, ~g_ok, t, L.edit(~ca, e, xs), vt)))

# The laws
# --------

def Laws.map_inc(ca, cb, g):
  {==}

def Laws.dmap_keep(ca, cb, g, xs):
  {==}

def Laws.dmap_replace(ca, cb, g, ys, xs):
  {==}

def Laws.dmap_insert(ca, cb, g, i, x, xs):
  {==}

def Laws.dmap_delete(ca, cb, g, i, xs):
  {==}

def Laws.dmap_update_inside(ca, cb, g, xs, i, d, x, at):
  %Equal.sym(Maybe<&2, C.Value(ca)>, List.get(&2, C.Value(ca), xs, i), Some{x}, at) : {C.then(L.edit_structure(~cb), L.map.at(~ca, ~cb, ~g, i, _, d), C.keep(L.edit_structure(~cb))) == C.edit(L.edit_structure(~cb), L.Update{i, C.Inc.df(ca, cb, g)(x, d)}) : C.Change.of(L.edit_structure(~cb))}
  {==}

# dmap is lift's derivative, so lift's law gives it.
def Laws.dmap_then(ca, cb, g, p, q, xs):
  CL.lift_then(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, p, q, xs)

# map.inc(g) is lift applied to map.edit, so lift's law gives it.
def Laws.map_inc_ok(ca, cb, g, g_ok):
  CL.lift_ok(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, ~(xs => e => map_edit_ok(~ca, ~cb, ~g, ~g_ok, xs, e)))

# dmap's change starts over where the change does, with the new list
# mapped, and its edits are out.run's.
def Laws.dmap_local(ca, cb, g, d, xs, v):
  match d:
    case C.Change{s, +es}:
      match s:
        case None{}:
          %Equal.sym(C.Change.of(L.edit_structure(~cb)), C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, es, xs), C.Change{None{}, out.run(~ca, ~cb, ~g, es, xs)}, lift_run_out(~ca, ~cb, ~g, es, xs)) : {L.shape(~cb, _) == L.shape(~ca, C.Change{None{}, es}) : C.Change<Unit, L.Edit<Unit, Unit>>}
          %Equal.sym(List<&2, L.Edit<Unit, Unit>>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, es, xs)), C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), es), shape_run(~ca, ~cb, ~g, es, xs, v)) : {C.Change{None{}, _} == L.shape(~ca, C.Change{None{}, es}) : C.Change<Unit, L.Edit<Unit, Unit>>}
          {==}
        case Some{+ys}:
          %Equal.sym(C.Change.of(L.edit_structure(~cb)), C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, es, ys), C.Change{None{}, out.run(~ca, ~cb, ~g, es, ys)}, lift_run_out(~ca, ~cb, ~g, es, ys)) : {L.shape(~cb, C.then(L.edit_structure(~cb), C.replace(L.edit_structure(~cb), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys)), _)) == L.shape(~ca, C.Change{Some{ys}, es}) : C.Change<Unit, L.Edit<Unit, Unit>>}
          %Equal.sym(List<&2, L.Edit<Unit, Unit>>, C.map.edits(~L.Edit.of(cb), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(cb), ~C.Edit(cb), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), out.run(~ca, ~cb, ~g, es, ys)), C.map.edits(~L.Edit.of(ca), ~L.Edit<Unit, Unit>, ~(e => L.Edit.map(~C.Value(ca), ~C.Edit(ca), ~Unit, ~Unit, ~(x => Unit{}), ~(u => Unit{}), e)), es), shape_run(~ca, ~cb, ~g, es, ys, v)) : {C.Change{Some{Unit{}}, _} == L.shape(~ca, C.Change{Some{ys}, es}) : C.Change<Unit, L.Edit<Unit, Unit>>}
          {==}

def Laws.dmap_valid(ca, cb, g, g_ok, d, xs, v):
  match d:
    case C.Change{s, +es}:
      match s:
        case None{}:
          %Equal.sym(C.Change.of(L.edit_structure(~cb)), C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, es, xs), C.Change{None{}, out.run(~ca, ~cb, ~g, es, xs)}, lift_run_out(~ca, ~cb, ~g, es, xs)) : Laws.valid(~cb, _, L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
          valid_run(~ca, ~cb, ~g, ~g_ok, es, xs, v)
        case Some{+ys}:
          %Equal.sym(C.Change.of(L.edit_structure(~cb)), C.lift.run(~L.edit_structure(~ca), ~L.edit_structure(~cb), ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)}, es, ys), C.Change{None{}, out.run(~ca, ~cb, ~g, es, ys)}, lift_run_out(~ca, ~cb, ~g, es, ys)) : Laws.valid(~cb, C.then(L.edit_structure(~cb), C.replace(L.edit_structure(~cb), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys)), _), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
          valid_run(~ca, ~cb, ~g, ~g_ok, es, ys, v)
