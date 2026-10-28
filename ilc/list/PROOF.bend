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

def Laws.structure(ca):
  {==}

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
  for ~ca: C.ChangeStructure
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for d: C.Delta(ca)
  for x: C.Value(ca)
  for at: {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.update(~ca, xs, i, d) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), xs, i), C.ChangeStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), xs, 1n+i)) : List<&2, C.Value(ca)>}

def update_inside(ca, xs, i, d, x, at):
  match xs i:
    case Nil{} _:
      Empty.absurd({L.update(~ca, Nil{}, i, d) == List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), Nil{}, i), C.ChangeStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), Nil{}, 1n+i)) : List<&2, C.Value(ca)>},
        some_none(C.Value(ca), x, Equal.sym(Maybe<&2, C.Value(ca)>, None{}, Some{x}, at)))
    case Con{h, t} 0n:
      %Equal.cong(Maybe<&2, C.Value(ca)>, C.Value(ca), m => Maybe.default(&2, C.Value(ca), m, h), Some{h}, Some{x}, at) : {C.ChangeStructure.apply(ca)(d, h) <> t == C.ChangeStructure.apply(ca)(d, _) <> List.drop(&2, C.Value(ca), t, 0n) : List<&2, C.Value(ca)>}
      %Equal.sym(List<&2, C.Value(ca)>, List.drop(&2, C.Value(ca), t, 0n), t, drop_zero(C.Value(ca), t)) : {C.ChangeStructure.apply(ca)(d, h) <> t == C.ChangeStructure.apply(ca)(d, h) <> _ : List<&2, C.Value(ca)>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, C.Value(ca)>, L.update(~ca, t, p, d), List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), t, p), C.ChangeStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), t, 1n+p)), update_inside(~ca, t, p, d, x, at)) : {h <> _ == h <> List.append(&2, C.Value(ca), List.take(&2, C.Value(ca), t, p), C.ChangeStructure.apply(ca)(d, x) <> List.drop(&2, C.Value(ca), t, 1n+p)) : List<&2, C.Value(ca)>}
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
  exs x: A
  {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}

def has_get(A, xs, i, v):
  match xs i:
    case Nil{} _:
      match v:
    case Con{h, t} 0n:
      (h, {==})
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
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for p: Nat
  for m: Maybe<&2, C.Value(ca)>
  for d: C.Delta(ca)
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
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for ~g_ok: C.Inc.ok(ca, cb, g)
  for +xs: List<&2, C.Value(ca)>
  for +i: Nat
  for +d: C.Delta(ca)
  {L.patch(~cb, L.map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) == L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, xs, i, d)) : List<&2, C.Value(cb)>}

def map_update(ca, cb, g, g_ok, xs, i, d):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %Equal.sym(C.Value(cb), C.ChangeStructure.apply(cb)(C.Inc.df(ca, cb, g)(h, d), C.Inc.f(ca, cb, g)(h)), C.Inc.f(ca, cb, g)(C.ChangeStructure.apply(ca)(d, h)), g_ok(h, d)) : {_ <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t) == C.Inc.f(ca, cb, g)(C.ChangeStructure.apply(ca)(d, h)) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t) : List<&2, C.Value(cb)>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, C.Value(cb)>, L.patch(~cb, L.map.at(~ca, ~cb, ~g, 1n+p, List.get(&2, C.Value(ca), t, p), d), C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), C.Inc.f(ca, cb, g)(h) <> L.patch(~cb, L.map.at(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), at_shift(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d, C.Inc.f(ca, cb, g)(h), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t))) : {_ == C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)) : List<&2, C.Value(cb)>}
      %Equal.sym(List<&2, C.Value(cb)>, L.patch(~cb, L.map.at(~ca, ~cb, ~g, p, List.get(&2, C.Value(ca), t, p), d), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), t)), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)), map_update(~ca, ~cb, ~g, ~g_ok, t, p, d)) : {C.Inc.f(ca, cb, g)(h) <> _ == C.Inc.f(ca, cb, g)(h) <> L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.update(~ca, t, p, d)) : List<&2, C.Value(cb)>}
      {==}

# Lemma: map.edit is correct for every single edit, if g is.
law map_edit_ok:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
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

# Lemma: an update at a position holding an element maps to an update at
# the same position.
law at_shape:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for u: C.Delta(ca)
  for r: &x: C.Value(ca) -> {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  {L.shape(~cb, L.map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), u)) == L.shape(~ca, C.Edit{L.Update{i, u}}) : C.Change<Unit, L.Edit<Unit, Unit>>}

def at_shape(ca, cb, g, xs, i, u, r):
  match r:
    case (x, at):
      %Equal.sym(Maybe<&2, C.Value(ca)>, List.get(&2, C.Value(ca), xs, i), Some{x}, at) : {L.shape(~cb, L.map.at(~ca, ~cb, ~g, i, _, u)) == L.shape(~ca, C.Edit{L.Update{i, u}}) : C.Change<Unit, L.Edit<Unit, Unit>>}
      {==}

# Lemma: an update at a position holding an element maps to an update
# valid for the mapped list, if its position is in range there.
law at_valid_at:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for xs: List<&2, C.Value(ca)>
  for i: Nat
  for u: C.Delta(ca)
  for r: &x: C.Value(ca) -> {List.get(&2, C.Value(ca), xs, i) == Some{x} : Maybe<&2, C.Value(ca)>}
  for w: Laws.has(C.Value(cb), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs), i)
  Laws.valid(~cb, L.map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), u), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))

def at_valid_at(ca, cb, g, xs, i, u, r, w):
  match r:
    case (x, at):
      %Equal.sym(Maybe<&2, C.Value(ca)>, List.get(&2, C.Value(ca), xs, i), Some{x}, at) : Laws.valid(~cb, L.map.at(~ca, ~cb, ~g, i, _, u), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))
      w

# Lemma: a valid update maps to a valid update.
law at_valid:
  for ~ca: C.ChangeStructure
  for ~cb: C.ChangeStructure
  for ~g: C.Inc<ca, cb>
  for +xs: List<&2, C.Value(ca)>
  for +i: Nat
  for u: C.Delta(ca)
  for +v: Laws.has(C.Value(ca), xs, i)
  Laws.valid(~cb, L.map.at(~ca, ~cb, ~g, i, List.get(&2, C.Value(ca), xs, i), u), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs))

def at_valid(ca, cb, g, xs, i, u, v):
  at_valid_at(~ca, ~cb, ~g, xs, i, u, has_get(C.Value(ca), xs, i, v), has_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v))

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
  %Equal.sym(Maybe<&2, C.Value(ca)>, List.get(&2, C.Value(ca), xs, i), Some{x}, at) : {L.map.at(~ca, ~cb, ~g, i, _, d) == C.Edit{L.Update{i, C.Inc.df(ca, cb, g)(x, d)}} : C.Change.of(L.structure(~cb))}
  {==}

def Laws.dmap_then(ca, cb, g, p, q, xs):
  {==}

# map.inc(g) is lift applied to map.edit, so lift's law gives it.
def Laws.map_inc_ok(ca, cb, g, g_ok):
  CL.lift_ok(~L.structure(~ca), ~L.structure(~cb),
    ~C.Inc{ys => L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), ys), ys => e => L.map.edit(~ca, ~cb, ~g, ys, e)},
    ~(xs => e => map_edit_ok(~ca, ~cb, ~g, ~g_ok, xs, e)))

# By induction on the change; a single edit maps to an edit of the same
# kind at the same position, since a valid update finds its element.
def Laws.dmap_local(ca, cb, g, d, xs, v):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{ys}:
      {==}
    case C.Edit{e}:
      match e:
        case L.Insert{i, x}:
          {==}
        case L.Delete{i}:
          {==}
        case L.Update{+i, u}:
          at_shape(~ca, ~cb, ~g, xs, i, u, has_get(C.Value(ca), xs, i, v))
    case C.Then{+p, q}:
      (vp, vq) = v
      %Equal.sym(C.Change<Unit, L.Edit<Unit, Unit>>, L.shape(~cb, L.dmap(~ca, ~cb, ~g, p, xs)), L.shape(~ca, p), Laws.dmap_local(~ca, ~cb, ~g, p, xs, vp)) : {C.Then{_, L.shape(~cb, L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs)))} == C.Then{L.shape(~ca, p), L.shape(~ca, q)} : C.Change<Unit, L.Edit<Unit, Unit>>}
      %Equal.sym(C.Change<Unit, L.Edit<Unit, Unit>>, L.shape(~cb, L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs))), L.shape(~ca, q), Laws.dmap_local(~ca, ~cb, ~g, q, L.patch(~ca, p, xs), vq)) : {C.Then{L.shape(~ca, p), _} == C.Then{L.shape(~ca, p), L.shape(~ca, q)} : C.Change<Unit, L.Edit<Unit, Unit>>}
      {==}

# By induction on the change: a valid edit's position is in range for the
# mapped list too, and after the first part of a Then, the mapped list is
# the list the first part produced, mapped.
def Laws.dmap_valid(ca, cb, g, g_ok, d, xs, v):
  match d:
    case C.Keep{}:
      Unit{}
    case C.Replace{ys}:
      Unit{}
    case C.Edit{e}:
      match e:
        case L.Insert{i, x}:
          gap_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v)
        case L.Delete{i}:
          has_map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs, i, v)
        case L.Update{+i, u}:
          at_valid(~ca, ~cb, ~g, xs, i, u, v)
    case C.Then{+p, q}:
      (vp, vq) = v
      %Equal.sym(List<&2, C.Value(cb)>, L.patch(~cb, L.dmap(~ca, ~cb, ~g, p, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), L.patch(~ca, p, xs)), Laws.map_inc_ok(~ca, ~cb, ~g, ~g_ok)(xs, p)) : Laws.valid(~cb, L.dmap(~ca, ~cb, ~g, p, xs), L.map(~C.Value(ca), ~C.Value(cb), ~C.Inc.f(ca, cb, g), xs)) & Laws.valid(~cb, L.dmap(~ca, ~cb, ~g, q, L.patch(~ca, p, xs)), _)
      (Laws.dmap_valid(~ca, ~cb, ~g, ~g_ok, p, xs, vp), Laws.dmap_valid(~ca, ~cb, ~g, ~g_ok, q, L.patch(~ca, p, xs), vq))
