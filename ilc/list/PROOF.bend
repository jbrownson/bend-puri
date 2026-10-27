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

def Laws.patch(A, DA, pa, d, xs):
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

def Laws.edit_insert(A, DA, pa, xs, i, x, v):
  insert_split(A, xs, i, x)

def Laws.edit_delete(A, DA, pa, xs, i, v):
  remove_split(A, xs, i)

# Lemma: update at a position holding x puts the changed x in its place.
law update_inside:
  for ~A: Data
  for ~DA: Data
  for ~pa: DA -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: DA
  for x: A
  for at: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.update(~A, ~DA, ~pa, xs, i, d) == List.append(&2, A, List.take(&2, A, xs, i), pa(d, x) <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

def update_inside(A, DA, pa, xs, i, d, x, at):
  match xs i:
    case Nil{} _:
      Empty.absurd({L.update(~A, ~DA, ~pa, Nil{}, i, d) == List.append(&2, A, List.take(&2, A, Nil{}, i), pa(d, x) <> List.drop(&2, A, Nil{}, 1n+i)) : List<&2, A>},
        some_none(A, x, Equal.sym(Maybe<&2, A>, None{}, Some{x}, at)))
    case Con{h, t} 0n:
      %Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, h), Some{h}, Some{x}, at) : {pa(d, h) <> t == pa(d, _) <> List.drop(&2, A, t, 0n) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.drop(&2, A, t, 0n), t, drop_zero(A, t)) : {pa(d, h) <> t == pa(d, h) <> _ : List<&2, A>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.update(~A, ~DA, ~pa, t, p, d), List.append(&2, A, List.take(&2, A, t, p), pa(d, x) <> List.drop(&2, A, t, 1n+p)), update_inside(~A, ~DA, ~pa, t, p, d, x, at)) : {h <> _ == h <> List.append(&2, A, List.take(&2, A, t, p), pa(d, x) <> List.drop(&2, A, t, 1n+p)) : List<&2, A>}
      {==}

def Laws.edit_update_inside(A, DA, pa, xs, i, d, x, at):
  update_inside(~A, ~DA, ~pa, xs, i, d, x, at)

def Laws.edit_map_insert(A, DA, B, DB, fa, fd, i, x):
  {==}

def Laws.edit_map_delete(A, DA, B, DB, fa, fd, i):
  {==}

def Laws.edit_map_update(A, DA, B, DB, fa, fd, i, d):
  {==}

def Laws.shape(A, DA, d):
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
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for p: Nat
  for m: Maybe<&2, A>
  for d: DA
  for y: B
  for ys: List<&2, B>
  {L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, 1n+p, m, d), y <> ys) == y <> L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, p, m, d), ys) : List<&2, B>}

def at_shift(A, DA, B, DB, pb, g, p, m, d, y, ys):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Lemma: mapping after an update updates the mapped element by g's
# derivative, if g is correct.
law map_update:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for ~g_ok: C.Inc.ok(A, DA, B, DB, pa, pb, g)
  for +xs: List<&2, A>
  for +i: Nat
  for +d: DA
  {L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, List.get(&2, A, xs, i), d), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs)) == L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.update(~A, ~DA, ~pa, xs, i, d)) : List<&2, B>}

def map_update(A, DA, B, DB, pa, pb, g, g_ok, xs, i, d):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %Equal.sym(B, pb(C.Inc.df(A, DA, B, DB, g)(h, d), C.Inc.f(A, DA, B, DB, g)(h)), C.Inc.f(A, DA, B, DB, g)(pa(d, h)), g_ok(h, d)) : {_ <> L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t) == C.Inc.f(A, DA, B, DB, g)(pa(d, h)) <> L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t) : List<&2, B>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, 1n+p, List.get(&2, A, t, p), d), C.Inc.f(A, DA, B, DB, g)(h) <> L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t)), C.Inc.f(A, DA, B, DB, g)(h) <> L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, p, List.get(&2, A, t, p), d), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t)), at_shift(~A, ~DA, ~B, ~DB, ~pb, ~g, p, List.get(&2, A, t, p), d, C.Inc.f(A, DA, B, DB, g)(h), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t))) : {_ == C.Inc.f(A, DA, B, DB, g)(h) <> L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.update(~A, ~DA, ~pa, t, p, d)) : List<&2, B>}
      %Equal.sym(List<&2, B>, L.patch(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, p, List.get(&2, A, t, p), d), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), t)), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.update(~A, ~DA, ~pa, t, p, d)), map_update(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok, t, p, d)) : {C.Inc.f(A, DA, B, DB, g)(h) <> _ == C.Inc.f(A, DA, B, DB, g)(h) <> L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.update(~A, ~DA, ~pa, t, p, d)) : List<&2, B>}
      {==}

# Lemma: map.edit is correct for every single edit, if g is.
law map_edit_ok:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pa: DA -> A -> A
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for ~g_ok: C.Inc.ok(A, DA, B, DB, pa, pb, g)
  for xs: List<&2, A>
  for e: L.Edit<A, DA>
  {L.patch(~B, ~DB, ~pb, L.map.edit(~A, ~DA, ~B, ~DB, ~g, xs, e), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs)) == L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.edit(~A, ~DA, ~pa, e, xs)) : List<&2, B>}

def map_edit_ok(A, DA, B, DB, pa, pb, g, g_ok, xs, e):
  match e:
    case L.Insert{i, x}:
      map_insert(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs, i, x)
    case L.Delete{i}:
      map_remove(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs, i)
    case L.Update{i, d}:
      map_update(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok, xs, i, d)

# Lemma: an update at a position holding an element maps to an update at
# the same position.
law at_shape:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~g: C.Inc<A, DA, B, DB>
  for xs: List<&2, A>
  for i: Nat
  for u: DA
  for r: &x: A -> {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.shape(~B, ~DB, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, List.get(&2, A, xs, i), u)) == L.shape(~A, ~DA, C.Edit{L.Update{i, u}}) : C.Change<Unit, L.Edit<Unit, Unit>>}

def at_shape(A, DA, B, DB, g, xs, i, u, r):
  match r:
    case (x, at):
      %Equal.sym(Maybe<&2, A>, List.get(&2, A, xs, i), Some{x}, at) : {L.shape(~B, ~DB, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, _, u)) == L.shape(~A, ~DA, C.Edit{L.Update{i, u}}) : C.Change<Unit, L.Edit<Unit, Unit>>}
      {==}

# Lemma: an update at a position holding an element maps to an update
# valid for the mapped list, if its position is in range there.
law at_valid_at:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for xs: List<&2, A>
  for i: Nat
  for u: DA
  for r: &x: A -> {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  for w: Laws.has(B, L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs), i)
  Laws.valid(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, List.get(&2, A, xs, i), u), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs))

def at_valid_at(A, DA, B, DB, pb, g, xs, i, u, r, w):
  match r:
    case (x, at):
      %Equal.sym(Maybe<&2, A>, List.get(&2, A, xs, i), Some{x}, at) : Laws.valid(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, _, u), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs))
      w

# Lemma: a valid update maps to a valid update.
law at_valid:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~pb: DB -> B -> B
  for ~g: C.Inc<A, DA, B, DB>
  for +xs: List<&2, A>
  for +i: Nat
  for u: DA
  for +v: Laws.has(A, xs, i)
  Laws.valid(~B, ~DB, ~pb, L.map.at(~A, ~DA, ~B, ~DB, ~g, i, List.get(&2, A, xs, i), u), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs))

def at_valid(A, DA, B, DB, pb, g, xs, i, u, v):
  at_valid_at(~A, ~DA, ~B, ~DB, ~pb, ~g, xs, i, u, has_get(A, xs, i, v), has_map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs, i, v))

def Laws.map_inc(A, DA, B, DB, pa, g):
  {==}

def Laws.dmap_keep(A, DA, B, DB, pa, g, xs):
  {==}

def Laws.dmap_replace(A, DA, B, DB, pa, g, ys, xs):
  {==}

def Laws.dmap_insert(A, DA, B, DB, pa, g, i, x, xs):
  {==}

def Laws.dmap_delete(A, DA, B, DB, pa, g, i, xs):
  {==}

def Laws.dmap_update_inside(A, DA, B, DB, pa, g, xs, i, d, x, at):
  %Equal.sym(Maybe<&2, A>, List.get(&2, A, xs, i), Some{x}, at) : {L.map.at(~A, ~DA, ~B, ~DB, ~g, i, _, d) == C.Edit{L.Update{i, C.Inc.df(A, DA, B, DB, g)(x, d)}} : L.Change(B, DB)}
  {==}

def Laws.dmap_then(A, DA, B, DB, pa, g, p, q, xs):
  {==}

# map.inc(g) is lift applied to map.edit, so lift's law gives it.
def Laws.map_inc_ok(A, DA, B, DB, pa, pb, g, g_ok):
  CL.lift_ok(~List<&2, A>, ~L.Edit<A, DA>, ~List<&2, B>, ~L.Edit<B, DB>, ~(e => ys => L.edit(~A, ~DA, ~pa, e, ys)), ~(e => ys => L.edit(~B, ~DB, ~pb, e, ys)),
    ~C.Inc{ys => L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), ys), ys => e => L.map.edit(~A, ~DA, ~B, ~DB, ~g, ys, e)},
    ~(xs => e => map_edit_ok(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok, xs, e)))

# By induction on the change; a single edit maps to an edit of the same
# kind at the same position, since a valid update finds its element.
def Laws.dmap_local(A, DA, B, DB, pa, g, d, xs, v):
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
          at_shape(~A, ~DA, ~B, ~DB, ~g, xs, i, u, has_get(A, xs, i, v))
    case C.Then{+p, q}:
      (vp, vq) = v
      %Equal.sym(C.Change<Unit, L.Edit<Unit, Unit>>, L.shape(~B, ~DB, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, p, xs)), L.shape(~A, ~DA, p), Laws.dmap_local(~A, ~DA, ~B, ~DB, ~pa, ~g, p, xs, vp)) : {C.Then{_, L.shape(~B, ~DB, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, q, L.patch(~A, ~DA, ~pa, p, xs)))} == C.Then{L.shape(~A, ~DA, p), L.shape(~A, ~DA, q)} : C.Change<Unit, L.Edit<Unit, Unit>>}
      %Equal.sym(C.Change<Unit, L.Edit<Unit, Unit>>, L.shape(~B, ~DB, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, q, L.patch(~A, ~DA, ~pa, p, xs))), L.shape(~A, ~DA, q), Laws.dmap_local(~A, ~DA, ~B, ~DB, ~pa, ~g, q, L.patch(~A, ~DA, ~pa, p, xs), vq)) : {C.Then{L.shape(~A, ~DA, p), _} == C.Then{L.shape(~A, ~DA, p), L.shape(~A, ~DA, q)} : C.Change<Unit, L.Edit<Unit, Unit>>}
      {==}

# By induction on the change: a valid edit's position is in range for the
# mapped list too, and after the first part of a Then, the mapped list is
# the list the first part produced, mapped.
def Laws.dmap_valid(A, DA, B, DB, pa, pb, g, g_ok, d, xs, v):
  match d:
    case C.Keep{}:
      Unit{}
    case C.Replace{ys}:
      Unit{}
    case C.Edit{e}:
      match e:
        case L.Insert{i, x}:
          gap_map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs, i, v)
        case L.Delete{i}:
          has_map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs, i, v)
        case L.Update{+i, u}:
          at_valid(~A, ~DA, ~B, ~DB, ~pb, ~g, xs, i, u, v)
    case C.Then{+p, q}:
      (vp, vq) = v
      %Equal.sym(List<&2, B>, L.patch(~B, ~DB, ~pb, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, p, xs), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs)), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), L.patch(~A, ~DA, ~pa, p, xs)), Laws.map_inc_ok(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok)(xs, p)) : Laws.valid(~B, ~DB, ~pb, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, p, xs), L.map(~A, ~B, ~C.Inc.f(A, DA, B, DB, g), xs)) & Laws.valid(~B, ~DB, ~pb, L.dmap(~A, ~DA, ~B, ~DB, ~pa, ~g, q, L.patch(~A, ~DA, ~pa, p, xs)), _)
      (Laws.dmap_valid(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok, p, xs, vp), Laws.dmap_valid(~A, ~DA, ~B, ~DB, ~pa, ~pb, ~g, ~g_ok, q, L.patch(~A, ~DA, ~pa, p, xs), vq))
