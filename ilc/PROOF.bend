import Base
import ./change.bend as C
import ./list.bend as L
import ./LAWS.bend as Laws

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

# Changes to any value
# --------------------

def Laws.apply_keep(A, E, edit, a):
  {==}

def Laws.apply_replace(A, E, edit, x, a):
  {==}

def Laws.apply_edit(A, E, edit, e, a):
  {==}

def Laws.apply_then(A, E, edit, p, q, a):
  {==}

def Laws.then_keep_left(A, E, edit, q, a):
  {==}

def Laws.then_keep_right(A, E, edit, p, a):
  {==}

def Laws.then_assoc(A, E, edit, p, q, r, a):
  {==}

# Derivatives
# -----------

# By induction on the change: after the first part of a Then, the lifted
# derivative of the rest starts from the value the first part produced.
def Laws.lift(A, E, B, F, ea, eb, f, fe, fe_ok, d, a):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{x}:
      {==}
    case C.Edit{e}:
      fe_ok(a, e)
    case C.Then{+p, q}:
      %Equal.sym(B, C.apply(~B, ~F, ~eb, C.lift(~A, ~E, ~B, ~F, ~ea, ~f, ~fe, p, a), f(a)), f(C.apply(~A, ~E, ~ea, p, a)), Laws.lift(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~fe, ~fe_ok, p, a)) : {C.apply(~B, ~F, ~eb, C.lift(~A, ~E, ~B, ~F, ~ea, ~f, ~fe, q, C.apply(~A, ~E, ~ea, p, a)), _) == f(C.apply(~A, ~E, ~ea, q, C.apply(~A, ~E, ~ea, p, a))) : B}
      Laws.lift(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~fe, ~fe_ok, q, C.apply(~A, ~E, ~ea, p, a))

def Laws.recompute(A, E, B, F, ea, eb, f, a, d):
  {==}

# Lists
# -----

def Laws.patch(A, E, ea, d, xs):
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

def Laws.edit_insert(A, E, ea, xs, i, x):
  insert_split(A, xs, i, x)

def Laws.edit_delete(A, E, ea, xs, i):
  remove_split(A, xs, i)

# Lemma: update at a position holding x puts the changed x in its place.
law update_inside:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: C.Change<A, E>
  for x: A
  for at: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}
  {L.update(~A, ~E, ~ea, xs, i, d) == List.append(&2, A, List.take(&2, A, xs, i), C.apply(~A, ~E, ~ea, d, x) <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

def update_inside(A, E, ea, xs, i, d, x, at):
  match xs i:
    case Nil{} _:
      Empty.absurd({L.update(~A, ~E, ~ea, Nil{}, i, d) == List.append(&2, A, List.take(&2, A, Nil{}, i), C.apply(~A, ~E, ~ea, d, x) <> List.drop(&2, A, Nil{}, 1n+i)) : List<&2, A>},
        some_none(A, x, Equal.sym(Maybe<&2, A>, None{}, Some{x}, at)))
    case Con{h, t} 0n:
      %Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, h), Some{h}, Some{x}, at) : {C.apply(~A, ~E, ~ea, d, h) <> t == C.apply(~A, ~E, ~ea, d, _) <> List.drop(&2, A, t, 0n) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.drop(&2, A, t, 0n), t, drop_zero(A, t)) : {C.apply(~A, ~E, ~ea, d, h) <> t == C.apply(~A, ~E, ~ea, d, h) <> _ : List<&2, A>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.update(~A, ~E, ~ea, t, p, d), List.append(&2, A, List.take(&2, A, t, p), C.apply(~A, ~E, ~ea, d, x) <> List.drop(&2, A, t, 1n+p)), update_inside(~A, ~E, ~ea, t, p, d, x, at)) : {h <> _ == h <> List.append(&2, A, List.take(&2, A, t, p), C.apply(~A, ~E, ~ea, d, x) <> List.drop(&2, A, t, 1n+p)) : List<&2, A>}
      {==}

# Lemma: update past the end leaves the list as it was.
law update_outside:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for xs: List<&2, A>
  for i: Nat
  for d: C.Change<A, E>
  for past: {List.get(&2, A, xs, i) == None{} : Maybe<&2, A>}
  {L.update(~A, ~E, ~ea, xs, i, d) == xs : List<&2, A>}

def update_outside(A, E, ea, xs, i, d, past):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      Empty.absurd({L.update(~A, ~E, ~ea, h <> t, 0n, d) == h <> t : List<&2, A>}, some_none(A, h, past))
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.update(~A, ~E, ~ea, t, p, d), t, update_outside(~A, ~E, ~ea, t, p, d, past)) : {h <> _ == h <> t : List<&2, A>}
      {==}

def Laws.edit_update_inside(A, E, ea, xs, i, d, x, at):
  update_inside(~A, ~E, ~ea, xs, i, d, x, at)

def Laws.edit_update_outside(A, E, ea, xs, i, d, past):
  update_outside(~A, ~E, ~ea, xs, i, d, past)

def Laws.map_nil(A, B, f):
  {==}

def Laws.map_con(A, B, f, h, t):
  {==}

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

# Lemma: mapping after an update updates the mapped element by f's
# derivative, if that derivative is correct.
law map_update:
  for ~A: Data
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~eb: F -> B -> B
  for ~f: A -> B
  for ~df: A -> C.Change<A, E> -> C.Change<B, F>
  for ~df_ok: (@x: A -> @d: C.Change<A, E> -> {C.apply(~B, ~F, ~eb, df(x, d), f(x)) == f(C.apply(~A, ~E, ~ea, d, x)) : B})
  for xs: List<&2, A>
  for i: Nat
  for d: C.Change<A, E>
  {L.update(~B, ~F, ~eb, L.map(~A, ~B, ~f, xs), i, L.map.at(~A, ~E, ~B, ~F, ~df, List.get(&2, A, xs, i), d)) == L.map(~A, ~B, ~f, L.update(~A, ~E, ~ea, xs, i, d)) : List<&2, B>}

def map_update(A, E, B, F, ea, eb, f, df, df_ok, xs, i, d):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %Equal.sym(B, C.apply(~B, ~F, ~eb, df(h, d), f(h)), f(C.apply(~A, ~E, ~ea, d, h)), df_ok(h, d)) : {_ <> L.map(~A, ~B, ~f, t) == f(C.apply(~A, ~E, ~ea, d, h)) <> L.map(~A, ~B, ~f, t) : List<&2, B>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.update(~B, ~F, ~eb, L.map(~A, ~B, ~f, t), p, L.map.at(~A, ~E, ~B, ~F, ~df, List.get(&2, A, t, p), d)), L.map(~A, ~B, ~f, L.update(~A, ~E, ~ea, t, p, d)), map_update(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~df, ~df_ok, t, p, d)) : {f(h) <> _ == f(h) <> L.map(~A, ~B, ~f, L.update(~A, ~E, ~ea, t, p, d)) : List<&2, B>}
      {==}

# Lemma: map.edit is correct for every single edit, if df is.
law map_edit_ok:
  for ~A: Data
  for ~E: Data
  for ~B: Data
  for ~F: Data
  for ~ea: E -> A -> A
  for ~eb: F -> B -> B
  for ~f: A -> B
  for ~df: A -> C.Change<A, E> -> C.Change<B, F>
  for ~df_ok: (@x: A -> @d: C.Change<A, E> -> {C.apply(~B, ~F, ~eb, df(x, d), f(x)) == f(C.apply(~A, ~E, ~ea, d, x)) : B})
  for xs: List<&2, A>
  for e: L.Edit<A, E>
  {L.patch(~B, ~F, ~eb, L.map.edit(~A, ~E, ~B, ~F, ~f, ~df, xs, e), L.map(~A, ~B, ~f, xs)) == L.map(~A, ~B, ~f, L.edit(~A, ~E, ~ea, e, xs)) : List<&2, B>}

def map_edit_ok(A, E, B, F, ea, eb, f, df, df_ok, xs, e):
  match e:
    case L.Insert{i, x}:
      map_insert(~A, ~B, ~f, xs, i, x)
    case L.Delete{i}:
      map_remove(~A, ~B, ~f, xs, i)
    case L.Update{i, d}:
      map_update(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~df, ~df_ok, xs, i, d)

# The same induction as lift's law. (Lift's law gives this directly, but
# BendTT, the kernel behind --verdict, can't yet check a law instantiated
# with functions, so map.change is proved on its own.)
def Laws.map_change(A, E, B, F, ea, eb, f, df, df_ok, d, xs):
  match d:
    case C.Keep{}:
      {==}
    case C.Replace{ys}:
      {==}
    case C.Edit{e}:
      map_edit_ok(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~df, ~df_ok, xs, e)
    case C.Then{+p, q}:
      %Equal.sym(List<&2, B>, L.patch(~B, ~F, ~eb, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, p, xs), L.map(~A, ~B, ~f, xs)), L.map(~A, ~B, ~f, L.patch(~A, ~E, ~ea, p, xs)), Laws.map_change(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~df, ~df_ok, p, xs)) : {L.patch(~B, ~F, ~eb, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, q, L.patch(~A, ~E, ~ea, p, xs)), _) == L.map(~A, ~B, ~f, L.patch(~A, ~E, ~ea, q, L.patch(~A, ~E, ~ea, p, xs))) : List<&2, B>}
      Laws.map_change(~A, ~E, ~B, ~F, ~ea, ~eb, ~f, ~df, ~df_ok, q, L.patch(~A, ~E, ~ea, p, xs))

# By induction on the change; a single edit maps to an edit of the same
# kind at the same position.
def Laws.map_change_local(A, E, B, F, ea, f, df, d, xs):
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
        case L.Update{i, u}:
          {==}
    case C.Then{+p, q}:
      %Equal.sym(C.Shape<L.Where>, L.shape(~B, ~F, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, p, xs)), L.shape(~A, ~E, p), Laws.map_change_local(~A, ~E, ~B, ~F, ~ea, ~f, ~df, p, xs)) : {C.SThen{_, L.shape(~B, ~F, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, q, L.patch(~A, ~E, ~ea, p, xs)))} == C.SThen{L.shape(~A, ~E, p), L.shape(~A, ~E, q)} : C.Shape<L.Where>}
      %Equal.sym(C.Shape<L.Where>, L.shape(~B, ~F, L.map.change(~A, ~E, ~B, ~F, ~ea, ~f, ~df, q, L.patch(~A, ~E, ~ea, p, xs))), L.shape(~A, ~E, q), Laws.map_change_local(~A, ~E, ~B, ~F, ~ea, ~f, ~df, q, L.patch(~A, ~E, ~ea, p, xs))) : {C.SThen{L.shape(~A, ~E, p), _} == C.SThen{L.shape(~A, ~E, p), L.shape(~A, ~E, q)} : C.Shape<L.Where>}
      {==}
