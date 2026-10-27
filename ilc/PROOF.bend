import Base
import ./list.bend as L
import ./LAWS.bend as Laws

def Bool.holds(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# Helper: False is not True.
law clash:
  for e: {False{} == True{} : Bool}
  Empty

def clash(e):
  %Equal.sym(Bool, False{}, True{}, e) : Bool.holds(_)
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

# Applying a change
# -----------------

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

# Lemma: set at a position inside the list puts x in place of the element
# there.
law set_inside:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  for inside: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {L.set(A, xs, i, x) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

def set_inside(A, xs, i, x, inside):
  match xs i:
    case Nil{} 0n:
      Empty.absurd({L.set(A, Nil{}, 0n, x) == List.append(&2, A, List.take(&2, A, Nil{}, 0n), x <> List.drop(&2, A, Nil{}, 1n)) : List<&2, A>}, clash(inside))
    case Nil{} 1n+p:
      Empty.absurd({L.set(A, Nil{}, 1n+p, x) == List.append(&2, A, List.take(&2, A, Nil{}, 1n+p), x <> List.drop(&2, A, Nil{}, 1n+1n+p)) : List<&2, A>}, clash(inside))
    case Con{h, t} 0n:
      %Equal.sym(List<&2, A>, List.drop(&2, A, t, 0n), t, drop_zero(A, t)) : {x <> t == x <> _ : List<&2, A>}
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.set(A, t, p, x), List.append(&2, A, List.take(&2, A, t, p), x <> List.drop(&2, A, t, 1n+p)), set_inside(A, t, p, x, inside)) : {h <> _ == h <> List.append(&2, A, List.take(&2, A, t, p), x <> List.drop(&2, A, t, 1n+p)) : List<&2, A>}
      {==}

# Lemma: set past the end leaves the list as it was.
law set_outside:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  for outside: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {L.set(A, xs, i, x) == xs : List<&2, A>}

def set_outside(A, xs, i, x, outside):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      Empty.absurd({L.set(A, h <> t, 0n, x) == h <> t : List<&2, A>}, clash(Equal.sym(Bool, True{}, False{}, outside)))
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, A>, L.set(A, t, p, x), t, set_outside(A, t, p, x, outside)) : {h <> _ == h <> t : List<&2, A>}
      {==}

def Laws.patch_keep(A, xs):
  {==}

def Laws.patch_insert(A, xs, i, x):
  insert_split(A, xs, i, x)

def Laws.patch_delete(A, xs, i):
  remove_split(A, xs, i)

def Laws.patch_set_inside(A, xs, i, x, inside):
  set_inside(A, xs, i, x, inside)

def Laws.patch_set_outside(A, xs, i, x, outside):
  set_outside(A, xs, i, x, outside)

def Laws.patch_replace(A, xs, ys):
  {==}

def Laws.patch_then(A, xs, a, b):
  {==}

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
  {L.map(~A, ~B, ~f, L.insert(A, xs, i, x)) == L.insert(B, L.map(~A, ~B, ~f, xs), i, f(x)) : List<&2, B>}

def map_insert(A, B, f, xs, i, x):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.map(~A, ~B, ~f, L.insert(A, t, p, x)), L.insert(B, L.map(~A, ~B, ~f, t), p, f(x)), map_insert(~A, ~B, ~f, t, p, x)) : {f(h) <> _ == f(h) <> L.insert(B, L.map(~A, ~B, ~f, t), p, f(x)) : List<&2, B>}
      {==}

# Lemma: mapping after a delete deletes from the mapped list.
law map_remove:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  {L.map(~A, ~B, ~f, L.remove(A, xs, i)) == L.remove(B, L.map(~A, ~B, ~f, xs), i) : List<&2, B>}

def map_remove(A, B, f, xs, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.map(~A, ~B, ~f, L.remove(A, t, p)), L.remove(B, L.map(~A, ~B, ~f, t), p), map_remove(~A, ~B, ~f, t, p)) : {f(h) <> _ == f(h) <> L.remove(B, L.map(~A, ~B, ~f, t), p) : List<&2, B>}
      {==}

# Lemma: mapping after a set sets the mapped element.
law map_set:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.map(~A, ~B, ~f, L.set(A, xs, i, x)) == L.set(B, L.map(~A, ~B, ~f, xs), i, f(x)) : List<&2, B>}

def map_set(A, B, f, xs, i, x):
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(List<&2, B>, L.map(~A, ~B, ~f, L.set(A, t, p, x)), L.set(B, L.map(~A, ~B, ~f, t), p, f(x)), map_set(~A, ~B, ~f, t, p, x)) : {f(h) <> _ == f(h) <> L.set(B, L.map(~A, ~B, ~f, t), p, f(x)) : List<&2, B>}
      {==}

# Lemma, by induction on the change.
law map_patch:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for dx: L.Change<A>
  for +xs: List<&2, A>
  {L.map(~A, ~B, ~f, L.patch(A, dx, xs)) == L.patch(B, L.map.change(~A, ~B, ~f, dx), L.map(~A, ~B, ~f, xs)) : List<&2, B>}

def map_patch(A, B, f, dx, xs):
  match dx:
    case L.Keep{}:
      {==}
    case L.Insert{i, x}:
      map_insert(~A, ~B, ~f, xs, i, x)
    case L.Delete{i}:
      map_remove(~A, ~B, ~f, xs, i)
    case L.Set{i, x}:
      map_set(~A, ~B, ~f, xs, i, x)
    case L.Replace{ys}:
      {==}
    case L.Then{+a, b}:
      %Equal.sym(List<&2, B>, L.map(~A, ~B, ~f, L.patch(A, b, L.patch(A, a, xs))), L.patch(B, L.map.change(~A, ~B, ~f, b), L.map(~A, ~B, ~f, L.patch(A, a, xs))), map_patch(~A, ~B, ~f, b, L.patch(A, a, xs))) : {_ == L.patch(B, L.map.change(~A, ~B, ~f, b), L.patch(B, L.map.change(~A, ~B, ~f, a), L.map(~A, ~B, ~f, xs))) : List<&2, B>}
      %Equal.sym(List<&2, B>, L.map(~A, ~B, ~f, L.patch(A, a, xs)), L.patch(B, L.map.change(~A, ~B, ~f, a), L.map(~A, ~B, ~f, xs)), map_patch(~A, ~B, ~f, a, xs)) : {L.patch(B, L.map.change(~A, ~B, ~f, b), _) == L.patch(B, L.map.change(~A, ~B, ~f, b), L.patch(B, L.map.change(~A, ~B, ~f, a), L.map(~A, ~B, ~f, xs))) : List<&2, B>}
      {==}

def Laws.map_change(A, B, f, xs, dx):
  map_patch(~A, ~B, ~f, dx, xs)

# Lemma: mapping keeps the length.
law map_length:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for ys: List<&2, A>
  {List.length(&2, B, L.map(~A, ~B, ~f, ys)) == List.length(&2, A, ys) : Nat}

def map_length(A, B, f, ys):
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, List.length(&2, B, L.map(~A, ~B, ~f, t)), List.length(&2, A, t), map_length(~A, ~B, ~f, t)) : {1n+_ == 1n+List.length(&2, A, t) : Nat}
      {==}

def Laws.map_change_local(A, B, f, dx):
  match dx:
    case L.Keep{}:
      {==}
    case L.Insert{i, x}:
      {==}
    case L.Delete{i}:
      {==}
    case L.Set{i, x}:
      {==}
    case L.Replace{ys}:
      %Equal.sym(Nat, List.length(&2, B, L.map(~A, ~B, ~f, ys)), List.length(&2, A, ys), map_length(~A, ~B, ~f, ys)) : {L.SReplace{_} == L.SReplace{List.length(&2, A, ys)} : L.Shape}
      {==}
    case L.Then{a, b}:
      %Equal.sym(L.Shape, L.shape(B, L.map.change(~A, ~B, ~f, a)), L.shape(A, a), Laws.map_change_local(~A, ~B, ~f, a)) : {L.SThen{_, L.shape(B, L.map.change(~A, ~B, ~f, b))} == L.SThen{L.shape(A, a), L.shape(A, b)} : L.Shape}
      %Equal.sym(L.Shape, L.shape(B, L.map.change(~A, ~B, ~f, b)), L.shape(A, b), Laws.map_change_local(~A, ~B, ~f, b)) : {L.SThen{L.shape(A, a), _} == L.SThen{L.shape(A, a), L.shape(A, b)} : L.Shape}
      {==}
