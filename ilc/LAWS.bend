import Base
import ./list.bend as L

# What the list layer of ILC promises; PROOF.bend proves it. The laws for
# patch say what applying each change returns, case by case. map.change is
# map's derivative: from a change to a list it computes the change to the
# mapped list. Its two laws pin it down: it is correct, and it touches
# exactly what the change touched.
#
# Bend doesn't infer type arguments, so each law starts with a `for` per
# type it mentions.

# Applying a change
# -----------------
# take(xs, i) is the first i elements (all of them when i is past the
# end), and drop(xs, i) the rest.

# LAW: keeping changes nothing.
law patch_keep:
  for -A: Data
  for xs: List<&2, A>
  {L.patch(A, L.Keep{}, xs) == xs : List<&2, A>}

# LAW: inserting at i puts x before the element at i, or at the end when i
# is past it.
law patch_insert:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  {L.patch(A, L.Insert{i, x}, xs) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, i)) : List<&2, A>}

# LAW: deleting at i removes the element at i, or nothing when i is past
# the end.
law patch_delete:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  {L.patch(A, L.Delete{i}, xs) == List.append(&2, A, List.take(&2, A, xs, i), List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: setting at a position inside the list replaces the element there.
law patch_set_inside:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  for inside: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {L.patch(A, L.Set{i, x}, xs) == List.append(&2, A, List.take(&2, A, xs, i), x <> List.drop(&2, A, xs, 1n+i)) : List<&2, A>}

# LAW: setting past the end changes nothing.
law patch_set_outside:
  for -A: Data
  for xs: List<&2, A>
  for i: Nat
  for x: A
  for outside: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {L.patch(A, L.Set{i, x}, xs) == xs : List<&2, A>}

# LAW: replacing gives the new list.
law patch_replace:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  {L.patch(A, L.Replace{ys}, xs) == ys : List<&2, A>}

# LAW: one change then another applies the first, then the second.
law patch_then:
  for -A: Data
  for xs: List<&2, A>
  for a: L.Change<A>
  for b: L.Change<A>
  {L.patch(A, L.Then{a, b}, xs) == L.patch(A, b, L.patch(A, a, xs)) : List<&2, A>}

# Mapping
# -------

# LAW: mapping the empty list gives the empty list.
law map_nil:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  {L.map(~A, ~B, ~f, Nil{}) == Nil{} : List<&2, B>}

# LAW: mapping h <> t gives f(h) <> map(t).
law map_con:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for h: A
  for t: List<&2, A>
  {L.map(~A, ~B, ~f, h <> t) == f(h) <> L.map(~A, ~B, ~f, t) : List<&2, B>}

# The derivative of map
# ---------------------

# LAW: map.change is correct: changing a list and then mapping it gives
# the same list as mapping it and then applying the mapped change.
law map_change:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for xs: List<&2, A>
  for dx: L.Change<A>
  {L.map(~A, ~B, ~f, L.patch(A, dx, xs)) == L.patch(B, L.map.change(~A, ~B, ~f, dx), L.map(~A, ~B, ~f, xs)) : List<&2, B>}

# LAW: map.change is local: the mapped change touches exactly the
# positions the change touched, and replaces with a list as long.
law map_change_local:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for dx: L.Change<A>
  {L.shape(B, L.map.change(~A, ~B, ~f, dx)) == L.shape(A, dx) : L.Shape}
