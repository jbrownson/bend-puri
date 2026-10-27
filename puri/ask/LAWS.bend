import Base
import ./ask.bend as A

# What asking a stack promises; PROOF.bend proves it. An Ask(X, Y) answers
# a question x with Some{y}, or declines with None{}. Handlers and hover
# probes are both Asks.

# LAW: the empty Ask declines everything.
law none_declines:
  for -X: Data
  for -Y: Type
  for x: X
  {A.Ask.none(X, Y)(x) == None{} : Maybe<Y>}

# LAW: if the layer on top answers, that is the answer.
law over_answered:
  for -X: Data
  for -Y: Type
  for base: A.Ask(X, Y)
  for above: A.Ask(X, Y)
  for +x: X
  for -y: Y
  for e: {above(x) == Some{y} : Maybe<Y>}
  {A.Ask.over(X, Y, base, above)(x) == Some{y} : Maybe<Y>}

# LAW: if the layer on top declines, the base answers.
law over_declined:
  for -X: Data
  for -Y: Type
  for base: A.Ask(X, Y)
  for above: A.Ask(X, Y)
  for +x: X
  for e: {above(x) == None{} : Maybe<Y>}
  {A.Ask.over(X, Y, base, above)(x) == base(x) : Maybe<Y>}

# It follows that:

# LAW: an empty base changes nothing.
law over_none_base:
  for -X: Data
  for -Y: Type
  for q: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, A.Ask.none(X, Y), q)(x) == q(x) : Maybe<Y>}

# LAW: an empty layer on top changes nothing.
law over_none_above:
  for -X: Data
  for -Y: Type
  for q: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, q, A.Ask.none(X, Y))(x) == q(x) : Maybe<Y>}

# LAW: how three layers are grouped doesn't matter, only their order.
law over_assoc:
  for -X: Data
  for -Y: Type
  for a: A.Ask(X, Y)
  for b: A.Ask(X, Y)
  for c: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, A.Ask.over(X, Y, a, b), c)(x) == A.Ask.over(X, Y, a, A.Ask.over(X, Y, b, c))(x) : Maybe<Y>}
