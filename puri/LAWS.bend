import Base
import ./ask.bend as A

# These laws are about Ask, so they hold for event handlers and for
# hover probes alike.

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

# LAW: when the layer on top answers, its answer wins.
law above_wins:
  for -X: Data
  for -Y: Type
  for base: A.Ask(X, Y)
  for y: Y
  for +x: X
  {A.Ask.over(X, Y, base, z => Some{y})(x) == Some{y} : Maybe<Y>}
