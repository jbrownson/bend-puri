import Base
import ./handler.bend as P

# LAW: adding the empty handler underneath changes nothing.
law plus_empty_left:
  for -M: Type -> Type
  for -E: Data
  for h: P.Handler(M, E)
  for +e: E
  {P.Handler.plus(M, E, P.Handler.empty(M, E), h)(e) == h(e) : Maybe<M(Unit)>}

# LAW: adding the empty handler on top changes nothing.
law plus_empty_right:
  for -M: Type -> Type
  for -E: Data
  for h: P.Handler(M, E)
  for +e: E
  {P.Handler.plus(M, E, h, P.Handler.empty(M, E))(e) == h(e) : Maybe<M(Unit)>}

# LAW: how three handlers are grouped doesn't matter, only their order.
law plus_assoc:
  for -M: Type -> Type
  for -E: Data
  for a: P.Handler(M, E)
  for b: P.Handler(M, E)
  for c: P.Handler(M, E)
  for +e: E
  {P.Handler.plus(M, E, P.Handler.plus(M, E, a, b), c)(e) == P.Handler.plus(M, E, a, P.Handler.plus(M, E, b, c))(e) : Maybe<M(Unit)>}

# LAW: when the later handler answers, its answer wins.
law later_wins:
  for -M: Type -> Type
  for -E: Data
  for earlier: P.Handler(M, E)
  for t: M(Unit)
  for +e: E
  {P.Handler.plus(M, E, earlier, x => Some{t})(e) == Some{t} : Maybe<M(Unit)>}
