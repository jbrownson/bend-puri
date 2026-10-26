import Base
import ./handler.bend as P

# LAW: adding the empty handler underneath changes nothing.
law plus_empty_left:
  for -S: Type
  for -E: Data
  for h: P.Handler(S, E)
  for +e: E
  {P.Handler.plus(S, E, P.Handler.empty(S, E), h)(e) == h(e) : Maybe<(S -> S)>}

# LAW: adding the empty handler on top changes nothing.
law plus_empty_right:
  for -S: Type
  for -E: Data
  for h: P.Handler(S, E)
  for +e: E
  {P.Handler.plus(S, E, h, P.Handler.empty(S, E))(e) == h(e) : Maybe<(S -> S)>}

# LAW: how three handlers are grouped doesn't matter, only their order.
law plus_assoc:
  for -S: Type
  for -E: Data
  for a: P.Handler(S, E)
  for b: P.Handler(S, E)
  for c: P.Handler(S, E)
  for +e: E
  {P.Handler.plus(S, E, P.Handler.plus(S, E, a, b), c)(e) == P.Handler.plus(S, E, a, P.Handler.plus(S, E, b, c))(e) : Maybe<(S -> S)>}

# LAW: when the later handler answers, its answer wins.
law later_wins:
  for -S: Type
  for -E: Data
  for earlier: P.Handler(S, E)
  for t: S -> S
  for +e: E
  {P.Handler.plus(S, E, earlier, x => Some{t})(e) == Some{t} : Maybe<(S -> S)>}
