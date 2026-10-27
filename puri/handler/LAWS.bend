import Base
import ../ask/ask.bend as A
import ./handler.bend as Hd

# What handlers promise; PROOF.bend proves it. A Handler(Act, E) is an Ask
# from events E to actions Act.

# LAW: the empty handler is the empty Ask.
law handler_empty:
  for -Act: Type
  for -E: Data
  {Hd.Handler.empty(Act, E) == A.Ask.none(E, Act) : Hd.Handler(Act, E)}

# LAW: handlers stack as Asks.
law handler_over:
  for -Act: Type
  for -E: Data
  for base: Hd.Handler(Act, E)
  for above: Hd.Handler(Act, E)
  {Hd.Handler.over(Act, E, base, above) == A.Ask.over(E, Act, base, above) : Hd.Handler(Act, E)}
