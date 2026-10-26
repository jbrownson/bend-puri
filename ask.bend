import Base

# Asking a stack of placements a question: the one placed later (on top)
# answers first, and only a decline (None) falls through to the one below.
# Event handling and hover both work this way.
def Ask(-X: Data, -Y: Type) -> Type:
  X -> Maybe<Y>

# The answer that declines everything.
def Ask.none(-X: Data, -Y: Type) -> Ask(X, Y):
  x => None{}

# Internal to Ask.over: keep the upper answer, or ask the base only when
# the upper one declined. Taking base and x separately, rather than
# base(x), means the base is never asked unless it is needed.
def Ask.fallback(-X: Data, -Y: Type, r: Maybe<Y>, base: Ask(X, Y), x: X) -> Maybe<Y>:
  match r:
    case Some{y}:
      Some{y}
    case None{}:
      base(x)

# Stack `above` on `base`: placed later, asked first.
def Ask.over(-X: Data, -Y: Type, base: Ask(X, Y), above: Ask(X, Y)) -> Ask(X, Y):
  +x => Ask.fallback(X, Y, above(x), base, x)
