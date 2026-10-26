import Base

# A handler looks at an event and either declines (None) or answers
# with a transition to apply to the state (Some). It never sees the
# state while deciding, so a declined event cannot change it.
def Handler(-S: Type, -E: Data) -> Type:
  E -> Maybe<(S -> S)>

# The handler that declines everything.
def Handler.empty(-S: Type, -E: Data) -> Handler(S, E):
  e => None{}

# The answer of a combined handler: the later handler's answer wins,
# and only a decline falls through to the earlier handler.
def Handler.fallback(-S: Type, -E: Data, r: Maybe<(S -> S)>, earlier: Handler(S, E), e: E) -> Maybe<(S -> S)>:
  match r:
    case Some{t}:
      Some{t}
    case None{}:
      earlier(e)

# Combine two handlers; the later one has priority.
def Handler.plus(-S: Type, -E: Data, earlier: Handler(S, E), later: Handler(S, E)) -> Handler(S, E):
  +e => Handler.fallback(S, E, later(e), earlier, e)
