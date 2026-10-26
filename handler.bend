import Base

# A handler looks at an event and either declines (None) or answers
# with an action to run (Some). M is the action type chosen by the
# caller, such as a state transition or an effectful command. The
# handler decides from the event alone, so declining cannot act.
def Handler(-M: Type -> Type, -E: Data) -> Type:
  E -> Maybe<M(Unit)>

# The handler that declines everything.
def Handler.empty(-M: Type -> Type, -E: Data) -> Handler(M, E):
  e => None{}

# The answer of a combined handler: the later handler's answer wins,
# and only a decline falls through to the earlier handler.
def Handler.fallback(-M: Type -> Type, -E: Data, r: Maybe<M(Unit)>, earlier: Handler(M, E), e: E) -> Maybe<M(Unit)>:
  match r:
    case Some{t}:
      Some{t}
    case None{}:
      earlier(e)

# Combine two handlers; the later one has priority.
def Handler.plus(-M: Type -> Type, -E: Data, earlier: Handler(M, E), later: Handler(M, E)) -> Handler(M, E):
  +e => Handler.fallback(M, E, later(e), earlier, e)
