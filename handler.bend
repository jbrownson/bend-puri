import Base
import ./ask.bend as A

# A handler looks at an event and either declines (None) or answers
# with an action to run (Some). M is the action type chosen by the
# caller, such as a state transition or an effectful command. The
# handler decides from the event alone, so declining cannot act.
def Handler(-M: Type -> Type, -E: Data) -> Type:
  A.Ask(E, M(Unit))

def Handler.empty(-M: Type -> Type, -E: Data) -> Handler(M, E):
  A.Ask.none(E, M(Unit))

# Stack `above` on `base`: the later handler is asked first.
def Handler.over(-M: Type -> Type, -E: Data, base: Handler(M, E), above: Handler(M, E)) -> Handler(M, E):
  A.Ask.over(E, M(Unit), base, above)
