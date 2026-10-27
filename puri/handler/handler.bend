import Base
import ../ask/ask.bend as A

# A handler looks at an event and either declines (None) or answers
# with an action to run (Some). Act is the action type chosen by the
# caller, such as a state transition or an effectful command. The
# handler decides from the event alone, so declining cannot act.
def Handler(-Act: Type, -E: Data) -> Type:
  A.Ask(E, Act)

def Handler.empty(-Act: Type, -E: Data) -> Handler(Act, E):
  A.Ask.none(E, Act)

# Stack `above` on `base`: the later handler is asked first.
def Handler.over(-Act: Type, -E: Data, base: Handler(Act, E), above: Handler(Act, E)) -> Handler(Act, E):
  A.Ask.over(E, Act, base, above)
