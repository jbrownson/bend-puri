import Base
import ./handler.bend as P

# The app's action type: read the counter, produce a result and a new counter.
def Count(A: Type) -> Type:
  U32 -> A & U32

# Any key press counts up.
def on_key(e: Event) -> Maybe<Count(Unit)>:
  match e:
    case Key{_, True{}}:
      Some{n => (Unit{}, (n + 1 : U32))}
    case _:
      None{}

# Escape (key 27) resets the counter.
def on_escape(e: Event) -> Maybe<Count(Unit)>:
  match e:
    case Key{27, True{}}:
      Some{n => (Unit{}, 0)}
    case _:
      None{}

# on_escape is added later, so it wins when both answer.
def handlers() -> P.Handler(A => Count(A), Event):
  P.Handler.over(A => Count(A), Event, e => on_key(e), e => on_escape(e))

def finish(r: Unit & U32) -> U32:
  (_, s) = r
  s

def apply(r: Maybe<Count(Unit)>, s: U32) -> U32:
  match r:
    case Some{t}:
      finish(t(s))
    case None{}:
      s

# A handler is one-shot, so each event gets a freshly built one.
def run(events: List<Event>, s: U32) -> U32:
  match events:
    case Nil{}:
      s
    case Con{e, rest}:
      run(rest, apply(handlers()(e), s))

def main() -> U32:
  run([Key{65, True{}}, Key{66, True{}}, Key{66, False{}}, Key{27, True{}}, Key{67, True{}}], 0)
