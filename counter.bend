import Base
import ./handler.bend as P

# Any key press counts up.
def on_key(e: Event) -> Maybe<(U32 -> U32)>:
  match e:
    case Key{_, True{}}:
      Some{n => (n + 1 : U32)}
    case _:
      None{}

# Escape (key 27) resets the counter.
def on_escape(e: Event) -> Maybe<(U32 -> U32)>:
  match e:
    case Key{27, True{}}:
      Some{n => 0}
    case _:
      None{}

# on_escape is added later, so it wins when both answer.
def handlers() -> P.Handler(U32, Event):
  P.Handler.plus(U32, Event, e => on_key(e), e => on_escape(e))

def apply(r: Maybe<(U32 -> U32)>, s: U32) -> U32:
  match r:
    case Some{t}:
      t(s)
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
