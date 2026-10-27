import Base
import ../puri/handler.bend as P

# The app's actions: steps that read and update the counter, producing a
# result of type A. Puri only ever sees Count(Unit); A is for composing
# steps inside a handler.
def Count(A: Type) -> Type:
  U32 -> A & U32

def Count.pure(-A: Type, a: A) -> Count(A):
  s => (a, s)

def Count.next(-A: Type, -B: Type, r: A & U32, k: A -> Count(B)) -> B & U32:
  (a, s) = r
  k(a)(s)

# Run v, then the step k picks from its result. `do Count<..>` uses this
# and Count.pure.
def Count.bind(-A: Type, -B: Type, v: Count(A), k: A -> Count(B)) -> Count(B):
  s => Count.next(A, B, v(s), k)

def get() -> Count(U32):
  +s => (s, s)

def put(n: U32) -> Count(Unit):
  s => (Unit{}, n)

# Read the counter, then write it back one higher.
def bump() -> Count(Unit):
  do Count<Unit>:
    n : U32 <- get()
    put((n + 1 : U32))

# Any key press counts up.
def on_key(e: Event) -> Maybe<Count(Unit)>:
  match e:
    case Key{_, True{}}:
      Some{bump()}
    case _:
      None{}

# Escape (key 27) resets the counter.
def on_escape(e: Event) -> Maybe<Count(Unit)>:
  match e:
    case Key{27, True{}}:
      Some{put(0)}
    case _:
      None{}

# on_escape is added later, so it wins when both answer.
def handlers() -> P.Handler(Count(Unit), Event):
  P.Handler.over(Count(Unit), Event, e => on_key(e), e => on_escape(e))

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

# A, B, B released, Escape, C, D: the count ends at 2.
def main() -> U32:
  run([Key{65, True{}}, Key{66, True{}}, Key{66, False{}}, Key{27, True{}}, Key{67, True{}}, Key{68, True{}}], 0)
