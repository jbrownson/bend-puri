import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import ../ilc/change/change.bend as C
import ../ilc/list/list.bend as L
import ../puri/ask/ask.bend as A
import ../puri/handler/handler.bend as Hd
import ../puri/geom.bend as G
import ../puri/frame/frame.bend as F
import ../raster/raster.bend as R

# Bars you can grow, add and remove. Left-click a bar to grow it,
# right-click it to remove it; "+" adds a bar, and the grey button resets.
# Run with: bend bars.bend -o bars && ./bars
#
# Every press becomes a run of list edits. The bars' heights are a mapped
# list kept up to date by patching it with dmap's edits for the run,
# never by mapping the numbers again.

# Numbers that change by "add n".
def adds() -> C.EditStructure:
  C.EditStructure{U32, U32, n => x => (x + n : U32)}

# A run of edits to a list of numbers.
def Edits() -> Data:
  List<&2, L.Edit.of(adds())>

# A bar's height in pixels: 20 per unit. Its derivative turns "add n" into
# "add 20n".
def height() -> C.Inc<adds(), adds()>:
  C.Inc{x => (x * 20 : U32), x => n => (n * 20 : U32)}

def heights.of(xs: List<&2, U32>) -> List<&2, U32>:
  L.map(~U32, ~U32, ~C.Inc.f(adds(), adds(), height()), xs)

# Where the pointer rests, the bars' numbers, and their heights.
type Model is Data:
  Model{pointer: G.Point, values: List<&2, U32>, heights: List<&2, U32>}

def start() -> List<&2, U32>:
  [2, 4, 3]

def initial() -> Model:
  Model{G.Point.of(0, 0), start(), heights.of(start())}

# The app's action: the edits a press makes, given the numbers before it.
def Act() -> Type:
  List<&2, U32> -> Edits()

def Scene() -> Type:
  F.Frame<Act(), Event, U32, R.Draw>

def background() -> U32:
  2106408

def over(base: Scene(), above: Scene()) -> Scene():
  F.Frame.over(Act(), Event, U32, R.Draw, base, above)

def nothing() -> Scene():
  F.Frame{Hd.Handler.empty(Act(), Event), A.Ask.none(G.Point, F.Claim<U32>), h => []}

def claim(inside: Bool, id: U32) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Direct{id}}
    case False{}:
      None{}

def pick(on: Bool, yes: U32, no: U32) -> U32:
  match on:
    case True{}:
      yes
    case False{}:
      no

# A target's color: lit when it's the one hovered.
def lit(h: Maybe<&2, U32>, +id: U32, +plain: U32, +hovered: U32) -> U32:
  match h:
    case Some{t}:
      pick(U32.is_eq(t, id), hovered, plain)
    case None{}:
      plain

# Bars
# ----

# Bar i stands on the floor at y = 320, h pixels tall.
def bar.rect(+i: U32, +h: U32) -> G.Rect:
  G.Rect{G.int((40 + i * 50 : U32)), (G.int(320) - G.int(h) : I.I32), G.int(36), G.int(h)}

# Right-click removes bar i; any other button grows it by 1.
def bar.act(remove: Bool, +i: Nat) -> Act():
  match remove:
    case True{}:
      vs => [L.Delete{i}]
    case False{}:
      vs => [L.Update{i, 1}]

def bar.press(inside: Bool, +b: U32, +i: Nat) -> Maybe<Act()>:
  match inside:
    case True{}:
      Some{bar.act(U32.is_eq(b, 3), i)}
    case False{}:
      None{}

def bar.on(+r: G.Rect, +i: Nat, e: Event) -> Maybe<Act()>:
  match e:
    case Mouse{+x, +y, +b, True{}}:
      bar.press(G.Rect.contains(r, G.Point.of(x, y)), b, i)
    case _:
      None{}

def bar(+r: G.Rect, +i: Nat, +id: U32) -> Scene():
  F.Frame{
    e => bar.on(r, i, e),
    p => claim(G.Rect.contains(r, p), id),
    h => [R.FillRect{r, lit(h, id, 4878245, 7317724)}]}

# The bars, left to right from position i, with hover targets 1, 2, ...
def bars(hs: List<&2, U32>, +i: U32) -> Scene():
  match hs:
    case Nil{}:
      nothing()
    case Con{+h, t}:
      over(bar(bar.rect(i, h), U32.to_nat(i), (i + 1 : U32)), bars(t, (i + 1 : U32)))

# Buttons
# -------

type Button is Data:
  Add{}
  Reset{}

# "+" adds a bar of 1 at the end. Reset goes back to the starting bars,
# by the run diff gives from the bars there are.
def Button.act(b: Button) -> Act():
  match b:
    case Add{}:
      vs => [L.Insert{List.length(&2, U32, vs), 1}]
    case Reset{}:
      vs => L.diff(~adds(), vs, start())

def Button.id(b: Button) -> U32:
  match b:
    case Add{}:
      100
    case Reset{}:
      101

def Button.rect(b: Button) -> G.Rect:
  match b:
    case Add{}:
      G.Rect.of(40, 20, 40, 30)
    case Reset{}:
      G.Rect.of(100, 20, 40, 30)

def Button.rgb(b: Button) -> U32:
  match b:
    case Add{}:
      3912040
    case Reset{}:
      8421504

def Button.lit(b: Button) -> U32:
  match b:
    case Add{}:
      6082681
    case Reset{}:
      11053224

# A "+" for the add button, and nothing on the reset button.
def Button.mark(b: Button) -> List<&2, R.Draw>:
  match b:
    case Add{}:
      [R.FillRect{G.Rect.of(52, 33, 16, 4), 15790320}, R.FillRect{G.Rect.of(58, 27, 4, 16), 15790320}]
    case Reset{}:
      []

def button.press(inside: Bool, +b: Button) -> Maybe<Act()>:
  match inside:
    case True{}:
      Some{Button.act(b)}
    case False{}:
      None{}

def button.on(+b: Button, e: Event) -> Maybe<Act()>:
  match e:
    case Mouse{+x, +y, _, True{}}:
      button.press(G.Rect.contains(Button.rect(b), G.Point.of(x, y)), b)
    case _:
      None{}

def button(+b: Button) -> Scene():
  F.Frame{
    e => button.on(b, e),
    p => claim(G.Rect.contains(Button.rect(b), p), Button.id(b)),
    h => R.FillRect{Button.rect(b), lit(h, Button.id(b), Button.rgb(b), Button.lit(b))} <> Button.mark(b)}

# The app
# -------

# The whole UI, built from the heights.
def scene(hs: List<&2, U32>) -> Scene():
  over(over(button(Add{}), button(Reset{})), bars(hs, 0))

def Model.heights(m: Model) -> List<&2, U32>:
  match m:
    case Model{p, v, h}:
      h

def Model.pointer(m: Model) -> G.Point:
  match m:
    case Model{p, v, h}:
      p

def Scene.handler(f: Scene()) -> Hd.Handler(Act(), Event):
  match f:
    case F.Frame{handler, probe, ink}:
      handler

# The incremental step: patch the numbers by the run, and the heights by
# the run dmap gives for it.
def edit(+es: Edits(), m: Model) -> Model:
  match m:
    case Model{p, +vs, hs}:
      Model{p, L.patch(~adds(), es, vs), L.patch(~adds(), L.dmap(~adds(), ~adds(), ~height(), es, vs), hs)}

def Model.values(m: Model) -> List<&2, U32>:
  match m:
    case Model{p, v, h}:
      v

def step(r: Maybe<Act()>, +m: Model) -> Model:
  match r:
    case Some{act}:
      edit(act(Model.values(m)), m)
    case None{}:
      m

def handle(e: Event, +m: Model) -> Model:
  match e:
    case Move{+x, +y}:
      match m:
        case Model{p, v, h}:
          Model{G.Point.of(x, y), v, h}
    case _:
      step(Scene.handler(scene(Model.heights(m)))(e), m)

def tick.go(events: List<Event>, +m: Model) -> Maybe<Model>:
  match events:
    case Nil{}:
      Some{m}
    case Con{Close{}, rest}:
      None{}
    case Con{e, rest}:
      tick.go(rest, handle(e, m))

def tick(events: List<Event>, m: Model) -> IO(Maybe<Model>):
  IO.pure(Maybe<Model>, tick.go(events, m))

def painting(r: Hd.Handler(Act(), Event) & List<&2, R.Draw>) -> List<&2, R.Draw>:
  (_, paint) = r
  paint

def view(+m: Model) -> Model & Image:
  +cmds = painting(F.Frame.present(Act(), Event, U32, R.Draw, scene(Model.heights(m)), Model.pointer(m)))
  (m, R.Raster.image(9n, cmds, background()))

def main() -> IO(Unit):
  App.run(~Model, ~App{+m => view(m), tick}, "Puri bars", 480, 360, initial())
