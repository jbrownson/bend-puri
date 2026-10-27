import Base
import ../puri/handler.bend as Hd
import ../puri/geom.bend as G
import ../puri/frame.bend as F
import ../raster/raster.bend as R

# Boxes you can hover and click. Run with: bend app.bend

# The app's state: where the pointer rests, and which box is selected
# (0 for none). Puri keeps nothing; all of it lives here.
type Model is Data:
  Model{pointer: G.Point, selected: U32}

# The app's action type: a transition of the model.
def Act() -> Type:
  Model -> Model

def Scene() -> Type:
  F.Frame<Act(), Event, U32, R.Draw>

type Color is Data:
  Plain{}
  Hovered{}
  Selected{}
  Shaded{}

def Color.rgb(c: Color) -> U32:
  match c:
    case Plain{}:
      4878245
    case Hovered{}:
      7317724
    case Selected{}:
      15774761
    case Shaded{}:
      8421504

def background() -> U32:
  2106408

def select(+id: U32, m: Model) -> Model:
  match m:
    case Model{p, s}:
      Model{p, id}

def box.claim(inside: Bool, id: U32) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Direct{id}}
    case False{}:
      None{}

def box.click(inside: Bool, +id: U32) -> Maybe<Act()>:
  match inside:
    case True{}:
      Some{m => select(id, m)}
    case False{}:
      None{}

# A box handles a press inside it by selecting itself.
def box.on(+r: G.Rect, +id: U32, e: Event) -> Maybe<Act()>:
  match e:
    case Mouse{+x, +y, _, True{}}:
      box.click(G.Rect.contains(r, G.Point.of(x, y)), id)
    case _:
      None{}

def box.hovered(hit: Bool) -> Color:
  match hit:
    case True{}:
      Hovered{}
    case False{}:
      Plain{}

def box.unselected(h: Maybe<&2, U32>, +id: U32) -> Color:
  match h:
    case Some{t}:
      box.hovered(U32.is_eq(t, id))
    case None{}:
      Plain{}

def box.color(is_selected: Bool, h: Maybe<&2, U32>, +id: U32) -> Color:
  match is_selected:
    case True{}:
      Selected{}
    case False{}:
      box.unselected(h, id)

# A box: selects itself when pressed, claims the pointer over its rect,
# and paints itself by whether it is selected or hovered.
def box(+r: G.Rect, +id: U32, +selected: U32) -> Scene():
  F.Frame{
    e => box.on(r, id, e),
    p => box.claim(G.Rect.contains(r, p), id),
    h => [R.FillRect{r, Color.rgb(box.color(U32.is_eq(selected, id), h, id))}]}

def panel.claim(inside: Bool) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Occludes{}}
    case False{}:
      None{}

def panel.click(inside: Bool) -> Maybe<Act()>:
  match inside:
    case True{}:
      Some{m => m}
    case False{}:
      None{}

# A press inside a panel is consumed and changes nothing, so it can't
# reach what lies beneath.
def panel.on(+r: G.Rect, e: Event) -> Maybe<Act()>:
  match e:
    case Mouse{+x, +y, _, True{}}:
      panel.click(G.Rect.contains(r, G.Point.of(x, y)))
    case _:
      None{}

# A panel names no target, but covers what lies beneath it, for hover and
# for presses alike.
def panel(+r: G.Rect) -> Scene():
  F.Frame{
    e => panel.on(r, e),
    p => panel.claim(G.Rect.contains(r, p)),
    h => [R.FillRect{r, Color.rgb(Shaded{})}]}

def over(base: Scene(), above: Scene()) -> Scene():
  F.Frame.over(Act(), Event, U32, R.Draw, base, above)

# The whole UI, built fresh from the model.
def scene(+selected: U32) -> Scene():
  over(over(over(
    box(G.Rect.of(60, 60, 200, 160), 1, selected),
    box(G.Rect.of(180, 140, 220, 160), 2, selected)),
    box(G.Rect.of(300, 40, 120, 80), 3, selected)),
    panel(G.Rect.of(30, 170, 120, 120)))

def Model.selected(m: Model) -> U32:
  match m:
    case Model{p, s}:
      s

# Just the scene's handler, for routing an event. The probe and the ink
# are dropped without running.
def Scene.handler(f: Scene()) -> Hd.Handler(Act(), Event):
  match f:
    case F.Frame{handler, probe, ink}:
      handler

def apply(r: Maybe<Act()>, m: Model) -> Model:
  match r:
    case Some{t}:
      t(m)
    case None{}:
      m

# One event: pointer motion updates the model directly; any other event
# goes to a freshly built frame's handler.
def handle(e: Event, +m: Model) -> Model:
  match e:
    case Move{+x, +y}:
      Model{G.Point.of(x, y), Model.selected(m)}
    case _:
      apply(Scene.handler(scene(Model.selected(m)))(e), m)

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

def Model.pointer(m: Model) -> G.Point:
  match m:
    case Model{p, s}:
      p

def painting(r: Hd.Handler(Act(), Event) & List<&2, R.Draw>) -> List<&2, R.Draw>:
  (_, paint) = r
  paint

# Present the scene at the pointer, then rasterize its painting.
def view(+m: Model) -> Model & Image:
  +cmds = painting(F.Frame.present(Act(), Event, U32, R.Draw, scene(Model.selected(m)), Model.pointer(m)))
  (m, R.Raster.image(9n, cmds, background()))

def initial() -> Model:
  Model{G.Point.of(0, 0), 0}

def main() -> IO(Unit):
  App.run(~Model, ~App{+m => view(m), tick}, "Puri boxes", 480, 360, initial())
