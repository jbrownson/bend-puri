import Base
import ../puri/handler.bend as Hd
import ../puri/geom.bend as G
import ../puri/frame.bend as F

# The example's colors, named by role. A real backend would map them to RGB.
type Color is Data:
  Plain{}
  Hovered{}
  Shaded{}

# The example's draw commands.
type Paint is Data:
  Fill{rect: G.Rect, color: Color}

# This example has no actions, so Unit serves as its action type.
def Scene() -> Type:
  F.Frame<Unit, Event, U32, Paint>

def box.claim(inside: Bool, id: U32) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Direct{id}}
    case False{}:
      None{}

def box.color.pick(hit: Bool) -> Color:
  match hit:
    case True{}:
      Hovered{}
    case False{}:
      Plain{}

def box.color(h: Maybe<&2, U32>, +id: U32) -> Color:
  match h:
    case Some{t}:
      box.color.pick(U32.is_eq(t, id))
    case None{}:
      Plain{}

# A box claims the pointer over its rect, and paints itself as hovered
# when it is the hovered target.
def box(+r: G.Rect, +id: U32) -> Scene():
  F.Frame{
    Hd.Handler.empty(Unit, Event),
    p => box.claim(G.Rect.contains(r, p), id),
    h => [Fill{r, box.color(h, id)}]}

def panel.claim(inside: Bool) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Occludes{}}
    case False{}:
      None{}

# A panel names no target, but covers what lies beneath it.
def panel(+r: G.Rect) -> Scene():
  F.Frame{
    Hd.Handler.empty(Unit, Event),
    p => panel.claim(G.Rect.contains(r, p)),
    h => [Fill{r, Shaded{}}]}

def over(base: Scene(), above: Scene()) -> Scene():
  F.Frame.over(Unit, Event, U32, Paint, base, above)

# Box 1, box 2 overlapping it, and a panel over box 1's top-left corner.
def scene() -> Scene():
  over(over(box(G.Rect.of(0, 0, 100, 100), 1), box(G.Rect.of(50, 50, 100, 100), 2)), panel(G.Rect.of(0, 0, 40, 40)))

def painting(r: Hd.Handler(Unit, Event) & List<&2, Paint>) -> List<&2, Paint>:
  (_, paint) = r
  paint

def paint_at(p: G.Point) -> List<&2, Paint>:
  painting(F.Frame.present(Unit, Event, U32, Paint, scene(), p))

# Pointer in the overlap, on box 1 alone, and under the panel.
def main() -> List<List<&2, Paint>>:
  [paint_at(G.Point.of(75, 75)), paint_at(G.Point.of(60, 20)), paint_at(G.Point.of(20, 20))]
