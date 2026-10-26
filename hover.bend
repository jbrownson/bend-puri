import Base
import ./handler.bend as Hd
import ./frame.bend as F

# The example's draw commands and colors.
type Paint is Data:
  Fill{rect: F.Rect, color: U32}

def cold() -> U32:
  1

def hot() -> U32:
  2

def gray() -> U32:
  3

# This example has no actions, so any action type will do.
def NoAction(A: Type) -> Type:
  Unit

def Scene() -> Type:
  F.Frame<(A => NoAction(A)), Event, U32, Paint>

def box.claim(inside: Bool, id: U32) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Direct{id}}
    case False{}:
      None{}

def box.color.pick(hit: Bool) -> U32:
  match hit:
    case True{}:
      hot()
    case False{}:
      cold()

def box.color(h: Maybe<&2, U32>, +id: U32) -> U32:
  match h:
    case Some{t}:
      box.color.pick(U32.is_eq(t, id))
    case None{}:
      cold()

# A box claims the pointer over its rect, and paints hot when it is the
# hovered target.
def box(+r: F.Rect, +id: U32) -> Scene():
  F.Frame{
    Hd.Handler.empty(A => NoAction(A), Event),
    p => box.claim(F.Rect.contains(r, p), id),
    h => [Fill{r, box.color(h, id)}]}

def panel.claim(inside: Bool) -> Maybe<F.Claim<U32>>:
  match inside:
    case True{}:
      Some{F.Occludes{}}
    case False{}:
      None{}

# A panel names no target, but covers what lies beneath it.
def panel(+r: F.Rect) -> Scene():
  F.Frame{
    Hd.Handler.empty(A => NoAction(A), Event),
    p => panel.claim(F.Rect.contains(r, p)),
    h => [Fill{r, gray()}]}

def over(base: Scene(), above: Scene()) -> Scene():
  F.Frame.over(A => NoAction(A), Event, U32, Paint, base, above)

# Box 1, box 2 overlapping it, and a panel over box 1's top-left corner.
def scene() -> Scene():
  over(over(box(F.Rect{0, 0, 100, 100}, 1), box(F.Rect{50, 50, 100, 100}, 2)), panel(F.Rect{0, 0, 40, 40}))

def painting(r: Hd.Handler(A => NoAction(A), Event) & List<Paint>) -> List<Paint>:
  (_, paint) = r
  paint

def paint_at(p: F.Point) -> List<Paint>:
  painting(F.Frame.present(A => NoAction(A), Event, U32, Paint, scene(), p))

# Pointer in the overlap, on box 1 alone, and under the panel.
def main() -> List<List<Paint>>:
  [paint_at(F.Point{75, 75}), paint_at(F.Point{60, 20}), paint_at(F.Point{20, 20})]
