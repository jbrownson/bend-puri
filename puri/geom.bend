import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I

# Coordinates are signed 32-bit integers (bend-kit-int's I32), so a
# rectangle can sit partly above or left of the window.
type Point is Data:
  Point{x: I.I32, y: I.I32}

type Rect is Data:
  Rect{x: I.I32, y: I.I32, w: I.I32, h: I.I32}

# A coordinate from a U32, such as an event's position or a literal.
def int(n: U32) -> I.I32:
  I.I32.from_u32(n)

def Point.of(x: U32, y: U32) -> Point:
  Point{int(x), int(y)}

def Rect.of(x: U32, y: U32, w: U32, h: U32) -> Rect:
  Rect{int(x), int(y), int(w), int(h)}

def Rect.contains(r: Rect, p: Point) -> Bool:
  match r p:
    case Rect{+x, +y, +w, +h} Point{+px, +py}:
      Bool.and(
        Bool.and((x <= px : I.I32), (px < x + w : I.I32)),
        Bool.and((y <= py : I.I32), (py < y + h : I.I32)))
