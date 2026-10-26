import Base

type Point is Data:
  Point{x: U32, y: U32}

type Rect is Data:
  Rect{x: U32, y: U32, w: U32, h: U32}

def Rect.contains(r: Rect, p: Point) -> Bool:
  match r p:
    case Rect{+x, +y, +w, +h} Point{+px, +py}:
      Bool.and(
        Bool.and(U32.is_le(x, px), U32.is_lt(px, (x + w : U32))),
        Bool.and(U32.is_le(y, py), U32.is_lt(py, (y + h : U32))))
