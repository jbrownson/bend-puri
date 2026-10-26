import Base
import ./frame.bend as F

# The backend's draw command: fill a rectangle with a 0xRRGGBB color.
type Draw is Data:
  FillRect{rect: F.Rect, rgb: U32}

# What a square cell of the window looks like: one color throughout, or
# an edge somewhere inside it.
type Cell is Data:
  Flat{rgb: U32}
  Mixed{}

# Does the rectangle overlap the square of side s at (x0, y0)?
def meets(r: F.Rect, +x0: U32, +y0: U32, +s: U32) -> Bool:
  match r:
    case F.Rect{+x, +y, +w, +h}:
      ((x < x0 + s) && (x0 < x + w) && (y < y0 + s) && (y0 < y + h) : U32)

# Does the rectangle cover that whole square?
def covers(r: F.Rect, +x0: U32, +y0: U32, +s: U32) -> Bool:
  match r:
    case F.Rect{+x, +y, +w, +h}:
      ((x <= x0) && (x0 + s <= x + w) && (y <= y0) && (y0 + s <= y + h) : U32)

def Cell.covering(cover: Bool, rgb: U32) -> Cell:
  match cover:
    case True{}:
      Flat{rgb}
    case False{}:
      Mixed{}

# A cell's look, from its commands listed top first: no command means the
# background; otherwise the top one decides, by covering the cell or not.
def Cell.of(+kept: +List<Draw>, +x0: U32, +y0: U32, +s: U32, +bg: U32) -> Cell:
  match kept:
    case Nil{}:
      Flat{bg}
    case Con{FillRect{+r, rgb}, rest}:
      Cell.covering(covers(r, x0, y0, s), rgb)

def keep.pick(meet: Bool, cover: Bool, +c: Draw, below: +List<Draw>) -> +List<Draw>:
  match meet cover:
    case False{} _:
      below
    case True{} True{}:
      [c]
    case True{} False{}:
      c <> below

# The commands that reach a cell, top first. A command that covers the
# whole cell hides everything beneath it, so the list stops there.
def keep(+cmds: +List<Draw>, +x0: U32, +y0: U32, +s: U32) -> +List<Draw>:
  match cmds:
    case Nil{}:
      Nil{}
    case Con{FillRect{+r, +rgb}, rest}:
      keep.pick(meets(r, x0, y0, s), covers(r, x0, y0, s), FillRect{r, rgb}, keep(rest, x0, y0, s))

# The quadtree for a square of side 2^d at (x0, y0), given the commands
# that reach it. A uniform cell is one Pix; a cell with an edge splits
# into four, each keeping only the commands that reach it.
def raster(+d: Nat, cell: Cell, +kept: +List<Draw>, +x0: U32, +y0: U32, +bg: U32) -> Image:
  match d cell:
    case 0n Flat{rgb}:
      Pix{rgb}
    case 0n Mixed{}:
      Pix{bg}
    case 1n+e Flat{rgb}:
      Pix{rgb}
    case 1n+e Mixed{}:
      +s = U32.shln(1, e)
      +x1 = (x0 + s : U32)
      +y1 = (y0 + s : U32)
      +k0 = keep(kept, x0, y0, s)
      +k1 = keep(kept, x1, y0, s)
      +k2 = keep(kept, x0, y1, s)
      +k3 = keep(kept, x1, y1, s)
      tl tr bl br = raster(e, Cell.of(k0, x0, y0, s, bg), k0, x0, y0, bg)
        raster(e, Cell.of(k1, x1, y0, s, bg), k1, x1, y0, bg)
        raster(e, Cell.of(k2, x0, y1, s, bg), k2, x0, y1, bg)
        raster(e, Cell.of(k3, x1, y1, s, bg), k3, x1, y1, bg)
      Qua{tl, tr, bl, br}

# A whole window: the root square of side 2^d over a background color,
# from commands in painting order (back to front).
def Raster.image(+d: Nat, cmds: +List<Draw>, +bg: U32) -> Image:
  +s = U32.shln(1, d)
  +top = keep(List.reverse(&2, Draw, cmds), 0, 0, s)
  raster(d, Cell.of(top, 0, 0, s, bg), top, 0, 0, bg)
