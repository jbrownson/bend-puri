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

def Cell.pick(meet: Bool, cover: Bool, rgb: U32, acc: Cell) -> Cell:
  match meet cover:
    case False{} _:
      acc
    case True{} True{}:
      Flat{rgb}
    case True{} False{}:
      Mixed{}

# Paint the commands over a cell in order, back to front: the last command
# that reaches the cell decides whether it stays one color.
def Cell.scan(+cmds: +List<Draw>, +x0: U32, +y0: U32, +s: U32, acc: Cell) -> Cell:
  match cmds:
    case Nil{}:
      acc
    case Con{FillRect{+r, rgb}, rest}:
      Cell.scan(rest, x0, y0, s, Cell.pick(meets(r, x0, y0, s), covers(r, x0, y0, s), rgb, acc))

# The quadtree for a square of side 2^d at (x0, y0). A uniform cell is one
# Pix; a cell with an edge splits into four, down to single pixels.
def raster(+d: Nat, cell: Cell, +x0: U32, +y0: U32, +cmds: +List<Draw>, +bg: U32) -> Image:
  match d cell:
    case 0n Flat{rgb}:
      Pix{rgb}
    case 0n Mixed{}:
      Pix{bg}
    case 1n+e Flat{rgb}:
      Pix{rgb}
    case 1n+e Mixed{}:
      +h = U32.shln(1, e)
      +x1 = (x0 + h : U32)
      +y1 = (y0 + h : U32)
      +s = U32.shln(1, e)
      tl tr bl br = raster(e, Cell.scan(cmds, x0, y0, s, Flat{bg}), x0, y0, cmds, bg)
        raster(e, Cell.scan(cmds, x1, y0, s, Flat{bg}), x1, y0, cmds, bg)
        raster(e, Cell.scan(cmds, x0, y1, s, Flat{bg}), x0, y1, cmds, bg)
        raster(e, Cell.scan(cmds, x1, y1, s, Flat{bg}), x1, y1, cmds, bg)
      Qua{tl, tr, bl, br}

# A whole window: the root square of side 2^d over a background color.
def Raster.image(+d: Nat, +cmds: +List<Draw>, +bg: U32) -> Image:
  raster(d, Cell.scan(cmds, 0, 0, U32.shln(1, d), Flat{bg}), 0, 0, cmds, bg)
