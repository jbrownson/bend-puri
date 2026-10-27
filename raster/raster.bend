import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import ../puri/geom.bend as G

# The backend's draw command: fill a rectangle with a 0xRRGGBB color.
type Draw is Data:
  FillRect{rect: G.Rect, rgb: U32}

# What a square cell of the window looks like: one color throughout, or
# an edge somewhere inside it.
type Cell is Data:
  Flat{rgb: U32}
  Mixed{}

# Does the rectangle overlap the square of side s at (x0, y0)?
def meets(r: G.Rect, +x0: I.I32, +y0: I.I32, +s: I.I32) -> Bool:
  match r:
    case G.Rect{+x, +y, +w, +h}:
      Bool.and(
        Bool.and((x < x0 + s : I.I32), (x0 < x + w : I.I32)),
        Bool.and((y < y0 + s : I.I32), (y0 < y + h : I.I32)))

# Does the rectangle cover that whole square?
def covers(r: G.Rect, +x0: I.I32, +y0: I.I32, +s: I.I32) -> Bool:
  match r:
    case G.Rect{+x, +y, +w, +h}:
      Bool.and(
        Bool.and((x <= x0 : I.I32), (x0 + s <= x + w : I.I32)),
        Bool.and((y <= y0 : I.I32), (y0 + s <= y + h : I.I32)))

def Cell.covering(cover: Bool, rgb: U32) -> Cell:
  match cover:
    case True{}:
      Flat{rgb}
    case False{}:
      Mixed{}

# A cell's look, from its commands listed top first: no command means the
# background; otherwise the top one decides, by covering the cell or not.
def Cell.of(+kept: +List<Draw>, +x0: I.I32, +y0: I.I32, +s: I.I32, +bg: U32) -> Cell:
  match kept:
    case Nil{}:
      Flat{bg}
    case Con{FillRect{+r, rgb}, rest}:
      Cell.covering(covers(r, x0, y0, s), rgb)

def Cell.pick(hit: Bool, rgb: U32, below: U32) -> U32:
  match hit:
    case True{}:
      rgb
    case False{}:
      below

# The color of the first command that contains the point, or the background.
def first(kept: +List<Draw>, +p: G.Point, +bg: U32) -> U32:
  match kept:
    case Nil{}:
      bg
    case Con{FillRect{+r, rgb}, rest}:
      Cell.pick(G.Rect.contains(r, p), rgb, first(rest, p, bg))

# The side of a cell 2^e pixels wide.
def side(e: Nat) -> I.I32:
  G.int(U32.shln(1, e))

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
def keep(+cmds: +List<Draw>, +x0: I.I32, +y0: I.I32, +s: I.I32) -> +List<Draw>:
  match cmds:
    case Nil{}:
      Nil{}
    case Con{FillRect{+r, +rgb}, rest}:
      keep.pick(meets(r, x0, y0, s), covers(r, x0, y0, s), FillRect{r, rgb}, keep(rest, x0, y0, s))

# The commands that reach each quarter of a cell of side 2s.
def Quads() -> Type:
  +List<Draw> & +List<Draw> & +List<Draw> & +List<Draw>

def split.add(+r: G.Rect, +rgb: U32, +x0: I.I32, +y0: I.I32, +s: I.I32, q: Quads()) -> Quads():
  (a, b, c, d) = q
  +x1 = (x0 + s : I.I32)
  +y1 = (y0 + s : I.I32)
  (keep.pick(meets(r, x0, y0, s), covers(r, x0, y0, s), FillRect{r, rgb}, a),
   keep.pick(meets(r, x1, y0, s), covers(r, x1, y0, s), FillRect{r, rgb}, b),
   keep.pick(meets(r, x0, y1, s), covers(r, x0, y1, s), FillRect{r, rgb}, c),
   keep.pick(meets(r, x1, y1, s), covers(r, x1, y1, s), FillRect{r, rgb}, d))

# What keep gives each quarter, in one pass over the cell's commands
# instead of four.
def split(cmds: +List<Draw>, +x0: I.I32, +y0: I.I32, +s: I.I32) -> Quads():
  match cmds:
    case Nil{}:
      (Nil{}, Nil{}, Nil{}, Nil{})
    case Con{FillRect{+r, +rgb}, rest}:
      split.add(r, rgb, x0, y0, s, split(rest, x0, y0, s))

# Hands the four lists to k. raster can't take a computed tuple apart
# itself, and a helper defined before it can't call it.
def quads(q: Quads(), k: +List<Draw> -> +List<Draw> -> +List<Draw> -> +List<Draw> -> Image) -> Image:
  (a, b, c, d) = q
  k(a)(b)(c)(d)

# The quadtree for a square of side 2^d at (x0, y0), given the commands
# that reach it. A uniform cell is one Pix; a cell with an edge splits
# into four, each keeping only the commands that reach it.
def raster(+d: Nat, cell: Cell, +kept: +List<Draw>, +x0: I.I32, +y0: I.I32, +bg: U32) -> Image:
  match d cell:
    case 0n Flat{rgb}:
      Pix{rgb}
    case 0n Mixed{}:
      Pix{first(kept, G.Point{x0, y0}, bg)}
    case 1n+e Flat{rgb}:
      Pix{rgb}
    case 1n+e Mixed{}:
      +s = side(e)
      +x1 = (x0 + s : I.I32)
      +y1 = (y0 + s : I.I32)
      quads(split(kept, x0, y0, s), +k0 => +k1 => +k2 => +k3 =>
        tl tr bl br = raster(e, Cell.of(k0, x0, y0, s, bg), k0, x0, y0, bg)
          raster(e, Cell.of(k1, x1, y0, s, bg), k1, x1, y0, bg)
          raster(e, Cell.of(k2, x0, y1, s, bg), k2, x0, y1, bg)
          raster(e, Cell.of(k3, x1, y1, s, bg), k3, x1, y1, bg)
        Qua{tl, tr, bl, br})

# A whole window: the root square of side 2^d over a background color,
# from commands in painting order (back to front).
def Raster.image(+d: Nat, cmds: +List<Draw>, +bg: U32) -> Image:
  +s = side(d)
  +top = keep(List.reverse(&2, Draw, cmds), G.int(0), G.int(0), s)
  raster(d, Cell.of(top, G.int(0), G.int(0), s, bg), top, G.int(0), G.int(0), bg)
