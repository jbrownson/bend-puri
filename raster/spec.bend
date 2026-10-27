import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import ../puri/geom.bend as G
import ./raster.bend as R

# What the raster must produce, stated the slow, obvious way, one point at
# a time.

def Spec.pick(hit: Bool, rgb: U32, below: U32) -> U32:
  match hit:
    case True{}:
      rgb
    case False{}:
      below

# The color the commands give a point, with the commands listed top first:
# the first one whose rectangle contains the point, or the background.
def Spec.color(cmds: +List<R.Draw>, +p: G.Point, +bg: U32) -> U32:
  match cmds:
    case Nil{}:
      bg
    case Con{R.FillRect{+r, rgb}, rest}:
      Spec.pick(G.Rect.contains(r, p), rgb, Spec.color(rest, p, bg))

def Spec.quarter(right: Bool, low: Bool, tl: Image, tr: Image, bl: Image, br: Image) -> Image:
  match right low:
    case False{} False{}:
      tl
    case True{} False{}:
      tr
    case False{} True{}:
      bl
    case True{} True{}:
      br

def Spec.half(upper: Bool, +a: I.I32, +s: I.I32) -> I.I32:
  match upper:
    case True{}:
      (a + s : I.I32)
    case False{}:
      a

# The color an image gives a point, for an image of the square of side 2^d
# at (x0, y0): descend into the quarter that holds the point.
def Spec.pixel(+d: Nat, img: Image, +x0: I.I32, +y0: I.I32, +p: G.Point) -> U32:
  match d img:
    case _ Pix{c}:
      c
    case 0n Qua{tl, tr, bl, br}:
      0
    case 1n+e Qua{tl, tr, bl, br}:
      match p:
        case G.Point{+px, +py}:
          +s = R.side(e)
          +right = (x0 + s <= px : I.I32)
          +low = (y0 + s <= py : I.I32)
          Spec.pixel(e, Spec.quarter(right, low, tl, tr, bl, br), Spec.half(right, x0, s), Spec.half(low, y0, s), G.Point{px, py})

# Geometric facts the proof of the raster rests on. Each holds for every I32
# value, wraparound included, and PROOF.bend proves all four.

# A rectangle that contains a point inside a square meets the square.
def Fact.meet() -> Type:
  (@r: G.Rect -> @p: G.Point -> @x0: I.I32 -> @y0: I.I32 -> @s: I.I32 ->
    {G.Rect.contains(r, p) == True{} : Bool} ->
    {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool} ->
    {R.meets(r, x0, y0, s) == True{} : Bool})

# A rectangle that covers a square contains every point inside it.
def Fact.cover() -> Type:
  (@r: G.Rect -> @p: G.Point -> @x0: I.I32 -> @y0: I.I32 -> @s: I.I32 ->
    {R.covers(r, x0, y0, s) == True{} : Bool} ->
    {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool} ->
    {G.Rect.contains(r, p) == True{} : Bool})

# The only point inside a 1x1 square is its corner.
def Fact.unit() -> Type:
  (@p: G.Point -> @x0: I.I32 -> @y0: I.I32 ->
    {G.Rect.contains(G.Rect{x0, y0, R.side(0n), R.side(0n)}, p) == True{} : Bool} ->
    {p == G.Point{x0, y0} : G.Point})

# A point inside a square of side 2^(e+1) is inside the quarter of side 2^e
# that Spec.pixel descends into.
def Fact.quarter() -> Type:
  (@x0: I.I32 -> @y0: I.I32 -> @e: Nat -> @px: I.I32 -> @py: I.I32 ->
    {G.Rect.contains(G.Rect{x0, y0, R.side(1n+e), R.side(1n+e)}, G.Point{px, py}) == True{} : Bool} ->
    {G.Rect.contains(G.Rect{
        Spec.half((x0 + R.side(e) <= px : I.I32), x0, R.side(e)),
        Spec.half((y0 + R.side(e) <= py : I.I32), y0, R.side(e)),
        R.side(e), R.side(e)}, G.Point{px, py}) == True{} : Bool})
