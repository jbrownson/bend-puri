import Base
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

def Spec.half(upper: Bool, +a: U32, +s: U32) -> U32:
  match upper:
    case True{}:
      (a + s : U32)
    case False{}:
      a

# The color an image gives a point, for an image of the square of side 2^d
# at (x0, y0): descend into the quarter that holds the point.
def Spec.pixel(+d: Nat, img: Image, +x0: U32, +y0: U32, +p: G.Point) -> U32:
  match d img:
    case _ Pix{c}:
      c
    case 0n Qua{tl, tr, bl, br}:
      0
    case 1n+e Qua{tl, tr, bl, br}:
      match p:
        case G.Point{+px, +py}:
          +s = U32.shln(1, e)
          +right = U32.is_le((x0 + s : U32), px)
          +low = U32.is_le((y0 + s : U32), py)
          Spec.pixel(e, Spec.quarter(right, low, tl, tr, bl, br), Spec.half(right, x0, s), Spec.half(low, y0, s), G.Point{px, py})
