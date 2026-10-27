import Base
import ../puri/geom.bend as G
import ./raster.bend as R
import ./spec.bend as S

# Compares every pixel of Raster.image with the spec, for a few scenes.

def unless(same: Bool) -> U32:
  match same:
    case True{}:
      0
    case False{}:
      1

def mismatch(+img: Image, +d: Nat, +cmds: +List<R.Draw>, +bg: U32, +p: G.Point) -> U32:
  unless(U32.is_eq(S.Spec.pixel(d, img, 0, 0, p), S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg)))

def row(+n: Nat, +x: U32, +y: U32, +img: Image, +d: Nat, +cmds: +List<R.Draw>, +bg: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n+k:
      (mismatch(img, d, cmds, bg, G.Point{x, y}) + row(k, (x + 1 : U32), y, img, d, cmds, bg) : U32)

def rows(+n: Nat, +w: Nat, +y: U32, +img: Image, +d: Nat, +cmds: +List<R.Draw>, +bg: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n+k:
      (row(w, 0, y, img, d, cmds, bg) + rows(k, w, (y + 1 : U32), img, d, cmds, bg) : U32)

def side(+d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+e:
      Nat.add(side(e), side(e))

# How many pixels of the 2^d square disagree with the spec.
def check(+d: Nat, +cmds: +List<R.Draw>, +bg: U32) -> U32:
  +img = R.Raster.image(d, cmds, bg)
  rows(side(d), side(d), 0, img, d, cmds, bg)

def report(name: String, bad: U32) -> IO(Unit):
  IO.print(name ++ ": " ++ U32.show(bad) ++ " pixels differ")

# Overlaps, edges, a rectangle past the window, an empty one, odd offsets.
def mixed() -> +List<R.Draw>:
  [R.FillRect{G.Rect{3, 5, 11, 7}, 1}, R.FillRect{G.Rect{9, 2, 4, 20}, 2}, R.FillRect{G.Rect{0, 0, 1, 1}, 3},
   R.FillRect{G.Rect{20, 20, 40, 40}, 4}, R.FillRect{G.Rect{7, 7, 0, 5}, 5}, R.FillRect{G.Rect{15, 0, 2, 32}, 6},
   R.FillRect{G.Rect{1, 30, 30, 1}, 7}]

# A rectangle covering everything, then smaller ones on top.
def covered() -> +List<R.Draw>:
  [R.FillRect{G.Rect{0, 0, 32, 32}, 8}, R.FillRect{G.Rect{4, 4, 8, 8}, 9}, R.FillRect{G.Rect{16, 16, 16, 16}, 10}]

# The boxes app with box 2 selected, at the window's real size.
def boxes() -> +List<R.Draw>:
  [R.FillRect{G.Rect{60, 60, 200, 160}, 4878245}, R.FillRect{G.Rect{180, 140, 220, 160}, 15774761},
   R.FillRect{G.Rect{300, 40, 120, 80}, 7317724}, R.FillRect{G.Rect{30, 170, 120, 120}, 8421504}]

def main() -> IO(Unit):
  do IO<Unit>:
    report("empty, 32x32", check(5n, [], 2106408))
    report("mixed, 32x32", check(5n, mixed(), 2106408))
    report("covered, 32x32", check(5n, covered(), 2106408))
    report("boxes, 512x512", check(9n, boxes(), 2106408))
