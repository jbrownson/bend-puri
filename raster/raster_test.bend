import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
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
  unless(U32.is_eq(S.Spec.pixel(d, img, G.int(0), G.int(0), p), S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg)))

def row(+n: Nat, +x: U32, +y: U32, +img: Image, +d: Nat, +cmds: +List<R.Draw>, +bg: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n+k:
      (mismatch(img, d, cmds, bg, G.Point.of(x, y)) + row(k, (x + 1 : U32), y, img, d, cmds, bg) : U32)

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
  [R.FillRect{G.Rect.of(3, 5, 11, 7), 1}, R.FillRect{G.Rect.of(9, 2, 4, 20), 2}, R.FillRect{G.Rect.of(0, 0, 1, 1), 3},
   R.FillRect{G.Rect.of(20, 20, 40, 40), 4}, R.FillRect{G.Rect.of(7, 7, 0, 5), 5}, R.FillRect{G.Rect.of(15, 0, 2, 32), 6},
   R.FillRect{G.Rect.of(1, 30, 30, 1), 7}]

# A rectangle covering everything, then smaller ones on top.
def covered() -> +List<R.Draw>:
  [R.FillRect{G.Rect.of(0, 0, 32, 32), 8}, R.FillRect{G.Rect.of(4, 4, 8, 8), 9}, R.FillRect{G.Rect.of(16, 16, 16, 16), 10}]

# The boxes app with box 2 selected, at the window's real size.
def boxes() -> +List<R.Draw>:
  [R.FillRect{G.Rect.of(60, 60, 200, 160), 4878245}, R.FillRect{G.Rect.of(180, 140, 220, 160), 15774761},
   R.FillRect{G.Rect.of(300, 40, 120, 80), 7317724}, R.FillRect{G.Rect.of(30, 170, 120, 120), 8421504}]

# The geometric facts the raster's proof assumes, tried on every combination
# of the values below, which include both ends of I32's range. Each fact is
# checked one axis at a time, with the other axis set so its part holds.

def vals() -> +List<I.I32>:
  [G.int(0), G.int(1), G.int(2), G.int(3), G.int(5), G.int(7), G.int(2147483646), G.int(2147483647),
   G.int(2147483648), G.int(2147483649), G.int(4294967294), G.int(4294967295)]

def big() -> I.I32:
  G.int(2147483647)

def zero() -> I.I32:
  G.int(0)

def violates(premise: Bool, conclusion: Bool) -> U32:
  match premise:
    case True{}:
      unless(conclusion)
    case False{}:
      0

def meet_bad(+r: G.Rect, +p: G.Point, +x0: I.I32, +y0: I.I32, +s: I.I32) -> U32:
  violates(Bool.and(G.Rect.contains(r, p), G.Rect.contains(G.Rect{x0, y0, s, s}, p)), R.meets(r, x0, y0, s))

def cover_bad(+r: G.Rect, +p: G.Point, +x0: I.I32, +y0: I.I32, +s: I.I32) -> U32:
  violates(Bool.and(R.covers(r, x0, y0, s), G.Rect.contains(G.Rect{x0, y0, s, s}, p)), G.Rect.contains(r, p))

def unit_bad(+px: I.I32, +x0: I.I32, +py: I.I32, +y0: I.I32) -> U32:
  violates(G.Rect.contains(G.Rect{x0, y0, R.side(0n), R.side(0n)}, G.Point{px, py}), Bool.and(I.I32.is_eq(px, x0), I.I32.is_eq(py, y0)))

def quarter_bad(+e: Nat, +x0: I.I32, +px: I.I32, +y0: I.I32, +py: I.I32) -> U32:
  violates(G.Rect.contains(G.Rect{x0, y0, R.side(1n+e), R.side(1n+e)}, G.Point{px, py}),
    G.Rect.contains(G.Rect{
      S.Spec.half((x0 + R.side(e) <= px : I.I32), x0, R.side(e)),
      S.Spec.half((y0 + R.side(e) <= py : I.I32), y0, R.side(e)),
      R.side(e), R.side(e)}, G.Point{px, py}))

# Which fact to try on coordinates a..e (k is the quarter fact's exponent).
def fact(+which: Nat, +k: Nat, +a: I.I32, +b: I.I32, +c: I.I32, +d: I.I32, +e: I.I32) -> U32:
  match which:
    case 0n:
      meet_bad(G.Rect{a, zero(), b, big()}, G.Point{c, zero()}, d, zero(), e)
    case 1n:
      meet_bad(G.Rect{zero(), a, big(), b}, G.Point{zero(), c}, zero(), d, e)
    case 2n:
      cover_bad(G.Rect{a, zero(), b, big()}, G.Point{c, zero()}, d, zero(), e)
    case 3n:
      cover_bad(G.Rect{zero(), a, big(), b}, G.Point{zero(), c}, zero(), d, e)
    case 4n:
      unit_bad(a, b, c, d)
    case _:
      quarter_bad(k, a, b, c, d)

def loop5(+which: Nat, +k: Nat, +a: I.I32, +b: I.I32, +c: I.I32, +d: I.I32, es: +List<I.I32>) -> U32:
  match es:
    case Nil{}:
      0
    case Con{+e, rest}:
      (fact(which, k, a, b, c, d, e) + loop5(which, k, a, b, c, d, rest) : U32)

def loop4(+which: Nat, +k: Nat, +a: I.I32, +b: I.I32, +c: I.I32, ds: +List<I.I32>) -> U32:
  match ds:
    case Nil{}:
      0
    case Con{+d, rest}:
      (loop5(which, k, a, b, c, d, vals()) + loop4(which, k, a, b, c, rest) : U32)

def loop3(+which: Nat, +k: Nat, +a: I.I32, +b: I.I32, cs: +List<I.I32>) -> U32:
  match cs:
    case Nil{}:
      0
    case Con{+c, rest}:
      (loop4(which, k, a, b, c, vals()) + loop3(which, k, a, b, rest) : U32)

def loop2(+which: Nat, +k: Nat, +a: I.I32, bs: +List<I.I32>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{+b, rest}:
      (loop3(which, k, a, b, vals()) + loop2(which, k, a, rest) : U32)

def loop1(+which: Nat, +k: Nat, as: +List<I.I32>) -> U32:
  match as:
    case Nil{}:
      0
    case Con{+a, rest}:
      (loop2(which, k, a, vals()) + loop1(which, k, rest) : U32)

def tries(+which: Nat, +k: Nat) -> U32:
  loop1(which, k, vals())

# The quarter fact for several exponents, including ones past I32's width.
def quarters(ks: +List<Nat>) -> U32:
  match ks:
    case Nil{}:
      0
    case Con{+k, rest}:
      (tries(5n, k) + quarters(rest) : U32)

def report_fact(name: String, bad: U32) -> IO(Unit):
  IO.print(name ++ ": " ++ U32.show(bad) ++ " counterexamples")

def main() -> IO(Unit):
  do IO<Unit>:
    report("empty, 32x32", check(5n, [], 2106408))
    report("mixed, 32x32", check(5n, mixed(), 2106408))
    report("covered, 32x32", check(5n, covered(), 2106408))
    report("boxes, 512x512", check(9n, boxes(), 2106408))
    report_fact("Fact.meet", (tries(0n, 0n) + tries(1n, 0n) : U32))
    report_fact("Fact.cover", (tries(2n, 0n) + tries(3n, 0n) : U32))
    report_fact("Fact.unit", tries(4n, 0n))
    report_fact("Fact.quarter", quarters([0n, 1n, 2n, 5n, 29n, 30n, 31n, 32n, 33n]))
