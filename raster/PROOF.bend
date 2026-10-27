import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import ../puri/geom.bend as G
import ./raster.bend as R
import ./spec.bend as S
import ../puri/order.bend as O
import 0xcdaf59a0332a2e0cdb289bf7a32fba62/bool.bend as B
import ./LAWS.bend as Laws

def Bool.holds(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# Helper: False is not True.
law clash:
  for e: {False{} == True{} : Bool}
  Empty

def clash(e):
  %Equal.sym(Bool, False{}, True{}, e) : Bool.holds(_)
  Unit{}

# Helpers: the four tests of a rectangle check, as one Bool.and of two pairs.
law part1:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}
  {a == True{} : Bool}

def part1(a, b, c, d, e):
  B.eq_true_of_and_left(a, b, B.eq_true_of_and_left(Bool.and(a, b), Bool.and(c, d), e))

law part2:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}
  {b == True{} : Bool}

def part2(a, b, c, d, e):
  B.eq_true_of_and_right(a, b, B.eq_true_of_and_left(Bool.and(a, b), Bool.and(c, d), e))

law part3:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}
  {c == True{} : Bool}

def part3(a, b, c, d, e):
  B.eq_true_of_and_left(c, d, B.eq_true_of_and_right(Bool.and(a, b), Bool.and(c, d), e))

law part4:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}
  {d == True{} : Bool}

def part4(a, b, c, d, e):
  B.eq_true_of_and_right(c, d, B.eq_true_of_and_right(Bool.and(a, b), Bool.and(c, d), e))

law all4:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  for ec: {c == True{} : Bool}
  for ed: {d == True{} : Bool}
  {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}

def all4(a, b, c, d, ea, eb, ec, ed):
  B.and_eq_true(Bool.and(a, b), Bool.and(c, d), B.and_eq_true(a, b, ea, eb), B.and_eq_true(c, d, ec, ed))

# Fact.meet, proved: a rectangle that contains a point inside a square
# meets the square, one axis at a time by transitivity.
law fact_meet:
  for r: G.Rect
  for p: G.Point
  for x0: I.I32
  for y0: I.I32
  for s: I.I32
  for hc: {G.Rect.contains(r, p) == True{} : Bool}
  for hi: {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool}
  {R.meets(r, x0, y0, s) == True{} : Bool}

def fact_meet(r, p, x0, y0, s, hc, hi):
  match r p:
    case G.Rect{+x, +y, +w, +h} G.Point{+px, +py}:
      +X = x0
      +Y = y0
      +S = s
      +C = hc
      +H = hi
      all4((x < X + S : I.I32), (X < x + w : I.I32), (y < Y + S : I.I32), (Y < y + h : I.I32),
        O.le_lt(x, px, (X + S : I.I32),
          part1((x <= px : I.I32), (px < x + w : I.I32), (y <= py : I.I32), (py < y + h : I.I32), C),
          part2((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H)),
        O.le_lt(X, px, (x + w : I.I32),
          part1((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H),
          part2((x <= px : I.I32), (px < x + w : I.I32), (y <= py : I.I32), (py < y + h : I.I32), C)),
        O.le_lt(y, py, (Y + S : I.I32),
          part3((x <= px : I.I32), (px < x + w : I.I32), (y <= py : I.I32), (py < y + h : I.I32), C),
          part4((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H)),
        O.le_lt(Y, py, (y + h : I.I32),
          part3((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H),
          part4((x <= px : I.I32), (px < x + w : I.I32), (y <= py : I.I32), (py < y + h : I.I32), C)))

# Fact.cover, proved: a rectangle that covers a square contains every point
# inside it, one axis at a time by transitivity.
law fact_cover:
  for r: G.Rect
  for p: G.Point
  for x0: I.I32
  for y0: I.I32
  for s: I.I32
  for hv: {R.covers(r, x0, y0, s) == True{} : Bool}
  for hi: {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool}
  {G.Rect.contains(r, p) == True{} : Bool}

def fact_cover(r, p, x0, y0, s, hv, hi):
  match r p:
    case G.Rect{+x, +y, +w, +h} G.Point{+px, +py}:
      +X = x0
      +Y = y0
      +S = s
      +V = hv
      +H = hi
      all4((x <= px : I.I32), (px < x + w : I.I32), (y <= py : I.I32), (py < y + h : I.I32),
        O.le_le(x, X, px,
          part1((x <= X : I.I32), (X + S <= x + w : I.I32), (y <= Y : I.I32), (Y + S <= y + h : I.I32), V),
          part1((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H)),
        O.lt_le(px, (X + S : I.I32), (x + w : I.I32),
          part2((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H),
          part2((x <= X : I.I32), (X + S <= x + w : I.I32), (y <= Y : I.I32), (Y + S <= y + h : I.I32), V)),
        O.le_le(y, Y, py,
          part3((x <= X : I.I32), (X + S <= x + w : I.I32), (y <= Y : I.I32), (Y + S <= y + h : I.I32), V),
          part3((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H)),
        O.lt_le(py, (Y + S : I.I32), (y + h : I.I32),
          part4((X <= px : I.I32), (px < X + S : I.I32), (Y <= py : I.I32), (py < Y + S : I.I32), H),
          part4((x <= X : I.I32), (X + S <= x + w : I.I32), (y <= Y : I.I32), (Y + S <= y + h : I.I32), V)))

# Helper: one command's step of keep, with its three tests as parameters.
law keep_step:
  for +r: G.Rect
  for +rgb: U32
  for rest: +List<R.Draw>
  for +x0: I.I32
  for +y0: I.I32
  for +s: I.I32
  for +p: G.Point
  for +bg: U32
  for m: Bool
  for c: Bool
  for h: Bool
  for eh: {G.Rect.contains(r, p) == h : Bool}
  for meet: {h == True{} : Bool} -> {m == True{} : Bool}
  for cover: {c == True{} : Bool} -> {h == True{} : Bool}
  for ih: {S.Spec.color(R.keep(rest, x0, y0, s), p, bg) == S.Spec.color(rest, p, bg) : U32}
  {S.Spec.color(R.keep.pick(m, c, R.FillRect{r, rgb}, R.keep(rest, x0, y0, s)), p, bg) == S.Spec.pick(h, rgb, S.Spec.color(rest, p, bg)) : U32}

def keep_step(r, rgb, rest, x0, y0, s, p, bg, m, c, h, eh, meet, cover, ih):
  match m c h:
    case False{} _ False{}:
      ih
    case False{} _ True{}:
      Empty.absurd({S.Spec.color(R.keep(rest, x0, y0, s), p, bg) == rgb : U32}, clash(meet({==})))
    case True{} True{} True{}:
      %Equal.sym(Bool, G.Rect.contains(r, p), True{}, eh) : {S.Spec.pick(_, rgb, bg) == rgb : U32}
      {==}
    case True{} True{} False{}:
      Empty.absurd({S.Spec.pick(G.Rect.contains(r, p), rgb, bg) == S.Spec.color(rest, p, bg) : U32}, clash(cover({==})))
    case True{} False{} True{}:
      %Equal.sym(Bool, G.Rect.contains(r, p), True{}, eh) : {S.Spec.pick(_, rgb, S.Spec.color(R.keep(rest, x0, y0, s), p, bg)) == rgb : U32}
      {==}
    case True{} False{} False{}:
      %Equal.sym(Bool, G.Rect.contains(r, p), False{}, eh) : {S.Spec.pick(_, rgb, S.Spec.color(R.keep(rest, x0, y0, s), p, bg)) == S.Spec.color(rest, p, bg) : U32}
      ih

# Lemma: the commands kept for a square color a point inside it as the
# whole list does.
law keep_color:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for cmds: +List<R.Draw>
  for +x0: I.I32
  for +y0: I.I32
  for +s: I.I32
  for +p: G.Point
  for +bg: U32
  for +inside: {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool}
  {S.Spec.color(R.keep(cmds, x0, y0, s), p, bg) == S.Spec.color(cmds, p, bg) : U32}

def keep_color(meet, cover, cmds, x0, y0, s, p, bg, inside):
  match cmds:
    case Nil{}:
      {==}
    case Con{R.FillRect{+r, +rgb}, +rest}:
      keep_step(r, rgb, rest, x0, y0, s, p, bg,
        R.meets(r, x0, y0, s), R.covers(r, x0, y0, s), G.Rect.contains(r, p), {==},
        e => meet(r, p, x0, y0, s, e, inside),
        e => cover(r, p, x0, y0, s, e, inside),
        keep_color(~meet, ~cover, rest, x0, y0, s, p, bg, inside))

def Cell.rgb(c: R.Cell) -> U32:
  match c:
    case R.Flat{x}:
      x
    case R.Mixed{}:
      0

def Cell.flat(c: R.Cell) -> Type:
  match c:
    case R.Flat{x}:
      Unit
    case R.Mixed{}:
      Empty

# Helper: a mixed cell is not flat.
law mixed_clash:
  for -c: U32
  for e: {R.Mixed{} == R.Flat{c} : R.Cell}
  Empty

def mixed_clash(c, e):
  %Equal.sym(R.Cell, R.Mixed{}, R.Flat{c}, e) : Cell.flat(_)
  Unit{}

# Helper: one command's step of Cell.of, with its two tests as parameters.
law flat_step:
  for +r: G.Rect
  for +rgb: U32
  for rest: +List<R.Draw>
  for +p: G.Point
  for +bg: U32
  for +c: U32
  for cv: Bool
  for h: Bool
  for cover: {cv == True{} : Bool} -> {h == True{} : Bool}
  for ec: {R.Cell.covering(cv, rgb) == R.Flat{c} : R.Cell}
  {S.Spec.pick(h, rgb, S.Spec.color(rest, p, bg)) == c : U32}

def flat_step(r, rgb, rest, p, bg, c, cv, h, cover, ec):
  match cv h:
    case True{} True{}:
      Equal.cong(R.Cell, U32, Cell.rgb, R.Flat{rgb}, R.Flat{c}, ec)
    case True{} False{}:
      Empty.absurd({S.Spec.color(rest, p, bg) == c : U32}, clash(cover({==})))
    case False{} _:
      Empty.absurd({S.Spec.pick(h, rgb, S.Spec.color(rest, p, bg)) == c : U32}, mixed_clash(c, ec))

# Lemma: a cell the raster finds to be one color gives every point inside
# it that color.
law flat_color:
  for ~cover: S.Fact.cover()
  for kept: +List<R.Draw>
  for +x0: I.I32
  for +y0: I.I32
  for +s: I.I32
  for +p: G.Point
  for +bg: U32
  for +c: U32
  for ec: {R.Cell.of(kept, x0, y0, s, bg) == R.Flat{c} : R.Cell}
  for +inside: {G.Rect.contains(G.Rect{x0, y0, s, s}, p) == True{} : Bool}
  {S.Spec.color(kept, p, bg) == c : U32}

def flat_color(cover, kept, x0, y0, s, p, bg, c, ec, inside):
  match kept:
    case Nil{}:
      Equal.cong(R.Cell, U32, Cell.rgb, R.Flat{bg}, R.Flat{c}, ec)
    case Con{R.FillRect{+r, +rgb}, +rest}:
      flat_step(r, rgb, rest, p, bg, c, R.covers(r, x0, y0, s), G.Rect.contains(r, p),
        e => cover(r, p, x0, y0, s, e, inside), ec)

# Helper: the raster's pick and the spec's pick agree.
law picks_agree:
  for h: Bool
  for +a: U32
  for +b: U32
  {R.Cell.pick(h, a, b) == S.Spec.pick(h, a, b) : U32}

def picks_agree(h, a, b):
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# Lemma: the raster's first containing command is the spec's color.
law first_color:
  for kept: +List<R.Draw>
  for +q: G.Point
  for +bg: U32
  {R.first(kept, q, bg) == S.Spec.color(kept, q, bg) : U32}

def first_color(kept, q, bg):
  match kept:
    case Nil{}:
      {==}
    case Con{R.FillRect{+r, +rgb}, +rest}:
      %Equal.sym(U32, R.first(rest, q, bg), S.Spec.color(rest, q, bg), first_color(rest, q, bg)) : {R.Cell.pick(G.Rect.contains(r, q), rgb, _) == S.Spec.pick(G.Rect.contains(r, q), rgb, S.Spec.color(rest, q, bg)) : U32}
      picks_agree(G.Rect.contains(r, q), rgb, S.Spec.color(rest, q, bg))

# Helper: one quarter of a split cell, given that the point is inside it
# and that the quarter is rasterized correctly.
law child:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for +e: Nat
  for +kept: +List<R.Draw>
  for +x: I.I32
  for +y: I.I32
  for +bg: U32
  for +px: I.I32
  for +py: I.I32
  for +inside: {G.Rect.contains(G.Rect{x, y, R.side(e), R.side(e)}, G.Point{px, py}) == True{} : Bool}
  for ih: (@c: R.Cell -> @k: +List<R.Draw> -> @x: I.I32 -> @y: I.I32 ->
    {R.Cell.of(k, x, y, R.side(e), bg) == c : R.Cell} ->
    {G.Rect.contains(G.Rect{x, y, R.side(e), R.side(e)}, G.Point{px, py}) == True{} : Bool} ->
    {S.Spec.pixel(e, R.raster(e, c, k, x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(k, G.Point{px, py}, bg) : U32})
  {S.Spec.pixel(e, R.raster(e, R.Cell.of(R.keep(kept, x, y, R.side(e)), x, y, R.side(e), bg), R.keep(kept, x, y, R.side(e)), x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(kept, G.Point{px, py}, bg) : U32}

def child(meet, cover, e, kept, x, y, bg, px, py, inside, ih):
  Equal.trans(U32,
    S.Spec.pixel(e, R.raster(e, R.Cell.of(R.keep(kept, x, y, R.side(e)), x, y, R.side(e), bg), R.keep(kept, x, y, R.side(e)), x, y, bg), x, y, G.Point{px, py}),
    S.Spec.color(R.keep(kept, x, y, R.side(e)), G.Point{px, py}, bg),
    S.Spec.color(kept, G.Point{px, py}, bg),
    ih(R.Cell.of(R.keep(kept, x, y, R.side(e)), x, y, R.side(e), bg), R.keep(kept, x, y, R.side(e)), x, y, {==}, inside),
    keep_color(~meet, ~cover, kept, x, y, R.side(e), G.Point{px, py}, bg, inside))

# Helper: a split cell, with the quarter holding the point as parameters.
law quad_step:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for +e: Nat
  for +kept: +List<R.Draw>
  for +x0: I.I32
  for +y0: I.I32
  for +bg: U32
  for +px: I.I32
  for +py: I.I32
  for right: Bool
  for low: Bool
  for +inside: {G.Rect.contains(G.Rect{S.Spec.half(right, x0, R.side(e)), S.Spec.half(low, y0, R.side(e)), R.side(e), R.side(e)}, G.Point{px, py}) == True{} : Bool}
  for ih: (@c: R.Cell -> @k: +List<R.Draw> -> @x: I.I32 -> @y: I.I32 ->
    {R.Cell.of(k, x, y, R.side(e), bg) == c : R.Cell} ->
    {G.Rect.contains(G.Rect{x, y, R.side(e), R.side(e)}, G.Point{px, py}) == True{} : Bool} ->
    {S.Spec.pixel(e, R.raster(e, c, k, x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(k, G.Point{px, py}, bg) : U32})
  {S.Spec.pixel(e, S.Spec.quarter(right, low, R.raster(e, R.Cell.of(R.keep(kept, x0, y0, R.side(e)), x0, y0, R.side(e), bg), R.keep(kept, x0, y0, R.side(e)), x0, y0, bg), R.raster(e, R.Cell.of(R.keep(kept, (x0 + R.side(e) : I.I32), y0, R.side(e)), (x0 + R.side(e) : I.I32), y0, R.side(e), bg), R.keep(kept, (x0 + R.side(e) : I.I32), y0, R.side(e)), (x0 + R.side(e) : I.I32), y0, bg), R.raster(e, R.Cell.of(R.keep(kept, x0, (y0 + R.side(e) : I.I32), R.side(e)), x0, (y0 + R.side(e) : I.I32), R.side(e), bg), R.keep(kept, x0, (y0 + R.side(e) : I.I32), R.side(e)), x0, (y0 + R.side(e) : I.I32), bg), R.raster(e, R.Cell.of(R.keep(kept, (x0 + R.side(e) : I.I32), (y0 + R.side(e) : I.I32), R.side(e)), (x0 + R.side(e) : I.I32), (y0 + R.side(e) : I.I32), R.side(e), bg), R.keep(kept, (x0 + R.side(e) : I.I32), (y0 + R.side(e) : I.I32), R.side(e)), (x0 + R.side(e) : I.I32), (y0 + R.side(e) : I.I32), bg)), S.Spec.half(right, x0, R.side(e)), S.Spec.half(low, y0, R.side(e)), G.Point{px, py}) == S.Spec.color(kept, G.Point{px, py}, bg) : U32}

def quad_step(meet, cover, e, kept, x0, y0, bg, px, py, right, low, inside, ih):
  match right low:
    case False{} False{}:
      child(~meet, ~cover, e, kept, x0, y0, bg, px, py, inside, ih)
    case True{} False{}:
      child(~meet, ~cover, e, kept, (x0 + R.side(e) : I.I32), y0, bg, px, py, inside, ih)
    case False{} True{}:
      child(~meet, ~cover, e, kept, x0, (y0 + R.side(e) : I.I32), bg, px, py, inside, ih)
    case True{} True{}:
      child(~meet, ~cover, e, kept, (x0 + R.side(e) : I.I32), (y0 + R.side(e) : I.I32), bg, px, py, inside, ih)

# Lemma, by induction on the depth: a cell rasterized from its commands
# gives every point inside it the spec's color.
law raster_color:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for ~unit: S.Fact.unit()
  for ~quarter: S.Fact.quarter()
  for +d: Nat
  for cell: R.Cell
  for +kept: +List<R.Draw>
  for +x0: I.I32
  for +y0: I.I32
  for +bg: U32
  for +p: G.Point
  for ec: {R.Cell.of(kept, x0, y0, R.side(d), bg) == cell : R.Cell}
  for +inside: {G.Rect.contains(G.Rect{x0, y0, R.side(d), R.side(d)}, p) == True{} : Bool}
  {S.Spec.pixel(d, R.raster(d, cell, kept, x0, y0, bg), x0, y0, p) == S.Spec.color(kept, p, bg) : U32}

def raster_color(meet, cover, unit, quarter, d, cell, kept, x0, y0, bg, p, ec, inside):
  match d cell:
    case 0n R.Flat{c}:
      Equal.sym(U32, S.Spec.color(kept, p, bg), c, flat_color(~cover, kept, x0, y0, R.side(0n), p, bg, c, ec, inside))
    case 0n R.Mixed{}:
      %Equal.sym(G.Point, p, G.Point{x0, y0}, unit(p, x0, y0, inside)) : {R.first(kept, G.Point{x0, y0}, bg) == S.Spec.color(kept, _, bg) : U32}
      first_color(kept, G.Point{x0, y0}, bg)
    case 1n+e R.Flat{c}:
      Equal.sym(U32, S.Spec.color(kept, p, bg), c, flat_color(~cover, kept, x0, y0, R.side(1n+e), p, bg, c, ec, inside))
    case 1n+e R.Mixed{}:
      match p:
        case G.Point{+px, +py}:
          quad_step(~meet, ~cover, e, kept, x0, y0, bg, px, py,
            I.I32.is_le((x0 + R.side(e) : I.I32), px), I.I32.is_le((y0 + R.side(e) : I.I32), py),
            quarter(x0, y0, e, px, py, inside),
            c => k => x => y => ec2 => ins => raster_color(~meet, ~cover, ~unit, ~quarter, e, c, k, x, y, bg, G.Point{px, py}, ec2, ins))

# The window is the root cell, holding the commands kept for it, top first.
def Laws.image_pixels(unit, quarter, d, cmds, bg, p, inside):
  Equal.trans(U32,
    S.Spec.pixel(d, R.raster(d, R.Cell.of(R.keep(List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d)), G.int(0), G.int(0), R.side(d), bg), R.keep(List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d)), G.int(0), G.int(0), bg), G.int(0), G.int(0), p),
    S.Spec.color(R.keep(List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d)), p, bg),
    S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg),
    raster_color(~fact_meet, ~fact_cover, ~unit, ~quarter, d, R.Cell.of(R.keep(List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d)), G.int(0), G.int(0), R.side(d), bg), R.keep(List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d)), G.int(0), G.int(0), bg, p, {==}, inside),
    keep_color(~fact_meet, ~fact_cover, List.reverse(&2, R.Draw, cmds), G.int(0), G.int(0), R.side(d), p, bg, inside))
