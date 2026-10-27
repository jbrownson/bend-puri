import Base
import ../puri/geom.bend as G
import ./raster.bend as R
import ./spec.bend as S
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

# Helper: one command's step of keep, with its three tests as parameters.
law keep_step:
  for +r: G.Rect
  for +rgb: U32
  for rest: +List<R.Draw>
  for +x0: U32
  for +y0: U32
  for +s: U32
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
  for +x0: U32
  for +y0: U32
  for +s: U32
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
  for +x0: U32
  for +y0: U32
  for +s: U32
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
  for +x: U32
  for +y: U32
  for +bg: U32
  for +px: U32
  for +py: U32
  for +inside: {G.Rect.contains(G.Rect{x, y, U32.shln(1, e), U32.shln(1, e)}, G.Point{px, py}) == True{} : Bool}
  for ih: (@c: R.Cell -> @k: +List<R.Draw> -> @x: U32 -> @y: U32 ->
    {R.Cell.of(k, x, y, U32.shln(1, e), bg) == c : R.Cell} ->
    {G.Rect.contains(G.Rect{x, y, U32.shln(1, e), U32.shln(1, e)}, G.Point{px, py}) == True{} : Bool} ->
    {S.Spec.pixel(e, R.raster(e, c, k, x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(k, G.Point{px, py}, bg) : U32})
  {S.Spec.pixel(e, R.raster(e, R.Cell.of(R.keep(kept, x, y, U32.shln(1, e)), x, y, U32.shln(1, e), bg), R.keep(kept, x, y, U32.shln(1, e)), x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(kept, G.Point{px, py}, bg) : U32}

def child(meet, cover, e, kept, x, y, bg, px, py, inside, ih):
  Equal.trans(U32,
    S.Spec.pixel(e, R.raster(e, R.Cell.of(R.keep(kept, x, y, U32.shln(1, e)), x, y, U32.shln(1, e), bg), R.keep(kept, x, y, U32.shln(1, e)), x, y, bg), x, y, G.Point{px, py}),
    S.Spec.color(R.keep(kept, x, y, U32.shln(1, e)), G.Point{px, py}, bg),
    S.Spec.color(kept, G.Point{px, py}, bg),
    ih(R.Cell.of(R.keep(kept, x, y, U32.shln(1, e)), x, y, U32.shln(1, e), bg), R.keep(kept, x, y, U32.shln(1, e)), x, y, {==}, inside),
    keep_color(~meet, ~cover, kept, x, y, U32.shln(1, e), G.Point{px, py}, bg, inside))

# Helper: a split cell, with the quarter holding the point as parameters.
law quad_step:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for +e: Nat
  for +kept: +List<R.Draw>
  for +x0: U32
  for +y0: U32
  for +bg: U32
  for +px: U32
  for +py: U32
  for right: Bool
  for low: Bool
  for +inside: {G.Rect.contains(G.Rect{S.Spec.half(right, x0, U32.shln(1, e)), S.Spec.half(low, y0, U32.shln(1, e)), U32.shln(1, e), U32.shln(1, e)}, G.Point{px, py}) == True{} : Bool}
  for ih: (@c: R.Cell -> @k: +List<R.Draw> -> @x: U32 -> @y: U32 ->
    {R.Cell.of(k, x, y, U32.shln(1, e), bg) == c : R.Cell} ->
    {G.Rect.contains(G.Rect{x, y, U32.shln(1, e), U32.shln(1, e)}, G.Point{px, py}) == True{} : Bool} ->
    {S.Spec.pixel(e, R.raster(e, c, k, x, y, bg), x, y, G.Point{px, py}) == S.Spec.color(k, G.Point{px, py}, bg) : U32})
  {S.Spec.pixel(e, S.Spec.quarter(right, low, R.raster(e, R.Cell.of(R.keep(kept, x0, y0, U32.shln(1, e)), x0, y0, U32.shln(1, e), bg), R.keep(kept, x0, y0, U32.shln(1, e)), x0, y0, bg), R.raster(e, R.Cell.of(R.keep(kept, (x0 + U32.shln(1, e) : U32), y0, U32.shln(1, e)), (x0 + U32.shln(1, e) : U32), y0, U32.shln(1, e), bg), R.keep(kept, (x0 + U32.shln(1, e) : U32), y0, U32.shln(1, e)), (x0 + U32.shln(1, e) : U32), y0, bg), R.raster(e, R.Cell.of(R.keep(kept, x0, (y0 + U32.shln(1, e) : U32), U32.shln(1, e)), x0, (y0 + U32.shln(1, e) : U32), U32.shln(1, e), bg), R.keep(kept, x0, (y0 + U32.shln(1, e) : U32), U32.shln(1, e)), x0, (y0 + U32.shln(1, e) : U32), bg), R.raster(e, R.Cell.of(R.keep(kept, (x0 + U32.shln(1, e) : U32), (y0 + U32.shln(1, e) : U32), U32.shln(1, e)), (x0 + U32.shln(1, e) : U32), (y0 + U32.shln(1, e) : U32), U32.shln(1, e), bg), R.keep(kept, (x0 + U32.shln(1, e) : U32), (y0 + U32.shln(1, e) : U32), U32.shln(1, e)), (x0 + U32.shln(1, e) : U32), (y0 + U32.shln(1, e) : U32), bg)), S.Spec.half(right, x0, U32.shln(1, e)), S.Spec.half(low, y0, U32.shln(1, e)), G.Point{px, py}) == S.Spec.color(kept, G.Point{px, py}, bg) : U32}

def quad_step(meet, cover, e, kept, x0, y0, bg, px, py, right, low, inside, ih):
  match right low:
    case False{} False{}:
      child(~meet, ~cover, e, kept, x0, y0, bg, px, py, inside, ih)
    case True{} False{}:
      child(~meet, ~cover, e, kept, (x0 + U32.shln(1, e) : U32), y0, bg, px, py, inside, ih)
    case False{} True{}:
      child(~meet, ~cover, e, kept, x0, (y0 + U32.shln(1, e) : U32), bg, px, py, inside, ih)
    case True{} True{}:
      child(~meet, ~cover, e, kept, (x0 + U32.shln(1, e) : U32), (y0 + U32.shln(1, e) : U32), bg, px, py, inside, ih)

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
  for +x0: U32
  for +y0: U32
  for +bg: U32
  for +p: G.Point
  for ec: {R.Cell.of(kept, x0, y0, U32.shln(1, d), bg) == cell : R.Cell}
  for +inside: {G.Rect.contains(G.Rect{x0, y0, U32.shln(1, d), U32.shln(1, d)}, p) == True{} : Bool}
  {S.Spec.pixel(d, R.raster(d, cell, kept, x0, y0, bg), x0, y0, p) == S.Spec.color(kept, p, bg) : U32}

def raster_color(meet, cover, unit, quarter, d, cell, kept, x0, y0, bg, p, ec, inside):
  match d cell:
    case 0n R.Flat{c}:
      Equal.sym(U32, S.Spec.color(kept, p, bg), c, flat_color(~cover, kept, x0, y0, U32.shln(1, 0n), p, bg, c, ec, inside))
    case 0n R.Mixed{}:
      %Equal.sym(G.Point, p, G.Point{x0, y0}, unit(p, x0, y0, inside)) : {R.first(kept, G.Point{x0, y0}, bg) == S.Spec.color(kept, _, bg) : U32}
      first_color(kept, G.Point{x0, y0}, bg)
    case 1n+e R.Flat{c}:
      Equal.sym(U32, S.Spec.color(kept, p, bg), c, flat_color(~cover, kept, x0, y0, U32.shln(1, 1n+e), p, bg, c, ec, inside))
    case 1n+e R.Mixed{}:
      match p:
        case G.Point{+px, +py}:
          quad_step(~meet, ~cover, e, kept, x0, y0, bg, px, py,
            U32.is_le((x0 + U32.shln(1, e) : U32), px), U32.is_le((y0 + U32.shln(1, e) : U32), py),
            quarter(x0, y0, e, px, py, inside),
            c => k => x => y => ec2 => ins => raster_color(~meet, ~cover, ~unit, ~quarter, e, c, k, x, y, bg, G.Point{px, py}, ec2, ins))

# The window is the root cell, holding the commands kept for it, top first.
def Laws.image_pixels(meet, cover, unit, quarter, d, cmds, bg, p, inside):
  Equal.trans(U32,
    S.Spec.pixel(d, R.raster(d, R.Cell.of(R.keep(List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d)), 0, 0, U32.shln(1, d), bg), R.keep(List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d)), 0, 0, bg), 0, 0, p),
    S.Spec.color(R.keep(List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d)), p, bg),
    S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg),
    raster_color(~meet, ~cover, ~unit, ~quarter, d, R.Cell.of(R.keep(List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d)), 0, 0, U32.shln(1, d), bg), R.keep(List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d)), 0, 0, bg, p, {==}, inside),
    keep_color(~meet, ~cover, List.reverse(&2, R.Draw, cmds), 0, 0, U32.shln(1, d), p, bg, inside))
