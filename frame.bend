import Base
import ./ask.bend as A
import ./handler.bend as Hd

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

# What the pointer rests on, as one placement answers: a hover target, or
# an occluder that covers what lies beneath without naming a target.
type Claim<-H: Data> is Data:
  Direct{target: H}
  Occludes{}

# A placement's hover answer, asked like a handler: top placement first.
def Probe(-H: Data) -> Type:
  A.Ask(Point, Claim<H>)

# Deferred painting: given the resolved hover, produce draw commands C.
# Commands are plain data, so a backend can read the list as often as
# it needs to.
def Ink(-H: Data, -C: Data) -> Type:
  Maybe<&2, H> -> List<&2, C>

# Paint the base, then paint above it.
def Ink.over(-H: Data, -C: Data, base: Ink(H, C), above: Ink(H, C)) -> Ink(H, C):
  +h => List.append(&2, C, base(h), above(h))

# What one placement produces: how it handles events, what it claims under
# the pointer, and how it paints once hover is known.
type Frame<-M: Type -> Type, -E: Data, -H: Data, -C: Data> is Type:
  Frame{handler: Hd.Handler(M, E), probe: Probe(H), ink: Ink(H, C)}

# Stack `above` on `base`: placed later, painted on top, asked first.
def Frame.over(-M: Type -> Type, -E: Data, -H: Data, -C: Data, base: Frame<M, E, H, C>, above: Frame<M, E, H, C>) -> Frame<M, E, H, C>:
  match base above:
    case Frame{bh, bp, bi} Frame{ah, ap, ai}:
      Frame{Hd.Handler.over(M, E, bh, ah), A.Ask.over(Point, Claim<H>, bp, ap), Ink.over(H, C, bi, ai)}

# The hovered target: an occluder, or no claim at all, hovers nothing.
def Claim.target(-H: Data, c: Maybe<Claim<H>>) -> Maybe<&2, H>:
  match c:
    case Some{Direct{t}}:
      Some{t}
    case _:
      None{}

# A frame's phases, in order: resolve hover from the settled probes, then
# run the deferred ink with that answer. Returns the handler for the next
# event alongside the painting.
def Frame.present(-M: Type -> Type, -E: Data, -H: Data, -C: Data, f: Frame<M, E, H, C>, pointer: Point) -> Hd.Handler(M, E) & List<&2, C>:
  match f:
    case Frame{handler, probe, ink}:
      (handler, ink(Claim.target(H, probe(pointer))))

# Just the handler, for routing an event. The probe and the ink are
# dropped without running.
def Frame.handler(-M: Type -> Type, -E: Data, -H: Data, -C: Data, f: Frame<M, E, H, C>) -> Hd.Handler(M, E):
  match f:
    case Frame{handler, probe, ink}:
      handler
