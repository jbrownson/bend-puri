import Base
import ./ask.bend as A
import ./handler.bend as Hd
import ./geom.bend as G
import ./frame.bend as F

# What Puri promises; PROOF.bend proves it. The laws say what each
# operation returns, case by case, so together they pin down what the
# library does. Laws under "It follows that" add nothing new: they are
# consequences, checked so you don't have to work them out.
#
# Bend doesn't infer type arguments, so each law starts with a `for` per
# type it mentions.

# Asking a stack
# --------------
# An Ask(X, Y) answers a question x with Some{y}, or declines with None{}.
# Handlers and hover probes are both Asks.

# LAW: the empty Ask declines everything.
law none_declines:
  for -X: Data
  for -Y: Type
  for x: X
  {A.Ask.none(X, Y)(x) == None{} : Maybe<Y>}

# LAW: if the layer on top answers, that is the answer.
law over_answered:
  for -X: Data
  for -Y: Type
  for base: A.Ask(X, Y)
  for above: A.Ask(X, Y)
  for +x: X
  for -y: Y
  for e: {above(x) == Some{y} : Maybe<Y>}
  {A.Ask.over(X, Y, base, above)(x) == Some{y} : Maybe<Y>}

# LAW: if the layer on top declines, the base answers.
law over_declined:
  for -X: Data
  for -Y: Type
  for base: A.Ask(X, Y)
  for above: A.Ask(X, Y)
  for +x: X
  for e: {above(x) == None{} : Maybe<Y>}
  {A.Ask.over(X, Y, base, above)(x) == base(x) : Maybe<Y>}

# It follows that:

# LAW: an empty base changes nothing.
law over_none_base:
  for -X: Data
  for -Y: Type
  for q: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, A.Ask.none(X, Y), q)(x) == q(x) : Maybe<Y>}

# LAW: an empty layer on top changes nothing.
law over_none_above:
  for -X: Data
  for -Y: Type
  for q: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, q, A.Ask.none(X, Y))(x) == q(x) : Maybe<Y>}

# LAW: how three layers are grouped doesn't matter, only their order.
law over_assoc:
  for -X: Data
  for -Y: Type
  for a: A.Ask(X, Y)
  for b: A.Ask(X, Y)
  for c: A.Ask(X, Y)
  for +x: X
  {A.Ask.over(X, Y, A.Ask.over(X, Y, a, b), c)(x) == A.Ask.over(X, Y, a, A.Ask.over(X, Y, b, c))(x) : Maybe<Y>}

# Handlers
# --------
# A Handler(Act, E) is an Ask from events E to actions Act.

# LAW: the empty handler is the empty Ask.
law handler_empty:
  for -Act: Type
  for -E: Data
  {Hd.Handler.empty(Act, E) == A.Ask.none(E, Act) : Hd.Handler(Act, E)}

# LAW: handlers stack as Asks.
law handler_over:
  for -Act: Type
  for -E: Data
  for base: Hd.Handler(Act, E)
  for above: Hd.Handler(Act, E)
  {Hd.Handler.over(Act, E, base, above) == A.Ask.over(E, Act, base, above) : Hd.Handler(Act, E)}

# Hover
# -----
# A Probe(H) is an Ask from points to claims: Direct{target}, or
# Occludes{} for something that covers what lies beneath it.
# Claim.target turns a probe's answer into what is hovered.

# LAW: a direct claim hovers its target.
law target_direct:
  for -H: Data
  for t: H
  {F.Claim.target(H, Some{F.Direct{t}}) == Some{t} : Maybe<&2, H>}

# LAW: an occluder hovers nothing.
law target_occludes:
  for -H: Data
  {F.Claim.target(H, Some{F.Occludes{}}) == None{} : Maybe<&2, H>}

# LAW: no claim hovers nothing.
law target_none:
  for -H: Data
  {F.Claim.target(H, None{}) == None{} : Maybe<&2, H>}

# It follows that:

# LAW: an occluder on top hides everything beneath it from hover.
law occluder_hides:
  for -H: Data
  for base: F.Probe(H)
  for above: F.Probe(H)
  for +pt: G.Point
  for e: {above(pt) == Some{F.Occludes{}} : Maybe<F.Claim<H>>}
  {F.Claim.target(H, A.Ask.over(G.Point, F.Claim<H>, base, above)(pt)) == None{} : Maybe<&2, H>}

# Frames
# ------
# A Frame is what one placement produces: a handler, a probe, and an ink,
# which turns the hovered target into draw commands C.

# LAW: stacking frames stacks each part. The two inks get the same hover,
# and the base's commands come first, so the layer above paints over it.
law frame_over:
  for -Act: Type
  for -E: Data
  for -H: Data
  for -C: Data
  for bh: Hd.Handler(Act, E)
  for bp: F.Probe(H)
  for bi: F.Ink(H, C)
  for ah: Hd.Handler(Act, E)
  for ap: F.Probe(H)
  for ai: F.Ink(H, C)
  {F.Frame.over(Act, E, H, C, F.Frame{bh, bp, bi}, F.Frame{ah, ap, ai})
    == F.Frame{Hd.Handler.over(Act, E, bh, ah), A.Ask.over(G.Point, F.Claim<H>, bp, ap), +h => List.append(&2, C, bi(h), ai(h))}
    : F.Frame<Act, E, H, C>}

# LAW: presenting a frame at a point keeps its handler, and paints with
# what its probe hovers there.
law present:
  for -Act: Type
  for -E: Data
  for -H: Data
  for -C: Data
  for h: Hd.Handler(Act, E)
  for p: F.Probe(H)
  for i: F.Ink(H, C)
  for pt: G.Point
  {F.Frame.present(Act, E, H, C, F.Frame{h, p, i}, pt) == (h, i(F.Claim.target(H, p(pt)))) : Hd.Handler(Act, E) & List<&2, C>}
