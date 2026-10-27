import Base
import ../ask/ask.bend as A
import ../handler/handler.bend as Hd
import ../geom.bend as G
import ./frame.bend as F

# What frames promise; PROOF.bend proves it.

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
