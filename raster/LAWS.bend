import Base
import ../puri/geom.bend as G
import ./raster.bend as R
import ./spec.bend as S

# LAW: given two geometric facts still to be proved (see spec.bend), every
# pixel of a rasterized window is the color the spec gives it: the topmost
# command whose rectangle contains it, or the background.
law image_pixels:
  for ~unit: S.Fact.unit()
  for ~quarter: S.Fact.quarter()
  for +d: Nat
  for +cmds: +List<R.Draw>
  for +bg: U32
  for +p: G.Point
  for +inside: {G.Rect.contains(G.Rect{G.int(0), G.int(0), R.side(d), R.side(d)}, p) == True{} : Bool}
  {S.Spec.pixel(d, R.Raster.image(d, cmds, bg), G.int(0), G.int(0), p) == S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg) : U32}
