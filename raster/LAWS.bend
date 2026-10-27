import Base
import ../puri/geom.bend as G
import ./raster.bend as R
import ./spec.bend as S

# LAW: given the geometric facts in spec.bend, every pixel of a rasterized
# window is the color the spec gives it: the topmost command whose rectangle
# contains it, or the background.
law image_pixels:
  for ~meet: S.Fact.meet()
  for ~cover: S.Fact.cover()
  for ~unit: S.Fact.unit()
  for ~quarter: S.Fact.quarter()
  for +d: Nat
  for +cmds: +List<R.Draw>
  for +bg: U32
  for +p: G.Point
  for +inside: {G.Rect.contains(G.Rect{0, 0, U32.shln(1, d), U32.shln(1, d)}, p) == True{} : Bool}
  {S.Spec.pixel(d, R.Raster.image(d, cmds, bg), 0, 0, p) == S.Spec.color(List.reverse(&2, R.Draw, cmds), p, bg) : U32}
