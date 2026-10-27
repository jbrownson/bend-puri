import Base
import ../ask/ask.bend as A
import ../geom.bend as G
import ./frame.bend as F
import ./LAWS.bend as Laws

def Laws.target_direct(H, t):
  {==}

def Laws.target_occludes(H):
  {==}

def Laws.target_none(H):
  {==}

def Laws.occluder_hides(H, base, above, pt, e):
  %Equal.sym(Maybe<F.Claim<H>>, above(pt), Some{F.Occludes{}}, e) : {F.Claim.target(H, A.Ask.fallback(G.Point, F.Claim<H>, _, base, pt)) == None{} : Maybe<&2, H>}
  {==}

def Laws.frame_over(Act, E, H, C, bh, bp, bi, ah, ap, ai):
  {==}

def Laws.present(Act, E, H, C, h, p, i, pt):
  {==}
