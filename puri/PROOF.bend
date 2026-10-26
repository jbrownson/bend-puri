import Base
import ./ask.bend as A
import ./handler.bend as Hd
import ./geom.bend as G
import ./frame.bend as F
import ./LAWS.bend as Laws

# Helper: falling back to the empty base gives back the answer itself.
law fallback_none:
  for -X: Data
  for -Y: Type
  for r: Maybe<Y>
  for -x: X
  {A.Ask.fallback(X, Y, r, A.Ask.none(X, Y), x) == r : Maybe<Y>}

def fallback_none(X, Y, r, x):
  match r:
    case Some{y}:
      {==}
    case None{}:
      {==}

# Helper: one fallback to a stacked base is two fallbacks in a row.
law fallback_over:
  for -X: Data
  for -Y: Type
  for -a: A.Ask(X, Y)
  for -b: A.Ask(X, Y)
  for r: Maybe<Y>
  for -x: X
  {A.Ask.fallback(X, Y, r, A.Ask.over(X, Y, a, b), x) == A.Ask.fallback(X, Y, A.Ask.fallback(X, Y, r, b, x), a, x) : Maybe<Y>}

def fallback_over(X, Y, a, b, r, x):
  match r:
    case Some{y}:
      {==}
    case None{}:
      {==}

def Laws.none_declines(X, Y, x):
  {==}

# The evidence e says what the top layer answers; rewriting with it lets
# the goal compute.
def Laws.over_answered(X, Y, base, above, x, y, e):
  %Equal.sym(Maybe<Y>, above(x), Some{y}, e) : {A.Ask.fallback(X, Y, _, base, x) == Some{y} : Maybe<Y>}
  {==}

def Laws.over_declined(X, Y, base, above, x, e):
  %Equal.sym(Maybe<Y>, above(x), None{}, e) : {A.Ask.fallback(X, Y, _, base, x) == base(x) : Maybe<Y>}
  {==}

def Laws.over_none_base(X, Y, q, x):
  fallback_none(X, Y, q(x), x)

def Laws.over_none_above(X, Y, q, x):
  {==}

def Laws.over_assoc(X, Y, a, b, c, x):
  fallback_over(X, Y, a, b, c(x), x)

def Laws.handler_empty(Act, E):
  {==}

def Laws.handler_over(Act, E, base, above):
  {==}

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
