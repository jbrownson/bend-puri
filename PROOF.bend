import Base
import ./handler.bend as P
import ./LAWS.bend as Laws

# Helper: falling back to the empty handler gives back the answer itself.
law fallback_empty:
  for -M: Type -> Type
  for -E: Data
  for r: Maybe<M(Unit)>
  for -e: E
  {P.Handler.fallback(M, E, r, P.Handler.empty(M, E), e) == r : Maybe<M(Unit)>}

def fallback_empty(M, E, r, e):
  match r:
    case Some{t}:
      {==}
    case None{}:
      {==}

# Helper: one fallback to a combined handler is two fallbacks in a row.
law fallback_plus:
  for -M: Type -> Type
  for -E: Data
  for -a: P.Handler(M, E)
  for -b: P.Handler(M, E)
  for r: Maybe<M(Unit)>
  for -e: E
  {P.Handler.fallback(M, E, r, P.Handler.plus(M, E, a, b), e) == P.Handler.fallback(M, E, P.Handler.fallback(M, E, r, b, e), a, e) : Maybe<M(Unit)>}

def fallback_plus(M, E, a, b, r, e):
  match r:
    case Some{t}:
      {==}
    case None{}:
      {==}

def Laws.plus_empty_left(M, E, h, e):
  fallback_empty(M, E, h(e), e)

def Laws.plus_empty_right(M, E, h, e):
  {==}

def Laws.plus_assoc(M, E, a, b, c, e):
  fallback_plus(M, E, a, b, c(e), e)

def Laws.later_wins(M, E, earlier, t, e):
  {==}
