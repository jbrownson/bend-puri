import Base
import ./handler.bend as P
import ./LAWS.bend as Laws

# Helper: falling back to the empty handler gives back the answer itself.
law fallback_empty:
  for -S: Type
  for -E: Data
  for r: Maybe<(S -> S)>
  for -e: E
  {P.Handler.fallback(S, E, r, P.Handler.empty(S, E), e) == r : Maybe<(S -> S)>}

def fallback_empty(S, E, r, e):
  match r:
    case Some{t}:
      {==}
    case None{}:
      {==}

# Helper: one fallback to a combined handler is two fallbacks in a row.
law fallback_plus:
  for -S: Type
  for -E: Data
  for -a: P.Handler(S, E)
  for -b: P.Handler(S, E)
  for r: Maybe<(S -> S)>
  for -e: E
  {P.Handler.fallback(S, E, r, P.Handler.plus(S, E, a, b), e) == P.Handler.fallback(S, E, P.Handler.fallback(S, E, r, b, e), a, e) : Maybe<(S -> S)>}

def fallback_plus(S, E, a, b, r, e):
  match r:
    case Some{t}:
      {==}
    case None{}:
      {==}

def Laws.plus_empty_left(S, E, h, e):
  fallback_empty(S, E, h(e), e)

def Laws.plus_empty_right(S, E, h, e):
  {==}

def Laws.plus_assoc(S, E, a, b, c, e):
  fallback_plus(S, E, a, b, c(e), e)

def Laws.later_wins(S, E, earlier, t, e):
  {==}
