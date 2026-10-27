import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# How values change
# -----------------
# A Changes<A, DA> says how values of A change by changes DA: it applies
# one.

# LAW: a change structure applies changes by its function.
law changes_apply:
  for ~A: Data
  for ~DA: Data
  for ~f: DA -> A -> A
  {C.Changes.apply(A, DA, C.Changes{f}) == f : DA -> A -> A}

# Changes to any value
# --------------------
# A type supplies its edits E, and `ce`, how one applies.

# LAW: keeping changes nothing.
law apply_keep:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for a: A
  {C.apply(~A, ~E, ~ce, C.Keep{}, a) == a : A}

# LAW: replacing gives the new value.
law apply_replace:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for x: A
  for a: A
  {C.apply(~A, ~E, ~ce, C.Replace{x}, a) == x : A}

# LAW: an edit is applied as `ce` says.
law apply_edit:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for e: E
  for a: A
  {C.apply(~A, ~E, ~ce, C.Edit{e}, a) == C.Changes.apply(A, E, ce)(e, a) : A}

# LAW: one change then another applies the first, then the second.
law apply_then:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ce, C.Then{p, q}, a) == C.apply(~A, ~E, ~ce, q, C.apply(~A, ~E, ~ce, p, a)) : A}

# It follows that:

# LAW: keeping first does nothing.
law then_keep_left:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ce, C.Then{C.Keep{}, q}, a) == C.apply(~A, ~E, ~ce, q, a) : A}

# LAW: keeping last does nothing.
law then_keep_right:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for p: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ce, C.Then{p, C.Keep{}}, a) == C.apply(~A, ~E, ~ce, p, a) : A}

# LAW: grouping doesn't matter.
law then_assoc:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for r: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ce, C.Then{C.Then{p, q}, r}, a) == C.apply(~A, ~E, ~ce, C.Then{p, C.Then{q, r}}, a) : A}

# LAW: Change<A, E> changes A by C.apply.
law changes:
  for ~A: Data
  for ~E: Data
  for ~ce: C.Changes<A, E>
  for d: C.Change<A, E>
  for a: A
  {C.Changes.apply(A, C.Change<A, E>, C.changes(~A, ~E, ~ce))(d, a) == C.apply(~A, ~E, ~ce, d, a) : A}

# Mapping a change
# ----------------
# C.map(fa, fe, d) maps d's new values by fa and its edits by fe.

# LAW: mapping keeping keeps.
law map_keep:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Keep{}) == C.Keep{} : C.Change<B, EB>}

# LAW: mapping a replacement maps the new value.
law map_replace:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for x: A
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Replace{x}) == C.Replace{fa(x)} : C.Change<B, EB>}

# LAW: mapping an edit maps the edit.
law map_edit:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for e: EA
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Edit{e}) == C.Edit{fe(e)} : C.Change<B, EB>}

# LAW: mapping one change then another maps each, in the same order.
law map_then:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~fa: A -> B
  for ~fe: EA -> EB
  for p: C.Change<A, EA>
  for q: C.Change<A, EA>
  {C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, C.Then{p, q}) == C.Then{C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, p), C.map(~A, ~EA, ~B, ~EB, ~fa, ~fe, q)} : C.Change<B, EB>}

# Incremental functions
# ---------------------
# An Inc<A, DA, B, DB> is a function f: A -> B with its derivative df,
# which takes a value and its change DA, and gives the change DB to f's
# result.

# LAW: Inc.f gives the function.
law inc_f:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~f: A -> B
  for ~df: A -> DA -> DB
  {C.Inc.f(A, DA, B, DB, C.Inc{f, df}) == f : A -> B}

# LAW: Inc.df gives the derivative.
law inc_df:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~DB: Data
  for ~f: A -> B
  for ~df: A -> DA -> DB
  {C.Inc.df(A, DA, B, DB, C.Inc{f, df}) == df : A -> DA -> DB}

# LAW: an Inc is correct, between how A changes (ca) and how B does (cb),
# when applying its derivative's change to f(a) gives f of the changed
# value.
law inc_ok:
  for -A: Data
  for -DA: Data
  for -B: Data
  for -DB: Data
  for -ca: C.Changes<A, DA>
  for -cb: C.Changes<B, DB>
  for -g: C.Inc<A, DA, B, DB>
  {C.Inc.ok(A, DA, B, DB, ca, cb, g) == (@a: A -> @d: DA -> {C.Changes.apply(B, DB, cb)(C.Inc.df(A, DA, B, DB, g)(a, d), C.Inc.f(A, DA, B, DB, g)(a)) == C.Inc.f(A, DA, B, DB, g)(C.Changes.apply(A, DA, ca)(d, a)) : B}) : Type}

# Lifting
# -------
# lift turns g, whose derivative handles one edit of A, applied as `ca`
# says, into an Inc whose derivative handles any change.

# LAW: lift(g) has g's function, and lift.df for its derivative.
law lift:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  {C.lift(~A, ~EA, ~B, ~EB, ~ca, ~g) == C.Inc{C.Inc.f(A, EA, B, C.Change<B, EB>, g), a => d => C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, d, a)} : C.Inc<A, C.Change<A, EA>, B, C.Change<B, EB>>}

# LAW: keeping the input keeps the result.
law lift_keep:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, C.Keep{}, a) == C.Keep{} : C.Change<B, EB>}

# LAW: replacing the input replaces the result, with f of the new value.
law lift_replace:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for x: A
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, C.Replace{x}, a) == C.Replace{C.Inc.f(A, EA, B, C.Change<B, EB>, g)(x)} : C.Change<B, EB>}

# LAW: one edit gives g's change.
law lift_edit:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for e: EA
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, C.Edit{e}, a) == C.Inc.df(A, EA, B, C.Change<B, EB>, g)(a, e) : C.Change<B, EB>}

# LAW: one change then another lifts the second from the value the first
# produced.
law lift_then:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for p: C.Change<A, EA>
  for q: C.Change<A, EA>
  for +a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, C.Then{p, q}, a) == C.Then{C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, p, a), C.lift.df(~A, ~EA, ~B, ~EB, ~ca, ~g, q, C.apply(~A, ~EA, ~ca, p, a))} : C.Change<B, EB>}

# It follows that:

# LAW: lift(g) is correct for every change, if g is correct for every
# single edit.
law lift_ok:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, EA>
  for ~cb: C.Changes<B, EB>
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for ~g_ok: C.Inc.ok(A, EA, B, C.Change<B, EB>, ca, C.changes(~B, ~EB, ~cb), g)
  C.Inc.ok(A, C.Change<A, EA>, B, C.Change<B, EB>, C.changes(~A, ~EA, ~ca), C.changes(~B, ~EB, ~cb), C.lift(~A, ~EA, ~B, ~EB, ~ca, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the changed value.
law recompute:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, DA>
  for ~f: A -> B
  {C.recompute(~A, ~DA, ~B, ~EB, ~ca, ~f) == C.Inc{f, a => d => C.Replace{f(C.Changes.apply(A, DA, ca)(d, a))}} : C.Inc<A, DA, B, C.Change<B, EB>>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~EB: Data
  for ~ca: C.Changes<A, DA>
  for ~cb: C.Changes<B, EB>
  for ~f: A -> B
  C.Inc.ok(A, DA, B, C.Change<B, EB>, ca, C.changes(~B, ~EB, ~cb), C.recompute(~A, ~DA, ~B, ~EB, ~ca, ~f))
