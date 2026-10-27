import Base
import ./change.bend as C

# What changes promise; PROOF.bend proves it.

# Changes to any value
# --------------------
# A type supplies its edits E and `ea`, how to apply one.

# LAW: keeping changes nothing.
law apply_keep:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for a: A
  {C.apply(~A, ~E, ~ea, C.Keep{}, a) == a : A}

# LAW: replacing gives the new value.
law apply_replace:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for x: A
  for a: A
  {C.apply(~A, ~E, ~ea, C.Replace{x}, a) == x : A}

# LAW: an edit is applied by `ea`.
law apply_edit:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for e: E
  for a: A
  {C.apply(~A, ~E, ~ea, C.Edit{e}, a) == ea(e, a) : A}

# LAW: one change then another applies the first, then the second.
law apply_then:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ea, C.Then{p, q}, a) == C.apply(~A, ~E, ~ea, q, C.apply(~A, ~E, ~ea, p, a)) : A}

# It follows that:

# LAW: keeping first does nothing.
law then_keep_left:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for q: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ea, C.Then{C.Keep{}, q}, a) == C.apply(~A, ~E, ~ea, q, a) : A}

# LAW: keeping last does nothing.
law then_keep_right:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for p: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ea, C.Then{p, C.Keep{}}, a) == C.apply(~A, ~E, ~ea, p, a) : A}

# LAW: grouping doesn't matter.
law then_assoc:
  for ~A: Data
  for ~E: Data
  for ~ea: E -> A -> A
  for p: C.Change<A, E>
  for q: C.Change<A, E>
  for r: C.Change<A, E>
  for a: A
  {C.apply(~A, ~E, ~ea, C.Then{C.Then{p, q}, r}, a) == C.apply(~A, ~E, ~ea, C.Then{p, C.Then{q, r}}, a) : A}

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

# LAW: an Inc is correct, for changes applied by pa and pb, when applying
# its derivative's change to f(a) gives f of the changed value.
law inc_ok:
  for -A: Data
  for -DA: Data
  for -B: Data
  for -DB: Data
  for -pa: DA -> A -> A
  for -pb: DB -> B -> B
  for -g: C.Inc<A, DA, B, DB>
  {C.Inc.ok(A, DA, B, DB, pa, pb, g) == (@a: A -> @d: DA -> {pb(C.Inc.df(A, DA, B, DB, g)(a, d), C.Inc.f(A, DA, B, DB, g)(a)) == C.Inc.f(A, DA, B, DB, g)(pa(d, a)) : B}) : Type}

# Lifting
# -------
# lift turns g, whose derivative handles one edit of A, applied by `ea`,
# into an Inc whose derivative handles any change.

# LAW: lift(g) has g's function, and lift.df for its derivative.
law lift:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  {C.lift(~A, ~EA, ~B, ~EB, ~ea, ~g) == C.Inc{C.Inc.f(A, EA, B, C.Change<B, EB>, g), a => d => C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, d, a)} : C.Inc<A, C.Change<A, EA>, B, C.Change<B, EB>>}

# LAW: keeping the input keeps the result.
law lift_keep:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, C.Keep{}, a) == C.Keep{} : C.Change<B, EB>}

# LAW: replacing the input replaces the result, with f of the new value.
law lift_replace:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for x: A
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, C.Replace{x}, a) == C.Replace{C.Inc.f(A, EA, B, C.Change<B, EB>, g)(x)} : C.Change<B, EB>}

# LAW: one edit gives g's change.
law lift_edit:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for e: EA
  for a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, C.Edit{e}, a) == C.Inc.df(A, EA, B, C.Change<B, EB>, g)(a, e) : C.Change<B, EB>}

# LAW: one change then another lifts the second from the value the first
# produced.
law lift_then:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for p: C.Change<A, EA>
  for q: C.Change<A, EA>
  for +a: A
  {C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, C.Then{p, q}, a) == C.Then{C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, p, a), C.lift.df(~A, ~EA, ~B, ~EB, ~ea, ~g, q, C.apply(~A, ~EA, ~ea, p, a))} : C.Change<B, EB>}

# It follows that:

# LAW: lift(g) is correct for every change, if g is correct for every
# single edit.
law lift_ok:
  for ~A: Data
  for ~EA: Data
  for ~B: Data
  for ~EB: Data
  for ~ea: EA -> A -> A
  for ~eb: EB -> B -> B
  for ~g: C.Inc<A, EA, B, C.Change<B, EB>>
  for ~g_ok: C.Inc.ok(A, EA, B, C.Change<B, EB>, ea, (d => b => C.apply(~B, ~EB, ~eb, d, b)), g)
  C.Inc.ok(A, C.Change<A, EA>, B, C.Change<B, EB>, (d => a => C.apply(~A, ~EA, ~ea, d, a)), (d => b => C.apply(~B, ~EB, ~eb, d, b)), C.lift(~A, ~EA, ~B, ~EB, ~ea, ~g))

# Recomputing
# -----------

# LAW: recompute(f) is f, with the derivative that replaces the result
# with f of the changed value.
law recompute:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~EB: Data
  for ~pa: DA -> A -> A
  for ~f: A -> B
  {C.recompute(~A, ~DA, ~B, ~EB, ~pa, ~f) == C.Inc{f, a => d => C.Replace{f(pa(d, a))}} : C.Inc<A, DA, B, C.Change<B, EB>>}

# It follows that:

# LAW: recomputing is correct, for any function.
law recompute_ok:
  for ~A: Data
  for ~DA: Data
  for ~B: Data
  for ~EB: Data
  for ~pa: DA -> A -> A
  for ~eb: EB -> B -> B
  for ~f: A -> B
  C.Inc.ok(A, DA, B, C.Change<B, EB>, pa, (d => b => C.apply(~B, ~EB, ~eb, d, b)), C.recompute(~A, ~DA, ~B, ~EB, ~pa, ~f))
