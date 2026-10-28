# Puri for Bend

An experiment in porting [Puri](https://github.com/jbrownson/roc-puri)'s
state-explicit UI components to [Bend 2](https://github.com/bendlang/bend),
with laws checked by Bend's prover.

## Files

A module with laws has a directory of its own: the module, `LAWS.bend`,
what it promises, and `PROOF.bend`, their proofs. The laws say what each
operation returns, case by case, so reading them is enough to know what it
does. Laws under "It follows that" add nothing new: they are consequences,
checked so you don't have to work them out. `PROOF.bend` at the root checks
every module's proofs.

`puri/`, the library:

- `ask/`: asking a stack of placements a question. The one placed later
  (on top) answers first, and only a decline falls through to the one below.
  `Ask.over(base, above)` stacks two. Event handling and hover both work
  this way.
- `handler/`: transient event handlers, an `Ask` from events to actions.
  The caller chooses the action type: a state transition, an effectful
  command, or anything else.
- `frame/`: what one placement produces: a handler, a hover probe, and
  deferred ink. `Frame.present` runs a frame's phases in order: it resolves
  hover from the settled probes, then paints with that answer.
- `geom.bend`: points and rectangles, with signed 32-bit coordinates.
- `order.bend`: `I32`'s order, proved from the packages below:
  transitivity, totality, and what adding 1 does.
- `arith.bend`: `U32` and `I32` arithmetic the packages don't have:
  associativity, a shift as a doubling, and the sign bit as adding 2^31.

`ilc/`, incremental computation (ILC: compute a result's change from the
input's change instead of recomputing it):

- `change/`: changes to any value. A change structure (`ChangeStructure`)
  says how values change: the type of the values (`Value`), the type of
  their changes (`Delta`), and how to apply one. A type supplies its own
  edits; `complete` turns them into a full change structure whose changes
  are `Change`s: an optional new value to start over from, then a run of
  edits. That gives what every type has: no change (`keep`), starting over
  (`replace`), and one change then another (`then`). An `Inc<ca, cb>` pairs
  a function, from values that change as `ca` says to values that change as
  `cb` says, with its derivative, which gives the change to the function's
  result from a change to its input. `lift` turns an `Inc` whose derivative
  handles single edits into one that handles any change. The laws say what
  applying each change returns, what `lift`'s derivative returns for each
  kind of change, and that lifting a correct `Inc` gives a correct one.
- `list/`: a list's edits (insert, delete, and update an element in place),
  how a list changes by one edit given how its elements change (`structure`,
  which `C.complete` completes), `patch` to apply a change, and `map.inc`,
  which maps an `Inc` over lists; its derivative is `dmap`. An element's
  change can be of any type, with its own way to apply it: a `Change` of the
  element, or something else entirely. The laws cover changes whose
  positions are in range (`valid`), and say what each edit does, what `dmap`
  returns for each kind of change, that `map.inc(g)` is correct when `g` is,
  that `dmap` acts exactly where the change acts, and that it turns valid
  changes into valid ones.

The approach follows Phil Freeman's
[Purview](https://github.com/paf31/purescript-purview), a PureScript UI
library built on ILC, and his
[purescript-incremental-functions](https://github.com/paf31/purescript-incremental-functions),
from the theory in Cai, Giarrusso, Rendel and Ostermann, ["A Theory of
Changes for Higher-Order Languages"](https://arxiv.org/abs/1312.0658).

`raster/`, the backend:

- `raster.bend`: turns fill commands into the `Image` quadtree a Bend window
  shows, splitting only where there's an edge.
- `spec.bend`: what the raster must produce, stated the slow, obvious way:
  each pixel takes the color of the topmost command whose rectangle contains
  it, or the background. It also states four geometric facts about `I32`
  coordinates that the proof rests on.
- `LAWS.bend`: every pixel of a rasterized window is the spec's color.
- `PROOF.bend`: the proof, including the four geometric facts.
- `raster_test.bend`: compares every pixel of a few scenes against the spec,
  and tries the four facts on every combination of edge-case values in the
  compiled program.

`examples/`:

- `counter.bend`: combining two handlers whose actions are state steps,
  composed with `do` inside a handler. Puri only sees the plain action type.
- `hover.bend`: overlapping boxes and an occluding panel, printing each
  frame's painting.
- `app.bend`: an interactive window: boxes you can hover and click to
  select, under a panel that blocks both.
- `app_test.bend`: replays scripted events through `app.bend` without a
  window.
- `ilc.bend`: `dmap` on concrete lists of numbers: the change that mapping
  makes, checked against mapping from scratch, and a map over lists of
  lists.

## Dependencies

Packages from [BendHub](https://hub.bend-lang.com/packages), imported by
content hash, so `bend` fetches exactly that code on first use and checks it:

- `bend-kit-int` (`0x4eed9d7a…`): the `I32` used for coordinates.
- `bend-kit-lemmas` (`0x917f5ed7…`): proved laws relating `U32` arithmetic and
  order to `Nat`.
- `bend-mathlib` 0.7.4.0 (`0xcdaf59a0…`): proved lemmas about `Nat` and `Bool`.

## Running

```sh
bend PROOF.bend               # ALL PROOFS CHECK when every law holds
bend ilc/list/PROOF.bend      # or one module's laws
bend examples/counter.bend    # runs the handler example
bend examples/hover.bend      # runs the hover example
bend examples/app_test.bend   # replays events through the app headlessly
bend examples/ilc.bend        # computes a mapped list's change
bend raster/raster_test.bend  # checks pixels and the geometric facts
```

`bend <file> --verdict` checks a proof a second time with Bend's BendTT
kernel, which has its own proof in Lean, and confirms nothing relies on
`@unsafe` or foreign code. `bend PROOF.bend --verdict` passes. It needs Lean
4.34.0 (the elan toolchain `leanprover/lean4:v4.34.0`) to build the kernel
on first use.

Windows only open from a native build; `bend examples/app.bend` alone runs
on Bend's JS path, which has no window. To open the interactive window:

```sh
bend examples/app.bend -o app && ./app
```

On Linux this needs clang and the X11 headers (`clang libx11-dev` on
Debian/Ubuntu), run from a desktop session so `$DISPLAY` is set. On
macOS it needs clang from the Xcode command line tools.

Tested with Bend 2.0.39.
