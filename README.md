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

- `change/`: edits to any value. An edit structure (`EditStructure`) says
  how a type's values are edited: the type of the values (`Value`), the type
  of their edits (`Edit`), and how to apply one. A change structure
  (`ChangeStructure`) is an edit structure with the proof that one edit gets
  from any value to any other (`reaches`). Two layers build on any edit
  structure: `runs`, whose edits are runs of its edits applied in order (no
  edits leaves a value alone, and one run then another is the two joined),
  and `whole`, whose edits are its edits or a replacement with a whole new
  value, which makes a change structure of anything. An `Inc<ca, cb>` pairs
  a function, from values edited as `ca` says to values edited as `cb` says,
  with its derivative, which gives the edit to the function's result from an
  edit to its input. `lift` turns an `Inc` whose derivative gives a run for
  one edit into one that handles runs, and `whole.lift` lifts one to values
  that can also be replaced. The laws say what each operation returns, and
  that lifting a correct `Inc` gives a correct one.
- `list/`: a list's edits (insert, delete, and update an element in place),
  given how its elements are edited (`edit_structure`), `patch` to apply a
  run of them, `diff`, a run from any list to any other, and `map.inc`,
  which maps an `Inc` over lists; its derivative is `dmap`. A list's change
  structure (`change_structure`) is runs of its edits: single edits don't
  reach, but runs do, by `diff`, without replacing. An element's edits can
  be of any type, with their own way to apply: runs of a list's edits,
  replacing a plain value (`C.whole(~C.none(~A))`), or something else
  entirely. The laws cover edits whose positions are in range (`valid`), and
  say what each edit does, that `diff` gets there, what `dmap` returns for
  each edit, that `map.inc(g)` is correct when `g` is, that `dmap` acts
  exactly where the edits act, and that it turns valid edits into valid
  ones.

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
- `ilc.bend`: `dmap` on concrete lists of numbers: the edits that mapping
  makes, checked against mapping from scratch, a map over lists of lists,
  and `diff`'s run between two lists.

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
bend examples/ilc.bend        # computes a mapped list's edits
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
