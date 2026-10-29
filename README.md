# Puri for Bend

An experiment in porting [Puri](https://github.com/jbrownson/roc-puri)'s
state-explicit UI components to [Bend 2](https://github.com/bendlang/bend),
with laws checked by Bend's prover.

## Files

A module with laws has a directory of its own: the module, `LAWS.bend`,
what it promises, and `PROOF.bend`, their proofs. The laws say what each
operation returns, case by case, so reading them is enough to know what it
does. A record's fields have no laws of their own: the record's definition
says what they are. Laws under "It follows that" add nothing new: they are consequences,
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

`window/`, the native window:

- `window.bend`: what an app paints (`Draw`: a rectangle filled with a
  color), and running a puri app in Ankra's window, drawn on the GPU. Each
  fill in the app's painting becomes an operation in a Chromi draw list,
  later fills on top, which Voltra draws and presents. Ankra's input arrives
  as Base's events, so an app's handlers are what they would be for Bend's
  own window. `play` replays events through an app without a window.

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
- `bars.bend`: an interactive window of bars you grow (left-click), remove
  (right-click), add ("+") and reset (the grey button). Each press is a run
  of list edits, and the bars' heights are a cached mapped list kept up to
  date by patching it with `dmap`'s edits; reset's run comes from `diff`.
- `bars_test.bend`: replays presses through `bars.bend` without a window,
  checking each time that the cached heights agree with mapping the numbers
  from scratch.

## Dependencies

`bend-kit-int` (`0x4eed9d7a…`), the `I32` used for coordinates, from
[BendHub](https://hub.bend-lang.com/packages). It's imported by content
hash, so `bend` fetches exactly that code on first use and checks it.

The [AMAGE](https://github.com/amage-si) libraries, copied into
`vendor/amage/` at the commits its README lists: Ankra (the window and its
events), Voltra (Vulkan), Chromi (draw lists), and Runika, Syllo, Dithra
and Splina (text, which nothing here uses yet). Ankra and Voltra each
include a native bridge in C.

## Running

```sh
bend PROOF.bend               # ALL PROOFS CHECK when every law holds
bend ilc/list/PROOF.bend      # or one module's laws
bend examples/counter.bend    # runs the handler example
bend examples/hover.bend      # runs the hover example
bend examples/app_test.bend   # replays events through the app headlessly
bend examples/ilc.bend        # computes a mapped list's edits
bend examples/bars_test.bend  # replays presses through the bars app
```

`bend <file> --verdict` checks a proof a second time with Bend's BendTT
kernel, which has its own proof in Lean, and confirms nothing relies on
`@unsafe` or foreign code. `bend PROOF.bend --verdict` passes. It needs Lean
4.34.0 (the elan toolchain `leanprover/lean4:v4.34.0`) to build the kernel
on first use.

Windows only open from a native build; `bend examples/app.bend` alone runs
on Bend's JS path, which has no window. To open the interactive windows:

```sh
bend examples/app.bend -o app && ./app
bend examples/bars.bend -o bars && ./bars
```

They open an X11 window, directly or through XWayland, and draw with
Vulkan. That needs Linux, clang, the X11 and XRandR headers (`clang
libx11-dev libxrandr-dev` on Debian/Ubuntu), a Vulkan 1.3 driver, and a
desktop session so `$DISPLAY` is set. Sizes and positions are physical
pixels, so on a scaled display the apps look small.

Tested with Bend 2.0.39.
