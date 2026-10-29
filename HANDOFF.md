# Handoff

Notes for picking this work up in a new session, on Jake's own machine
(omarchy, Arch with Hyprland), after a long cloud session. Read
`README.md` first for what the repository is. Delete this file once its
open items are settled.

## How Jake likes to work

- **The laws are the reading surface.** Jake reads `LAWS.bend` files, not
  the code. Laws exist for what a reader needs plus anything tricky. Record
  field accessors and small helper steps don't get laws. Definitions that
  restate a structure (`runs`, `whole`, `lift`, ...) do, even when their
  proof is `{==}`, because that's where a reader learns what they are.
- **Questions are questions.** A question asked to understand something is
  not a request to change it. When something should change, say so and
  why; for changes to what Jake reads (laws, names, structure), wait for a
  yes. For small, clearly-good fixes, decide, do it, and report.
- **Honest assessments, no spin.** Don't agree to be agreeable, and don't
  dress a weakness up as a strength. Example: "the frame is slow, which
  argues for the incremental layer" was rejected; what matters is speed in
  absolute terms, not relative.
- **Names:** prefer descriptive structure to terse names, but don't replace
  spelled-out terms with new abbreviations without asking.
- **Comments don't document Bend itself.**
- **Git:** commit to `master` and push; no pull requests unless asked. End
  commit messages with the attribution lines the harness specifies.
- **GitHub:** don't post issues or comments without Jake's approval.
  Jake filed amage-si/runika#1 (the font checksum) himself; a fix for it
  was drafted and deliberately shelved. Don't bring it up.
- **Verifying a change:** `bend PROOF.bend` and `bend PROOF.bend --verdict`
  must both pass, plus the examples.
  For new laws, run a sabotage check: break the code or the law and confirm
  the checker rejects it.
  Lean 4.34.0 isn't installed on omarchy yet, so `--verdict` can't run
  there (`bend PROOF.bend` can).

## Where the code stands

The ILC layer was reworked heavily in this session; the history is in the
commit messages. As of `26a1506`:

- **`ilc/change/`:**
  - `EditStructure{Value, Edit, apply}`: how a type's values are edited.
  - `reaches(ce)`: one edit gets from any value to any other.
  - `ChangeStructure{structure, reach}`: an edit structure carrying that
    proof, kept live deliberately (see the comment on it).
  - `none(A)`: no edits of its own.
  - `runs(ce)`: lists of edits, applied in order; `run_append` is proved
    in `change.bend`.
  - `whole(ce)`: an edit is `Replace{x}` or `Apply{e}`, using `Whole<ce>`;
    `whole.change_structure` is its change structure.
  - `Inc<ca, cb>{f, df}` and `Inc.ok`.
  - `lift`: lifts a per-edit derivative that gives a run to a derivative
    over runs.
  - `whole.lift` and `recompute`.
- **`ilc/list/`:**
  - The list's own edits: `Insert`, `Delete`, `Update`.
  - `edit_structure`: single edits, which don't reach, proved by
    `edits_not_change_structure`.
  - `change_structure`: runs of edits, proved to reach by `diff` (clear,
    then fill). The proof lives in `list.bend`, because the value carries
    it.
  - `map`, `map.edit`, `dmap` (runs to runs) and `map.inc`.
  - `valid`, `shape`, and the laws `dmap_local`, `dmap_valid` and
    `map_inc_ok`.
- **`examples/bars.bend` and `bars_test.bend`:** a window app whose bar
  heights are a cache patched by `dmap`'s edits. The test checks the cache
  against recomputing. It works, but isn't compelling: the cached work is
  trivial, and every frame is redrawn whole.
- **`window/window.bend`:** runs a puri app (a model, a `view` giving its
  painting as `R.Draw`s, and Base's `tick`) in Ankra's native window,
  drawn by Chromi's GPU path through Voltra. `app.bend` and `bars.bend` use
  it; nothing uses Bend's own window any more. `W.play` replaces
  `App.play` in the tests. It defines `Draw`, the fill the apps paint.
  Checked once on the CPU, before `raster/` was removed: its painting of
  both apps equaled `raster/spec.bend`'s colors on every pixel (and
  differed when the paint order was reversed).
- **Removed at Jake's request:** `raster/`, our proved CPU rasterizer
  (fills into Base's quadtree `Image`), and `puri/order.bend` and
  `puri/arith.bend`, the `I32` order and arithmetic proofs only it used,
  with the BendHub packages `bend-kit-lemmas` and `bend-mathlib` they
  imported. All of it is in history at `c9469f1`.
- **`vendor/amage/`:** Runika, Syllo, Dithra, Splina, Chromi (with
  `gpu.bend`), Voltra and Ankra, at the commits in its README. Voltra and
  Ankra include C.

## Open decisions

1. **An environment parameter for the ILC layer ("option A"): proposed,
   not approved.** `dmap`, `lift` and `map.inc` take their element function
   as a `~` template, and Bend requires template arguments to be closed, so
   they can't capture runtime values like a loaded font. The proposal:
   `~g: E -> C.Inc<ca, cb>` plus a runtime `+env: E`, replacing the current
   signatures (code without context passes `Unit`). The TODO app needs it,
   to cache each row's laid-out text. It changes laws Jake has read, so
   ask first.
2. **Rendering speed: decided, the GPU path** (Jake: "the bend window is
   a toy, we'll need an external window"). See the measurements below.
   What's left:
   - Laying out and rasterizing text is now most of a frame's cost when
     it's redone every frame (~8 ms against ~0.5 ms with glyphs reused),
     which is what the TODO app's cached text is for.
   - Coordinates are physical pixels and Ankra doesn't discover a scale,
     so on Jake's 2x display (Hyprland, `xwayland:force_zero_scaling`)
     the apps are a quarter of the intended size. Chromi's scenes take a
     scale; events would need dividing by it.
   - On screen, colors come out a few levels off (background `0x202428`
     captures as `0x24272b`), most in dark colors. Hyprland's color
     management is on, and the offscreen readback is exact, so it's
     probably the compositor. Not night light: it was off, and every
     channel moves by the same curve, roughly sRGB decoded then re-encoded
     as gamma 2.2.
3. **The TODO app**, the next demo, using AMAGE for text:
   - Items carry their own edits (`Toggle`).
   - "N items left" is kept as an incremental count (a fold).
   - The All/Active/Done views use a new filter derivative. One edit can
     become an insert or delete at a shifted position, so it deserves laws
     and a proof.
   - Each item's laid-out text is cached with `dmap`, which needs option
     A. Changing the filter mode re-filters the cached rows.
   - Typing comes from `Text` and `Key` events.

Parked: tree-backed sequences proved against the list laws (faster
indexing); arrays as an update-only change structure; function changes;
damage-driven repaint.

## Bend and AMAGE notes

- **Run AMAGE text natively.** `bend file.bend` runs through JavaScript,
  which overflows its stack on font work. Use
  `bend file.bend -o app && ./app`. A native binary doesn't print `main`'s
  result; print it yourself.
- **Restrictions the checker enforces:**
  - Define before use.
  - No mutual recursion.
  - `match` and destructuring only on parameters or fields, so give a
    computed value its own def.
  - Operators need a type: `(a + b : U32)`.
  - `+x` to use a value more than once.
  - There's no `?:`.
- **`--verdict` can't model a proof passed as a `~` template parameter.**
  Take it as an ordinary parameter.
- **Arrays are contiguous memory natively:** about 0.9 ns per
  read-blend-write, linear up to 72 million operations. Bend itself isn't
  the bottleneck for pixel work.
- **Base's window** (`App.run`, `Window.frame`) takes only the quadtree
  `Image`; its C code walks the tree. It sends Backspace as `Key` 127 and
  Return as 13; Ankra uses the same key codes and button numbers.
- **Ankra's window:** pointer positions are `F32` physical pixels, sizes
  `U32`. Hyprland now takes Lua for `hyprctl dispatch`; to close a window
  the way a user would:
  `hyprctl dispatch 'hl.dsp.window.close({ window = "address:0x..." })'`.
- **A compound type argument takes parentheses:** `Loop.Step<(M & R)>`.
  A `+` binding needs its type to be `Data`, so a generic model is
  `~M: Data`.
- **Font:** `/usr/share/fonts/liberation/LiberationSans-Regular.ttf`.
- **Text into a Chromi scene.** This worked on 2.0.39: load with `F.load`,
  then pass the `Result` to a def, then this. Imports: `F` is Runika
  `font.bend`, `Sy` is Syllo `main.bend`, `D` is Dithra `main.bend`, `DR`
  is Dithra `raster.bend`, `S` is Chromi `scene.bend`. Render the scene
  with `R.image`, from Chromi `replay.bend`.

```
def paint_mask(m: D.PositionedMask, s: S.Scene, +x: F32, +top: F32, +color: U32) -> S.Scene:
  D.PositionedMask{dx, dy, start, end, DR.Mask{w, h, left, otop, adv, data}} = m
  S.blit_mask(s, 0, (x + dx : F32), (top + dy : F32), w, h, data, color)

def paint_masks(ms: List<&2, D.PositionedMask>, s: S.Scene, +x: F32, +top: F32, +color: U32) -> S.Scene:
  match ms:
    case Nil{}:
      s
    case m <> rest:
      paint_masks(rest, paint_mask(m, s, x, top, color), x, top, color)

def text.masked(r: Result<&2, &2, String, List<&2, D.PositionedMask>>, s: S.Scene, +x: F32, +top: F32, +color: U32) -> S.Scene:
  match r:
    case Done{ms}:
      paint_masks(ms, s, x, top, color)
    case Fail{e}:
      S.reject(s, e)

def text.laid(+font: F.Font, r: Result<&2, &2, String, Sy.Layout>, s: S.Scene, +x: F32, +top: F32, +color: U32) -> S.Scene:
  match r:
    case Done{+layout}:
      text.masked(D.render(font, layout, 20.0, 1.0), s, x, top, color)
    case Fail{e}:
      S.reject(s, e)

def text(+font: F.Font, label: String, s: S.Scene, +x: F32, +top: F32, +color: U32) -> S.Scene:
  text.laid(font, Sy.layout(font, label, 20.0, 1000.0), s, x, top, color)
```

## Measurements

Native builds, in a 4-core cloud container.

| What | Time |
|---|---|
| Process start plus loading the font | ~27 ms, once |
| A 480×360 frame with 8 rows of 25-character text, from scratch (Chromi CPU) | ~31 ms |
| ...of which, 8 rounded rectangles | ~16 ms |
| ...of which, blending ~200 pre-rasterized glyphs | ~14 ms |
| ...of which, laying out and rasterizing the 8 labels | ~4 ms |
| 8 plain rectangles (Chromi) / (our proved raster, since removed) | 0.3 ms / 0.9 ms |
| Blending a pixel in Chromi's quadtree, against a flat `Array` | ~400 ns, against ~0.9 ns |
| Building a 512×512 quadtree `Image` from pixels | ~2.3 ms, worst case |

The same frame on omarchy (Core Ultra X7 358H, Arc B390, power-saver
profile), averaged over 50 frames on the CPU and 500 on the GPU. The GPU
column is Chromi's GPU path through Voltra, offscreen. Chromi's CPU path
uses one core: 1, 4 and 16 threads give the same times.

| What | CPU | GPU |
|---|---|---|
| The frame, glyphs already rasterized | ~29 ms | ~0.5 ms |
| The frame from scratch | 34–37 ms | ~8.2 ms |
| 8 rounded rectangles | 17–18 ms | ~0.2 ms |
| Laying out and rasterizing the 8 labels | ~6 ms | (on the CPU) |
| Drawing, then reading the pixels back, each frame | | ~5 ms |
| Pixels differing from Chromi's CPU output | | 0 of 172,800 |

## Remote Control

A standalone cloud session can't use a folder on Jake's computer, even
with `claude remote-control` running there. The supported route is a
claude.ai **Project**: choose "Work locally" in the project conversation.
It needs Claude Code v2.1.280 or later on the computer and "Require
trusted devices" off. Projects are in a gradual beta rollout. See
<https://code.claude.com/docs/en/claude-projects.md#run-a-thread-on-your-own-computer>.
