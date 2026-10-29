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
  must both pass, plus the examples and `bend raster/raster_test.bend`.
  For new laws, run a sabotage check: break the code or the law and confirm
  the checker rejects it.

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
- **`vendor/amage/`:** Runika, Syllo, Dithra, Splina and Chromi, CPU only,
  at the commits in its README. Voltra (GPU) and Ankra (window) aren't
  vendored; both include C.

## Open decisions

1. **An environment parameter for the ILC layer ("option A"): proposed,
   not approved.** `dmap`, `lift` and `map.inc` take their element function
   as a `~` template, and Bend requires template arguments to be closed, so
   they can't capture runtime values like a loaded font. The proposal:
   `~g: E -> C.Inc<ca, cb>` plus a runtime `+env: E`, replacing the current
   signatures (code without context passes `Unit`). The TODO app needs it,
   to cache each row's laid-out text. It changes laws Jake has read, so
   ask first.
2. **Rendering speed.** Too slow in absolute terms; see the measurements
   below. Options:
   - **Chromi's GPU path** through Voltra and Ankra. This is why the work
     moved to Jake's machine. Nothing has been tried yet.
   - **A flat-array CPU renderer.** Draw rectangles, rounded corners and
     Dithra's glyph masks into an `Array<U32>`, then build the quadtree
     `Image` Base's window wants. Estimated ~3 ms per full frame, but only
     the pieces were measured. Threading the array through the quadtree
     build is awkward given the restrictions below.
   - **Improving Chromi's CPU path upstream.** Rounded rectangles seem to
     compute coverage over their whole area.
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
  Return as 13. `App.play` replays events without a window.
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

Native builds, in a 4-core cloud container. Expect different numbers on
omarchy; the proportions are what matter.

| What | Time |
|---|---|
| Process start plus loading the font | ~27 ms, once |
| A 480×360 frame with 8 rows of 25-character text, from scratch (Chromi CPU) | ~31 ms |
| ...of which, 8 rounded rectangles | ~16 ms |
| ...of which, blending ~200 pre-rasterized glyphs | ~14 ms |
| ...of which, laying out and rasterizing the 8 labels | ~4 ms |
| 8 plain rectangles (Chromi) / (our proved raster) | 0.3 ms / 0.9 ms |
| Blending a pixel in Chromi's quadtree, against a flat `Array` | ~400 ns, against ~0.9 ns |
| Building a 512×512 quadtree `Image` from pixels | ~2.3 ms, worst case |

## Remote Control

A standalone cloud session can't use a folder on Jake's computer, even
with `claude remote-control` running there. The supported route is a
claude.ai **Project**: choose "Work locally" in the project conversation.
It needs Claude Code v2.1.280 or later on the computer and "Require
trusted devices" off. Projects are in a gradual beta rollout. See
<https://code.claude.com/docs/en/claude-projects.md#run-a-thread-on-your-own-computer>.
