# Puri for Bend

An experiment in porting [Puri](https://github.com/jbrownson/roc-puri)'s
state-explicit UI components to [Bend 2](https://github.com/bendlang/bend),
with laws checked by Bend's prover.

## Files

- `ask.bend`: asking a stack of placements a question. The one placed later
  (on top) answers first, and only a decline falls through to the one below.
  `Ask.over(base, above)` stacks two. Event handling and hover both work
  this way.
- `handler.bend`: transient event handlers, an `Ask` from events to actions.
  The action type `M` is chosen by the caller, as in the Haskell prototype's
  `actionM`.
- `frame.bend`: what one placement produces: a handler, a hover probe, and
  deferred ink. `Frame.present` runs a frame's phases in order: it resolves
  hover from the settled probes, then paints with that answer.
- `LAWS.bend`: the claims the code must satisfy. They are stated about
  `Ask`, so they hold for handlers and hover probes alike.
- `PROOF.bend`: their proofs.
- `counter.bend`: an example combining two handlers, with a state transition
  as its action type.
- `hover.bend`: an example of overlapping boxes and an occluding panel,
  printing each frame's painting.
- `raster.bend`: a pure-Bend backend that turns fill commands into the
  `Image` quadtree a Bend window shows, splitting only where there's an edge.
- `app.bend`: an interactive window: boxes you can hover and click to select,
  under a panel that blocks both.
- `app_test.bend`: replays scripted events through `app.bend` without a
  window.

## Running

```sh
bend PROOF.bend      # ALL PROOFS CHECK when every law holds
bend counter.bend    # runs the handler example
bend hover.bend      # runs the hover example
bend app.bend        # opens the interactive window
bend app_test.bend   # replays events through the app headlessly
```

A window needs macOS, or Linux with X11. For a native build that runs
on all CPU cores: `bend app.bend -o app && ./app`.

Tested with Bend 2.0.39.
