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
- `hover.bend`: an example of overlapping boxes and an occluding panel.

## Running

```sh
bend PROOF.bend      # ALL PROOFS CHECK when every law holds
bend counter.bend    # runs the handler example
bend hover.bend      # runs the hover example
```

Tested with Bend 2.0.39.
