# Puri for Bend

An experiment in porting [Puri](https://github.com/jbrownson/roc-puri)'s
state-explicit UI components to [Bend 2](https://github.com/bendlang/bend),
with laws checked by Bend's prover.

## Files

- `handler.bend`: transient event handlers. A handler looks at an event and
  either declines or answers with an action of a caller-chosen type `M`,
  as in the Haskell prototype's `actionM`. `Handler.plus` combines two
  handlers; the later one has priority.
- `LAWS.bend`: the claims the code must satisfy.
- `PROOF.bend`: their proofs.
- `counter.bend`: a small example combining two handlers, with a state
  transition as its action type.

## Running

```sh
bend PROOF.bend      # ALL PROOFS CHECK when every law holds
bend counter.bend    # runs the example
```

Tested with Bend 2.0.39.
