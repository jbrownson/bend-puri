import Base
import ../window/window.bend as W
import ./app.bend as Ap

def show(r: Maybe<Ap.Model>) -> String:
  match r:
    case None{}:
      "quit"
    case Some{Ap.Model{p, s}}:
      "selected: " ++ U32.show(s)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Maybe<Ap.Model> <- W.play(~Ap.Model, ~Ap.tick, [[Move{200, 180}], [Mouse{100, 100, 1, True{}}, Mouse{100, 100, 1, False{}}]], Ap.initial())
    IO.print(show(a))
    b : Maybe<Ap.Model> <- W.play(~Ap.Model, ~Ap.tick, [[Mouse{100, 100, 1, True{}}], [Mouse{350, 200, 1, True{}}]], Ap.initial())
    IO.print(show(b))
    c : Maybe<Ap.Model> <- W.play(~Ap.Model, ~Ap.tick, [[Mouse{350, 200, 1, True{}}], [Mouse{90, 200, 1, True{}}]], Ap.initial())
    IO.print(show(c))
    d : Maybe<Ap.Model> <- W.play(~Ap.Model, ~Ap.tick, [[Move{10, 10}, Close{}]], Ap.initial())
    IO.print(show(d))
