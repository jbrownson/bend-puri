import Base
import ../window/window.bend as W
import ./bars.bend as B

def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(U32.is_eq(x, y), same(xt, yt))
    case _ _:
      False{}

def nums.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ ", " ++ nums.go(t)

def nums(xs: List<&2, U32>) -> String:
  "[" ++ nums.go(xs) ++ "]"

def agree(ok: Bool) -> String:
  match ok:
    case True{}:
      " agree"
    case False{}:
      " DISAGREE"

# The numbers, the heights kept by patching, and whether they agree with
# mapping the numbers from scratch.
def show(r: Maybe<B.Model>) -> String:
  match r:
    case None{}:
      "quit"
    case Some{B.Model{p, +vs, +hs}}:
      nums(vs) ++ " heights " ++ nums(hs) ++ agree(same(hs, B.heights.of(vs)))

def press(+x: U32, +y: U32, +b: U32) -> List<Event>:
  [Mouse{x, y, b, True{}}, Mouse{x, y, b, False{}}]

def play(frames: List<List<Event>>) -> IO(Maybe<B.Model>):
  W.play(~B.Model, ~B.tick, frames, B.initial())

def main() -> IO(Unit):
  do IO<Unit>:
    a : Maybe<B.Model> <- play([press(50, 300, 1), press(50, 300, 1)])
    IO.print("grow bar 0 twice: " ++ show(a))
    b : Maybe<B.Model> <- play([press(55, 35, 1), press(55, 35, 1)])
    IO.print("add two bars:     " ++ show(b))
    c : Maybe<B.Model> <- play([press(100, 300, 3)])
    IO.print("remove bar 1:     " ++ show(c))
    d : Maybe<B.Model> <- play([press(50, 300, 1), press(55, 35, 1), press(100, 300, 3), press(120, 35, 1)])
    IO.print("then reset:       " ++ show(d))
    e : Maybe<B.Model> <- play([press(300, 200, 1)])
    IO.print("press on nothing: " ++ show(e))
