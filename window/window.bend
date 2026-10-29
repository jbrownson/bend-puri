import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import ../puri/geom.bend as G
import ../vendor/amage/Ankra/window.bend as A
import ../vendor/amage/Ankra/app.bend as Loop
import ../vendor/amage/Chromi/scene.bend as Sc
import ../vendor/amage/Chromi/geometry.bend as CG
import ../vendor/amage/Chromi/gpu.bend as Gpu
import ../vendor/amage/Voltra/gpu.bend as V

# A puri app in a native window: Ankra's window and events, with the app's
# painting drawn on the GPU as a Chromi draw list, which Voltra draws and
# presents. The app has the shape it has for Base's window, except that
# its view gives the painting instead of an image.

# What an app paints: a rectangle filled with a 0xRRGGBB color.
type Draw is Data:
  FillRect{rect: G.Rect, rgb: U32}

# Events
# ------

# A pointer coordinate as Base's events carry it: 0 left of or above the
# window.
def pixel(v: F32) -> U32:
  F32.to_u32(F32.max(v, 0.0))

# Ankra's input as Base's event, where Base has one.
def event(i: A.Input) -> Maybe<Event>:
  match i:
    case A.PointerDown{x, y, b, m}:
      Some{Mouse{pixel(x), pixel(y), b, True{}}}
    case A.PointerUp{x, y, b, m}:
      Some{Mouse{pixel(x), pixel(y), b, False{}}}
    case A.PointerMoved{x, y}:
      Some{Move{pixel(x), pixel(y)}}
    case A.KeyDown{c, r, m}:
      Some{Key{c, True{}}}
    case A.KeyUp{c, m}:
      Some{Key{c, False{}}}
    case A.TextTyped{t}:
      Some{Text{t}}
    case A.Wheel{x, y, dx, dy}:
      Some{Scroll{pixel(x), pixel(y), dx, dy}}
    case A.CloseRequested{}:
      Some{Close{}}
    case _:
      None{}

def events.add(m: Maybe<Event>, rest: List<Event>) -> List<Event>:
  match m:
    case Some{e}:
      Con{e, rest}
    case None{}:
      rest

def events(ins: List<&2, A.Input>) -> List<Event>:
  match ins:
    case Nil{}:
      Nil{}
    case Con{i, rest}:
      events.add(event(i), events(rest))

# Painting
# --------

def float(v: I.I32) -> F32:
  +u = I.I32.to_u32(v)
  Bool.pick(F32, U32.is_ge(u, 2147483648), F32.neg(U32.to_f32((0 - u : U32))), U32.to_f32(u))

def rgba(+rgb: U32) -> U32:
  ((rgb << 8n) .|. 255 : U32)

# The painting onto a scene, in order, so later commands are on top.
def paint(ds: List<&2, Draw>, s: Sc.Scene) -> Sc.Scene:
  match ds:
    case Nil{}:
      s
    case Con{FillRect{G.Rect{x, y, w, h}, rgb}, rest}:
      paint(rest, Sc.fill_rect(s, CG.Rect{float(x), float(y), float(w), float(h)}, rgba(rgb)))

# The loop
# --------

def resized(m: Maybe<&2, A.Size>, +r: Gpu.Renderer) -> IO(Gpu.Renderer):
  match m:
    case None{}:
      IO.pure(Gpu.Renderer, r)
    case Some{A.Size{w, h}}:
      Gpu.resize(r, w, h)

# The app's answer to a batch: a new state to draw, or quitting.
def next(-M: Data, r: Gpu.Renderer, m: M, n: Maybe<M>) -> Loop.Step<(M & Gpu.Renderer)>:
  match n:
    case Some{m1}:
      Loop.Redraw{(m1, r)}
    case None{}:
      Loop.Stop{(m, r)}

def update(~M: Data, ~tick: List<Event> -> M -> IO(Maybe<M>), win: A.Win,
  batch: List<&2, A.Input>, st: M & Gpu.Renderer) -> IO(Loop.Step<(M & Gpu.Renderer)>):
  (+m, r) = st
  +es = batch
  do IO<Loop.Step<(M & Gpu.Renderer)>>:
    +r1 : Gpu.Renderer <- resized(A.resized(es, None{}), r)
    n : Maybe<M> <- tick(events(es), m)
    return next(M, r1, m, n)

def scene(~M: Data, ~view: M -> List<&2, Draw>, ~bg: U32, m: M, size: V.Size) -> Sc.Scene:
  V.Size{w, h} = size
  paint(view(m), Sc.new(w, h, 1.0, rgba(bg)))

# Another frame is owed when the swapchain was rebuilt while presenting.
def drawn(-M: Data, pending: Bool, r: Gpu.Renderer, m: M) -> Loop.Step<(M & Gpu.Renderer)>:
  match pending:
    case True{}:
      Loop.Redraw{(m, r)}
    case False{}:
      Loop.Keep{(m, r)}

def draw(~M: Data, ~view: M -> List<&2, Draw>, ~bg: U32, win: A.Win,
  st: M & Gpu.Renderer) -> IO(Loop.Step<(M & Gpu.Renderer)>):
  (+m, +r) = st
  do IO<Loop.Step<(M & Gpu.Renderer)>>:
    +r1 : Gpu.Renderer <- Gpu.draw(r, scene(~M, ~view, ~bg, m, Gpu.target_size(r)))
    return drawn(M, Gpu.pending(r1), r1, m)

# The GPU objects go before the window they were made from.
def finish(-M: Data, end: A.Win & M & Gpu.Renderer) -> IO(Unit):
  (win, m, r) = end
  do IO<Unit>:
    +report : V.Report <- Gpu.close(r)
    Unit <- IO.print(V.report.show(report))
    +left : U32 <- A.close(win)
    return Unit{}

# Runs the app in a window of the given size on a background of `bg`
# (0xRRGGBB) until the window closes or `tick` gives None.
def run(~M: Data, ~view: M -> List<&2, Draw>, ~tick: List<Event> -> M -> IO(Maybe<M>),
  ~bg: U32, title: String, +width: U32, +height: U32, model: M) -> IO(Unit):
  do IO<Unit>:
    +win : A.Win <- IO.try(A.Win, A.open(A.options(title, width, height)))
    +native : List<&2, U32> <- A.native(win)
    +r : Gpu.Renderer <- Gpu.open(native, width, height, True{})
    end : A.Win & M & Gpu.Renderer <- Loop.run(~(M & Gpu.Renderer),
      ~(w => b => st => update(~M, ~tick, w, b, st)),
      ~(w => st => draw(~M, ~view, ~bg, w, st)), win, (model, r))
    finish(M, end)

# Replays batches of events through `tick` without a window, as Base's
# App.play does: the model after the last batch, or None if `tick` quit.
def play.more(-M: Data, rest: M -> IO(Maybe<M>), next: Maybe<M>) -> IO(Maybe<M>):
  match next:
    case None{}:
      IO.pure(Maybe<M>, None{})
    case Some{m}:
      rest(m)

def play(~M: Data, ~tick: List<Event> -> M -> IO(Maybe<M>), frames: List<List<Event>>, model: M) ->
  IO(Maybe<M>):
  match frames:
    case Nil{}:
      IO.pure(Maybe<M>, Some{model})
    case Con{events, rest}:
      IO.bind(Maybe<M>, Maybe<M>, tick(events, model), play.more(M, m => play(~M, ~tick, rest, m)))
