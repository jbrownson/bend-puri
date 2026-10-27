import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import 0x917f5ed79ae87f89944206ae34045b4e/lemmas.bend as K
import 0xcdaf59a0332a2e0cdb289bf7a32fba62/nat.bend as N

# Arithmetic lemmas for U32 and bend-kit-int's I32 that the packages don't
# have yet, built on bend-kit-lemmas (U32 against Nat) and bend-mathlib.

# LAW: reducing before adding doesn't change the remainder:
# (x mod n + y) mod n is (x + y) mod n.
law mod_add_mod:
  for +x: Nat
  for +y: Nat
  for +n: Nat
  {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(x, y), n) : Nat}

# Write x as x mod n plus a multiple of n, move the multiple to the end,
# and drop it.
def mod_add_mod(x, y, n):
  %N.mod_add_div(x, n) : {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(_, y), n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mod(x, n), Nat.mul(n, Nat.div(x, n))), y), Nat.add(Nat.add(Nat.mod(x, n), y), Nat.mul(n, Nat.div(x, n))), N.add_right_comm(Nat.mod(x, n), Nat.mul(n, Nat.div(x, n)), y)) : {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(_, n) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.add(Nat.mod(x, n), y), Nat.mul(n, Nat.div(x, n))), n), Nat.mod(Nat.add(Nat.mod(x, n), y), n), N.add_mul_mod_self_left(Nat.add(Nat.mod(x, n), y), n, Nat.div(x, n)))

# Helper: the value of (a + b) + c.
law assoc_left:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.to_nat(U32.add(U32.add(a, b), c)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}

def assoc_left(a, b, c):
  %Equal.sym(Nat, U32.to_nat(U32.add(U32.add(a, b), c)), Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), K.pow2(32n)), K.u32_add_mod(U32.add(a, b), c)) : {_ == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), K.pow2(32n)), K.u32_add_mod(a, b)) : {Nat.mod(Nat.add(_, U32.to_nat(c)), K.pow2(32n)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), K.pow2(32n)), U32.to_nat(c)), K.pow2(32n)), Nat.mod(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), K.pow2(32n)), mod_add_mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c), K.pow2(32n))) : {_ == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), N.add_assoc(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c))) : {Nat.mod(_, K.pow2(32n)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  {==}

# Helper: the value of a + (b + c).
law assoc_right:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.to_nat(U32.add(a, U32.add(b, c))) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}

def assoc_right(a, b, c):
  %Equal.sym(Nat, U32.to_nat(U32.add(a, U32.add(b, c))), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), K.pow2(32n)), K.u32_add_mod(a, U32.add(b, c))) : {_ == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(b, c)), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), K.pow2(32n)), K.u32_add_mod(b, c)) : {Nat.mod(Nat.add(U32.to_nat(a), _), K.pow2(32n)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), K.pow2(32n))), Nat.add(Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), K.pow2(32n)), U32.to_nat(a)), N.add_comm(U32.to_nat(a), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), K.pow2(32n)))) : {Nat.mod(_, K.pow2(32n)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), K.pow2(32n)), U32.to_nat(a)), K.pow2(32n)), Nat.mod(Nat.add(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a)), K.pow2(32n)), mod_add_mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a), K.pow2(32n))) : {_ == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a)), Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), N.add_comm(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a))) : {Nat.mod(_, K.pow2(32n)) == Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)) : Nat}
  {==}

# LAW: U32 addition is associative.
law u32_assoc:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.add(U32.add(a, b), c) == U32.add(a, U32.add(b, c)) : U32}

def u32_assoc(a, b, c):
  K.u32_to_nat_inj(U32.add(U32.add(a, b), c), U32.add(a, U32.add(b, c)),
    Equal.trans(Nat, U32.to_nat(U32.add(U32.add(a, b), c)), Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)), U32.to_nat(U32.add(a, U32.add(b, c))), assoc_left(a, b, c),
      Equal.sym(Nat, U32.to_nat(U32.add(a, U32.add(b, c))), Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), K.pow2(32n)), assoc_right(a, b, c))))

# Helper: adding a word to itself with carry-in c moves every bit up one
# place and puts c at the bottom.
law adc_self:
  for +n: Nat
  for w: Word(n)
  for c: Bool
  {Word.adc(n, w, w, False{}, c) == Word.shl.put(n, c, w) : Word(n)}

def adc_self(n, w, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          match b c:
            case False{} False{}:
              Equal.cong(Word(p), Word(1n+p), v => WCon{False{}, v}, Word.adc(p, t, t, False{}, False{}), Word.shl.put(p, False{}, t), adc_self(p, t, False{}))
            case False{} True{}:
              Equal.cong(Word(p), Word(1n+p), v => WCon{True{}, v}, Word.adc(p, t, t, False{}, False{}), Word.shl.put(p, False{}, t), adc_self(p, t, False{}))
            case True{} False{}:
              Equal.cong(Word(p), Word(1n+p), v => WCon{False{}, v}, Word.adc(p, t, t, False{}, True{}), Word.shl.put(p, True{}, t), adc_self(p, t, True{}))
            case True{} True{}:
              Equal.cong(Word(p), Word(1n+p), v => WCon{True{}, v}, Word.adc(p, t, t, False{}, True{}), Word.shl.put(p, True{}, t), adc_self(p, t, True{}))

# LAW: shifting a U32 left by one bit adds it to itself.
law shl_add:
  for x: U32
  {U32.shl(x) == U32.add(x, x) : U32}

def shl_add(x):
  match x:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          Equal.sym(U32, U32.add(U32{WCon{b, t}}, U32{WCon{b, t}}), U32.shl(U32{WCon{b, t}}),
            Equal.cong(Word(32n), U32, v => U32{v}, Word.adc(32n, WCon{b, t}, WCon{b, t}, False{}, False{}), Word.shl.put(32n, False{}, WCon{b, t}), adc_self(32n, WCon{b, t}, False{})))

# LAW: I32 addition is associative.
law i32_assoc:
  for a: I.I32
  for b: I.I32
  for c: I.I32
  {I.I32.add(I.I32.add(a, b), c) == I.I32.add(a, I.I32.add(b, c)) : I.I32}

def i32_assoc(a, b, c):
  match a b c:
    case I.I32{+x} I.I32{+y} I.I32{+z}:
      Equal.cong(U32, I.I32, v => I.I32{v}, U32.add(U32.add(x, y), z), U32.add(x, U32.add(y, z)), u32_assoc(x, y, z))

# A word of 1+n bits with only its top bit set.
def top(n: Nat) -> Word(1n+n):
  match n:
    case 0n:
      WCon{True{}, WNil{}}
    case 1n+p:
      WCon{False{}, top(p)}

# Helper: flipping the top bit is adding it, since the carry out of the top
# bit is dropped.
law word_xor_top:
  for +n: Nat
  for w: Word(1n+n)
  {Word.xor(1n+n, w, top(n)) == Word.adc(1n+n, w, top(n), False{}, False{}) : Word(1n+n)}

def word_xor_top(n, w):
  match n:
    case 0n:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              {==}
            case True{}:
              {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              Equal.cong(Word(1n+p), Word(2n+p), v => WCon{False{}, v}, Word.xor(1n+p, t, top(p)), Word.adc(1n+p, t, top(p), False{}, False{}), word_xor_top(p, t))
            case True{}:
              Equal.cong(Word(1n+p), Word(2n+p), v => WCon{True{}, v}, Word.xor(1n+p, t, top(p)), Word.adc(1n+p, t, top(p), False{}, False{}), word_xor_top(p, t))

# LAW: flipping a U32's top bit adds 2^31, modulo 2^32.
law xor_top:
  for x: U32
  {U32.xor(x, I.S32.MIN()) == U32.add(x, I.S32.MIN()) : U32}

def xor_top(x):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.xor(32n, w, top(31n)), Word.adc(32n, w, top(31n), False{}, False{}), word_xor_top(31n, w))

# Helper: xor-ing a word with m twice gives it back.
law word_xor_twice:
  for +n: Nat
  for w: Word(n)
  for m: Word(n)
  {Word.xor(n, Word.xor(n, w, m), m) == w : Word(n)}

def word_xor_twice(n, w, m):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              match m:
                case WCon{c, +u}:
                  match c:
                    case False{}:
                      Equal.cong(Word(p), Word(1n+p), v => WCon{False{}, v}, Word.xor(p, Word.xor(p, t, u), u), t, word_xor_twice(p, t, u))
                    case True{}:
                      Equal.cong(Word(p), Word(1n+p), v => WCon{False{}, v}, Word.xor(p, Word.xor(p, t, u), u), t, word_xor_twice(p, t, u))
            case True{}:
              match m:
                case WCon{c, +u}:
                  match c:
                    case False{}:
                      Equal.cong(Word(p), Word(1n+p), v => WCon{True{}, v}, Word.xor(p, Word.xor(p, t, u), u), t, word_xor_twice(p, t, u))
                    case True{}:
                      Equal.cong(Word(p), Word(1n+p), v => WCon{True{}, v}, Word.xor(p, Word.xor(p, t, u), u), t, word_xor_twice(p, t, u))

# LAW: xor-ing a U32 with m twice gives it back.
law xor_twice:
  for x: U32
  for m: U32
  {U32.xor(U32.xor(x, m), m) == x : U32}

def xor_twice(x, m):
  match x m:
    case U32{w} U32{v}:
      Equal.cong(Word(32n), U32, k => U32{k}, Word.xor(32n, Word.xor(32n, w, v), v), w, word_xor_twice(32n, w, v))
