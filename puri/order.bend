import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import 0x917f5ed79ae87f89944206ae34045b4e/lemmas.bend as K
import 0xcdaf59a0332a2e0cdb289bf7a32fba62/nat.bend as N
import ./arith.bend as A

# Order lemmas for bend-kit-int's I32. Signed comparison flips the sign bit
# and compares as U32; bend-kit-lemmas relates that to Nat, and
# bend-mathlib supplies Nat's transitivity.

# An I32's place in signed order, as a Nat.
def I32.key(a: I.I32) -> Nat:
  match a:
    case I.I32{x}:
      U32.to_nat(U32.xor(x, I.S32.MIN()))

law le_key:
  for a: I.I32
  for b: I.I32
  {I.I32.is_le(a, b) == Nat.is_le(I32.key(a), I32.key(b)) : Bool}

def le_key(a, b):
  match a b:
    case I.I32{x} I.I32{y}:
      K.u32_is_le_nat(U32.xor(x, I.S32.MIN()), U32.xor(y, I.S32.MIN()))

law lt_key:
  for a: I.I32
  for b: I.I32
  {I.I32.is_lt(a, b) == Nat.is_lt(I32.key(a), I32.key(b)) : Bool}

def lt_key(a, b):
  match a b:
    case I.I32{x} I.I32{y}:
      K.u32_is_lt_nat(U32.xor(x, I.S32.MIN()), U32.xor(y, I.S32.MIN()))

# LAW: a <= b and b < c give a < c.
law le_lt:
  for +a: I.I32
  for +b: I.I32
  for +c: I.I32
  for ab: {I.I32.is_le(a, b) == True{} : Bool}
  for bc: {I.I32.is_lt(b, c) == True{} : Bool}
  {I.I32.is_lt(a, c) == True{} : Bool}

def le_lt(a, b, c, ab, bc):
  Equal.trans(Bool, I.I32.is_lt(a, c), Nat.is_lt(I32.key(a), I32.key(c)), True{}, lt_key(a, c),
    N.lt_of_le_of_lt(I32.key(a), I32.key(b), I32.key(c),
      Equal.trans(Bool, Nat.is_le(I32.key(a), I32.key(b)), I.I32.is_le(a, b), True{},
        Equal.sym(Bool, I.I32.is_le(a, b), Nat.is_le(I32.key(a), I32.key(b)), le_key(a, b)), ab),
      Equal.trans(Bool, Nat.is_lt(I32.key(b), I32.key(c)), I.I32.is_lt(b, c), True{},
        Equal.sym(Bool, I.I32.is_lt(b, c), Nat.is_lt(I32.key(b), I32.key(c)), lt_key(b, c)), bc)))

# LAW: a < b and b <= c give a < c.
law lt_le:
  for +a: I.I32
  for +b: I.I32
  for +c: I.I32
  for ab: {I.I32.is_lt(a, b) == True{} : Bool}
  for bc: {I.I32.is_le(b, c) == True{} : Bool}
  {I.I32.is_lt(a, c) == True{} : Bool}

def lt_le(a, b, c, ab, bc):
  Equal.trans(Bool, I.I32.is_lt(a, c), Nat.is_lt(I32.key(a), I32.key(c)), True{}, lt_key(a, c),
    N.lt_of_lt_of_le(I32.key(a), I32.key(b), I32.key(c),
      Equal.trans(Bool, Nat.is_lt(I32.key(a), I32.key(b)), I.I32.is_lt(a, b), True{},
        Equal.sym(Bool, I.I32.is_lt(a, b), Nat.is_lt(I32.key(a), I32.key(b)), lt_key(a, b)), ab),
      Equal.trans(Bool, Nat.is_le(I32.key(b), I32.key(c)), I.I32.is_le(b, c), True{},
        Equal.sym(Bool, I.I32.is_le(b, c), Nat.is_le(I32.key(b), I32.key(c)), le_key(b, c)), bc)))

# LAW: a <= b and b <= c give a <= c.
law le_le:
  for +a: I.I32
  for +b: I.I32
  for +c: I.I32
  for ab: {I.I32.is_le(a, b) == True{} : Bool}
  for bc: {I.I32.is_le(b, c) == True{} : Bool}
  {I.I32.is_le(a, c) == True{} : Bool}

def le_le(a, b, c, ab, bc):
  Equal.trans(Bool, I.I32.is_le(a, c), Nat.is_le(I32.key(a), I32.key(c)), True{}, le_key(a, c),
    N.le_trans(I32.key(a), I32.key(b), I32.key(c),
      Equal.trans(Bool, Nat.is_le(I32.key(a), I32.key(b)), I.I32.is_le(a, b), True{},
        Equal.sym(Bool, I.I32.is_le(a, b), Nat.is_le(I32.key(a), I32.key(b)), le_key(a, b)), ab),
      Equal.trans(Bool, Nat.is_le(I32.key(b), I32.key(c)), I.I32.is_le(b, c), True{},
        Equal.sym(Bool, I.I32.is_le(b, c), Nat.is_le(I32.key(b), I32.key(c)), le_key(b, c)), bc)))

# LAW: if a <= b fails, then b < a.
law not_le:
  for +a: I.I32
  for +b: I.I32
  for e: {I.I32.is_le(a, b) == False{} : Bool}
  {I.I32.is_lt(b, a) == True{} : Bool}

def not_le(a, b, e):
  %Equal.sym(Bool, I.I32.is_lt(b, a), Nat.is_lt(I32.key(b), I32.key(a)), lt_key(b, a)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(I32.key(b), I32.key(a)), Bool.not(Nat.is_le(I32.key(a), I32.key(b))), Equal.sym(Bool, Bool.not(Nat.is_le(I32.key(a), I32.key(b))), Nat.is_lt(I32.key(b), I32.key(a)), N.not_is_le(I32.key(a), I32.key(b)))) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(I32.key(a), I32.key(b)), I.I32.is_le(a, b), Equal.sym(Bool, I.I32.is_le(a, b), Nat.is_le(I32.key(a), I32.key(b)), le_key(a, b))) : {Bool.not(_) == True{} : Bool}
  %Equal.sym(Bool, I.I32.is_le(a, b), False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# LAW: different I32s have different keys.
law key_inj:
  for a: I.I32
  for b: I.I32
  for e: {I32.key(a) == I32.key(b) : Nat}
  {a == b : I.I32}

def key_inj(a, b, e):
  match a b:
    case I.I32{+x} I.I32{+y}:
      Equal.cong(U32, I.I32, v => I.I32{v}, x, y,
        Equal.trans(U32, x, U32.xor(U32.xor(x, I.S32.MIN()), I.S32.MIN()), y,
          Equal.sym(U32, U32.xor(U32.xor(x, I.S32.MIN()), I.S32.MIN()), x, A.xor_twice(x, I.S32.MIN())),
          Equal.trans(U32, U32.xor(U32.xor(x, I.S32.MIN()), I.S32.MIN()), U32.xor(U32.xor(y, I.S32.MIN()), I.S32.MIN()), y,
            Equal.cong(U32, U32, v => U32.xor(v, I.S32.MIN()), U32.xor(x, I.S32.MIN()), U32.xor(y, I.S32.MIN()), K.u32_to_nat_inj(U32.xor(x, I.S32.MIN()), U32.xor(y, I.S32.MIN()), e)),
            A.xor_twice(y, I.S32.MIN()))))

# Helper: (x + 1) + 2^31 is 1 + (x + 2^31).
law succ_top:
  for +x: U32
  {U32.add(U32.add(x, 1), I.S32.MIN()) == U32.add(1, U32.add(x, I.S32.MIN())) : U32}

def succ_top(x):
  Equal.trans(U32, U32.add(U32.add(x, 1), I.S32.MIN()), U32.add(x, U32.add(1, I.S32.MIN())), U32.add(1, U32.add(x, I.S32.MIN())), A.u32_assoc(x, 1, I.S32.MIN()),
    Equal.trans(U32, U32.add(x, U32.add(1, I.S32.MIN())), U32.add(x, U32.add(I.S32.MIN(), 1)), U32.add(1, U32.add(x, I.S32.MIN())),
      Equal.cong(U32, U32, v => U32.add(x, v), U32.add(1, I.S32.MIN()), U32.add(I.S32.MIN(), 1), U32.add_comm(1, I.S32.MIN())),
      Equal.trans(U32, U32.add(x, U32.add(I.S32.MIN(), 1)), U32.add(U32.add(x, I.S32.MIN()), 1), U32.add(1, U32.add(x, I.S32.MIN())),
        Equal.sym(U32, U32.add(U32.add(x, I.S32.MIN()), 1), U32.add(x, U32.add(I.S32.MIN(), 1)), A.u32_assoc(x, I.S32.MIN(), 1)),
        U32.add_comm(U32.add(x, I.S32.MIN()), 1))))

# Helper: a remainder is at most the number, here 1 + k, for any modulus.
law mod_succ_le:
  for +k: Nat
  for +n: Nat
  N.le(Nat.mod(Nat.add(1n, k), n), 1n+k)

def mod_succ_le(k, n):
  N.mod_le(1n+k, n)

# LAW: adding 1 moves an I32's key up by at most 1: by exactly 1, or down
# to 0 when it wraps.
law key_next:
  for a: I.I32
  N.le(I32.key((a + I.I32{1} : I.I32)), 1n+I32.key(a))

def key_next(a):
  match a:
    case I.I32{+x}:
      %Equal.sym(U32, U32.xor(U32.add(x, 1), I.S32.MIN()), U32.add(U32.add(x, 1), I.S32.MIN()), A.xor_top(U32.add(x, 1))) : N.le(U32.to_nat(_), 1n+U32.to_nat(U32.xor(x, I.S32.MIN())))
      %Equal.sym(U32, U32.add(U32.add(x, 1), I.S32.MIN()), U32.add(1, U32.add(x, I.S32.MIN())), succ_top(x)) : N.le(U32.to_nat(_), 1n+U32.to_nat(U32.xor(x, I.S32.MIN())))
      %Equal.sym(U32, U32.xor(x, I.S32.MIN()), U32.add(x, I.S32.MIN()), A.xor_top(x)) : N.le(U32.to_nat(U32.add(1, U32.add(x, I.S32.MIN()))), 1n+U32.to_nat(_))
      %Equal.sym(Nat, U32.to_nat(U32.add(1, U32.add(x, I.S32.MIN()))), Nat.mod(Nat.add(U32.to_nat(1), U32.to_nat(U32.add(x, I.S32.MIN()))), K.pow2(32n)), K.u32_add_mod(1, U32.add(x, I.S32.MIN()))) : N.le(_, 1n+U32.to_nat(U32.add(x, I.S32.MIN())))
      %Equal.sym(Nat, U32.to_nat(1), 1n, {==}) : N.le(Nat.mod(Nat.add(_, U32.to_nat(U32.add(x, I.S32.MIN()))), K.pow2(32n)), 1n+U32.to_nat(U32.add(x, I.S32.MIN())))
      mod_succ_le(U32.to_nat(U32.add(x, I.S32.MIN())), K.pow2(32n))

# LAW: x0 <= px < x0 + 1 forces px == x0.
law unit_axis:
  for +x0: I.I32
  for +px: I.I32
  for lo: {(x0 <= px : I.I32) == True{} : Bool}
  for hi: {(px < x0 + I.I32{1} : I.I32) == True{} : Bool}
  {px == x0 : I.I32}

def unit_axis(x0, px, lo, hi):
  key_inj(px, x0,
    N.le_antisymm(I32.key(px), I32.key(x0),
      N.le_of_lt_succ(I32.key(px), I32.key(x0),
        N.lt_of_lt_of_le(I32.key(px), I32.key((x0 + I.I32{1} : I.I32)), 1n+I32.key(x0),
          Equal.trans(Bool, Nat.is_lt(I32.key(px), I32.key((x0 + I.I32{1} : I.I32))), I.I32.is_lt(px, (x0 + I.I32{1} : I.I32)), True{},
            Equal.sym(Bool, I.I32.is_lt(px, (x0 + I.I32{1} : I.I32)), Nat.is_lt(I32.key(px), I32.key((x0 + I.I32{1} : I.I32))), lt_key(px, (x0 + I.I32{1} : I.I32))), hi),
          key_next(x0))),
      Equal.trans(Bool, Nat.is_le(I32.key(x0), I32.key(px)), I.I32.is_le(x0, px), True{},
        Equal.sym(Bool, I.I32.is_le(x0, px), Nat.is_le(I32.key(x0), I32.key(px)), le_key(x0, px)), lo)))
