import Base
import 0x4eed9d7ac6ece61523d747a9d804e4f0/int.bend as I
import 0x917f5ed79ae87f89944206ae34045b4e/lemmas.bend as K
import 0xcdaf59a0332a2e0cdb289bf7a32fba62/nat.bend as N

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
