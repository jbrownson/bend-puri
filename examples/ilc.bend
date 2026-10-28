import Base
import ../ilc/change/change.bend as C
import ../ilc/list/list.bend as L

# Numbers that change by "add n".
def adds() -> C.Changes:
  C.Changes{U32, U32, n => x => (x + n : U32)}

# Times ten. Its derivative turns "add n" into "add 10n" without looking
# at the number.
def times10() -> C.Inc<adds(), adds()>:
  C.Inc{x => (x * 10 : U32), x => n => (n * 10 : U32)}

# Insert 5 at position 1, then add 1 to the element now at position 2.
def change() -> L.Change(adds()):
  C.Then{C.Edit{L.Insert{1n, 5}}, C.Edit{L.Update{2n, 1}}}

# The change that mapping times10 makes to [10, 20, 30] when [1, 2, 3]
# changes, computed without mapping the list again.
def mapped() -> L.Change(adds()):
  L.dmap(~adds(), ~adds(), ~times10(), change(), [1, 2, 3])

# Lists of lists, mapped twice: inserting 7 at the front of the second
# inner list inserts 70 there.
def nested() -> L.Change(L.changes(~adds())):
  L.dmap(~L.changes(~adds()), ~L.changes(~adds()), ~L.map.inc(~adds(), ~adds(), ~times10()),
    C.Edit{L.Update{1n, C.Edit{L.Insert{0n, 7}}}}, [[1, 2], [3]])

# The mapped change; [10, 20, 30] patched by it; [1, 2, 3] patched and
# then mapped from scratch, which agrees; and the nested change.
def main() -> L.Change(adds()) & (List<&2, U32> & (List<&2, U32> & L.Change(L.changes(~adds())))):
  (mapped(), (L.patch(~adds(), mapped(), [10, 20, 30]),
    (L.map(~U32, ~U32, ~C.Inc.f(adds(), adds(), times10()), L.patch(~adds(), change(), [1, 2, 3])), nested())))
