import Base
import ../ilc/change/change.bend as C
import ../ilc/list/list.bend as L

# Numbers that change by "add n".
def adds() -> C.EditStructure:
  C.EditStructure{U32, U32, n => x => (x + n : U32)}

# Times ten. Its derivative turns "add n" into "add 10n" without looking
# at the number.
def times10() -> C.Inc<adds(), adds()>:
  C.Inc{x => (x * 10 : U32), x => n => (n * 10 : U32)}

# Insert 5 at position 1, then add 1 to the element now at position 2.
def edits() -> List<&2, L.Edit.of(adds())>:
  [L.Insert{1n, 5}, L.Update{2n, 1}]

# The edits that mapping times10 makes to [10, 20, 30] when [1, 2, 3] is
# edited, computed without mapping the list again.
def mapped() -> List<&2, L.Edit.of(adds())>:
  L.dmap(~adds(), ~adds(), ~times10(), edits(), [1, 2, 3])

# Lists of lists, mapped twice: inserting 7 at the front of the second
# inner list inserts 70 there.
def nested() -> List<&2, L.Edit.of(C.runs(~L.edit_structure(~adds())))>:
  L.dmap(~C.runs(~L.edit_structure(~adds())), ~C.runs(~L.edit_structure(~adds())), ~L.map.inc(~adds(), ~adds(), ~times10()),
    [L.Update{1n, [L.Insert{0n, 7}]}], [[1, 2], [3]])

# The run diff gives from [1, 2, 3] to [7, 8].
def jump() -> List<&2, L.Edit.of(adds())>:
  L.diff(~adds(), [1, 2, 3], [7, 8])

# The mapped edits; [10, 20, 30] patched by them; [1, 2, 3] patched and
# then mapped from scratch, which agrees; the nested edits; and diff's run,
# with [1, 2, 3] patched by it.
def main() -> List<&2, L.Edit.of(adds())> & (List<&2, U32> & (List<&2, U32> & (List<&2, L.Edit.of(C.runs(~L.edit_structure(~adds())))> & (List<&2, L.Edit.of(adds())> & List<&2, U32>)))):
  (mapped(), (L.patch(~adds(), mapped(), [10, 20, 30]),
    (L.map(~U32, ~U32, ~C.Inc.f(adds(), adds(), times10()), L.patch(~adds(), edits(), [1, 2, 3])), (nested(),
    (jump(), L.patch(~adds(), jump(), [1, 2, 3]))))))
