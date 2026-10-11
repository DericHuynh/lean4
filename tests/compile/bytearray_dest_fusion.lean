module

/-!
Exercise three-way byte concatenation after compiler optimization, including
empty inputs, aliasing, and all placements of small and larger buffers.
-/

namespace ByteArrayFusionTest

def append3 (a b c : ByteArray) : ByteArray := (a ++ b) ++ c

def append3Direct (a b c : ByteArray) : ByteArray :=
  (a.fastAppend b).fastAppend c

/-- The intermediate also escapes as a returned component; do not fuse it. -/
def retainsIntermediate (a b c : ByteArray) : ByteArray × ByteArray :=
  let intermediate := a ++ b
  (intermediate, intermediate ++ c)

/-- This shared intermediate cannot be erased: it is used twice. -/
def duplicateIntermediate (a b : ByteArray) : ByteArray :=
  let intermediate := a ++ b
  intermediate ++ intermediate

def append3Reference (a b c : ByteArray) : ByteArray :=
  (a.data.toList ++ b.data.toList ++ c.data.toList).toByteArray

def check (a b c : ByteArray) : IO Unit := do
  let got := append3 a b c
  let expected := append3Reference a b c
  unless got == expected do
    throw <| IO.userError
      s!"append3 mismatched: sizes {a.size} {b.size} {c.size}"
  unless append3Direct a b c == expected do
    throw <| IO.userError "direct fastAppend chain changed byte contents"
  let (intermediate, full) := retainsIntermediate a b c
  unless intermediate == a.fastAppend b && full == expected do
    throw <| IO.userError "escaping append intermediate was not preserved"
  let both := a.fastAppend b
  unless duplicateIntermediate a b == both.fastAppend both do
    throw <| IO.userError "double-use intermediate was not preserved"

def run : IO Unit := do
  let sizes := #[0, 1, 2, 3, 7, 64, 512, 4096]
  let mut arrays := #[]
  for n in sizes do
    let xs := ((List.range n).map (fun i => ((17 * i + 83) % 256).toUInt8)).toByteArray
    arrays := arrays.push xs
  for a in arrays do
    for b in arrays do
      for c in arrays do
        check a b c
        check a a c
        check a b a
        check a a a
  IO.println "bytearray 3-way fusion semantic tests passed"

end ByteArrayFusionTest

def main : IO Unit := ByteArrayFusionTest.run
