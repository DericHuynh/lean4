module

/-!
Exercise three-way byte concatenation after compiler optimization, including
empty inputs, aliasing, and all placements of small and larger buffers.
-/

def append3 (a b c : ByteArray) : ByteArray := (a ++ b) ++ c

def append3Reference (a b c : ByteArray) : ByteArray :=
  (a.data.toList ++ b.data.toList ++ c.data.toList).toByteArray

def check (a b c : ByteArray) : IO Unit := do
  let got := append3 a b c
  let expected := append3Reference a b c
  unless got == expected do
    throw <| IO.userError
      s!"append3 mismatched: sizes {a.size} {b.size} {c.size}"

def main : IO Unit := do
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
