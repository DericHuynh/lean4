module

/-!
Checks automatically inferred borrowed-mode functions on ordinary Lean declarations.
The owned object returned by wrap must retain the input when necessary.
This tests program results and alias preservation, not physical reference counts.
-/

namespace MorphicBorrowTest

structure Box where
  contents : List UInt8
  deriving BEq, Repr

@[noinline] def wrap (xs : List UInt8) : Box := ⟨xs⟩

@[noinline] def wrapAgain (xs : List UInt8) : Box := wrap xs

@[noinline] def wrapTwice (xs : List UInt8) : Box × Box :=
  let left := wrap xs
  let right := wrap xs
  (left, right)

@[noinline] def appendPrefix (xs : List UInt8) : List UInt8 := 0 :: xs

@[noinline] def readOnly (xs : List UInt8) : Nat := xs.length

@[noinline] def matchAndWrap (xs : List UInt8) : Box :=
  match xs with
  | [] => ⟨[]⟩
  | _ :: _ => ⟨xs⟩

def check (xs : List UInt8) : IO Unit := do
  let first := wrap xs
  let second := wrapAgain xs
  let (l, r) := wrapTwice xs
  let prefixed := appendPrefix xs
  let branched := matchAndWrap xs
  unless first.contents == xs &&
    second.contents == xs &&
    l.contents == xs && r.contents == xs &&
    prefixed == 0 :: xs &&
    branched.contents == xs &&
    readOnly xs == xs.length do
      throw <| IO.userError "Morphic borrowing changed observed values"
  unless (first.contents ++ xs) == (xs ++ xs) do
    throw <| IO.userError "Borrowed input was not preserved"

def main : IO Unit := do
  for n in [0, 1, 2, 7, 32, 128, 512] do
    let xs := (List.range n).map (fun i => (i % 251).toUInt8)
    check xs
  IO.println "morphic borrow semantics passed"

end MorphicBorrowTest

def main : IO Unit := MorphicBorrowTest.main
