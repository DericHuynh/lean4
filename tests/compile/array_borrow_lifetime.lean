module

/-!
Regression for array element lifetime propagation in inferred borrowing.
Returned elements must remain valid after the source array has gone out of
scope, even when the array element is reference-typed and shared.
-/

namespace BorrowLifetimeTest

@[noinline] def escapeElement (xs : Array String) : String :=
  xs[0]!

@[noinline] def readOnly (xs : Array String) : Nat :=
  xs.size

@[noinline] def escapeViaBranch (xs : Array String) (flag : Bool) : String :=
  if flag then xs[0]! else xs[1]!

def mainTest : IO Unit := do
  let a := #["hello", "world"]
  let kept := escapeElement a
  unless kept == "hello" do
    throw <| IO.userError "owned array element escaped incorrectly"
  let copy := a
  unless readOnly copy == 2 do
    throw <| IO.userError "borrowed read changed array size"
  let first := escapeViaBranch a true
  let second := escapeViaBranch a false
  unless first == "hello" && second == "world" do
    throw <| IO.userError "borrow propagation through branch changed result"
  let saved := escapeElement (#[kept, second])
  unless saved == "hello" && copy[0]! == "hello" do
    throw <| IO.userError "array element lifetime was not retained"
  IO.println "array borrowing lifetime regression passed"

end BorrowLifetimeTest

def main : IO Unit := BorrowLifetimeTest.mainTest
