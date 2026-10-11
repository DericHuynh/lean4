import Lean.Compiler.LCNF.MorphicBorrowCheck

/-!
Check that the independent real-LCNF borrow-escape guard rejects direct
owner consumption and exhaustion while admitting constructor capture.
-/

open Lean
open Lean.Compiler.LCNF
open Lean.Compiler.LCNF.MorphicBorrow.DirectTransfer

private def x : FVarId := ⟨Name.mkSimple "source"⟩
private def y : FVarId := ⟨Name.mkSimple "result"⟩

private def cinfo : CtorInfo :=
  { name := Name.mkSimple "Box.mk"
    cidx := 0, size := 1, usize := 0, ssize := 0 }

private def boxCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "result",
         type := ImpureType.object,
         value := .ctor cinfo #[.fvar x] } (.return y)

private def resetCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "reset",
         type := ImpureType.tobject,
         value := .reset 1 x } (.return y)

private def closureCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "closure",
         type := ImpureType.object,
         value := .pap (Name.mkSimple "f") #[.fvar x] } (.return y)

private def aliasCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "projection",
         type := ImpureType.object,
         value := .oproj 0 x } (.return y)

/-- Runtime regression assertions are separate from kernel proofs in the
    checker module. -/
def smoke : IO Unit := do
  unless hasDirectTransferAux 4 x (.return x) do
    throw <| IO.userError "return of borrowed owner must be rejected"
  if hasDirectTransferAux 4 x (.return y) then
    throw <| IO.userError "return of unrelated result should be allowed"
  unless hasDirectTransferAux 0 x (.return y) do
    throw <| IO.userError "exhausted fuel must reject"
  if hasDirectTransferAux 4 x boxCode then
    throw <| IO.userError "retained constructor field unexpectedly rejected"
  unless hasDirectTransferAux 4 x resetCode do
    throw <| IO.userError "reset of borrowed owner was allowed"
  unless hasDirectTransferAux 4 x closureCode do
    throw <| IO.userError "escaping closure capture was allowed"
  unless hasDirectTransferAux 4 x aliasCode do
    throw <| IO.userError "derived alias was allowed"
  IO.println "bounded actual-LCNF direct-transfer regression passed"

def main : IO Unit := smoke
