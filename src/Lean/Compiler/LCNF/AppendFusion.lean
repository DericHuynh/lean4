/-
Copyright (c) 2026 Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.LiveVars

public section

namespace Lean.Compiler.LCNF

/--
Recognize the ByteArray append functions whose semantics are established by
ByteArray.fastAppend3_fusion_correct. The pass runs before borrowing and RC
insertion, so existing analyses recompute ownership after the rewrite.
-/
private def appendArgs? (value : LetValue .impure) :
    Option (Arg .impure × Arg .impure) :=
  match value with
  | .fap name args .. =>
    if (name.toString == "ByteArray.fastAppend" ||
        name.toString == "ByteArray.append") &&
       args.size == 2 then
      some (args[0]!, args[1]!)
    else
      none
  | _ => none

/--
Fuse consecutive append calls only if the intermediate is not live after the
second call. This allows the destination to be reserved once. Borrow and
reference-count decisions are re-inferred by the stock passes afterwards.
-/
partial def Code.fuseByteArrayAppend (code : Code .impure) :
    CompilerM (Code .impure) := do
  match code with
  | .let first (.let second k) =>
    let tail ← (Code.let second k).fuseByteArrayAppend
    let .let second k := tail | return .let first tail
    if let some (a, b) := appendArgs? first.value then
      if let some (.fvar intermediate, c) := appendArgs? second.value then
        if intermediate == first.fvarId &&
           a != .fvar intermediate &&
           b != .fvar intermediate &&
           c != .fvar intermediate &&
           !(← k.isFVarLiveIn intermediate) then
          let fused := { second with
            value := LetValue.fap
              (Name.str (Name.mkSimple "ByteArray") "fastAppend3")
              #[a, b, c] }
          trace[Compiler.appendFusion] "fused two ByteArray appends"
          return .let fused k
    return .let first (.let second k)
  | .let decl k =>
    return .let decl (← k.fuseByteArrayAppend)
  | .jp (.mk fvar name params ty body) k =>
    return .jp
      (.mk fvar name params ty (← body.fuseByteArrayAppend))
      (← k.fuseByteArrayAppend)
  | .cases (.mk ty result discr alts) =>
    let alts ← alts.mapM (·.mapCodeM (·.fuseByteArrayAppend))
    return .cases (.mk ty result discr alts)
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _
  | .setTag _ _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ =>
    return code.updateCont! (← k.fuseByteArrayAppend)
  | .jmp .. | .return .. | .unreach .. =>
    return code

def Decl.fuseByteArrayAppend (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM (·.fuseByteArrayAppend)
  return { decl with value }

/-- Automatic, conservative destination-passing fusion for ordinary Lean code. -/
def fuseByteArrayAppend : Pass :=
  Pass.mkPerDeclaration (Name.mkSimple "fuseByteArrayAppend")
    .impure Decl.fuseByteArrayAppend

builtin_initialize
  registerTraceClass (Name.str (Name.mkSimple "Compiler") "appendFusion")

end Lean.Compiler.LCNF
