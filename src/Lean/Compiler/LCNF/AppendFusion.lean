/-
Copyright (c) 2026 Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager

public section

namespace Lean.Compiler.LCNF

/-- The precise known-safe library operation, established by
    ByteArray.fastAppend3_fusion_correct. -/
private def helperName : Name :=
  Name.str (Name.mkSimple "ByteArray") "fastAppend3"

private def isByteAppend (n : Name) : Bool :=
  n == Name.str (Name.mkSimple "ByteArray") "fastAppend"

/--
Recognize a short nonescaping append chain in pure LCNF. The HAppend variant
requires both known ByteArray typeclass instances and the matching method
projection. Other dictionaries or additional uses never match.
-/
private def appendChain? : Code .pure → Option
    (LetDecl .pure × Arg .pure × Arg .pure × Arg .pure)
  | .let first (.let final (.return ret)) =>
    if ret != final.fvarId then none
    else
      match first.value, final.value with
      | .const n _ args _, .const m _ args' _ =>
        if isByteAppend n && isByteAppend m &&
           args.size == 2 && args'.size == 2 &&
           args'[0]! == .fvar first.fvarId &&
           args'[1]! != .fvar first.fvarId then
          some (final, args[0]!, args[1]!, args'[1]!)
        else none
      | _, _ => none
  | .let inst (.let happ (.let method (.let first (.let final (.return ret))))) =>
    if ret != final.fvarId then none
    else
      match inst.value, happ.value, method.value, first.value, final.value with
      | .const n _ iargs _, .const hn _ hargs _, .proj pn ix src _,
        .fvar fn args, .fvar fn' args' =>
        if n.toString == "ByteArray.instAppend" &&
           iargs.isEmpty &&
           hn.toString == "instHAppendOfAppend" &&
           hargs.size == 2 && hargs[1]! == .fvar inst.fvarId &&
           pn.toString == "HAppend" && ix == 0 && src == happ.fvarId &&
           fn == method.fvarId && fn' == method.fvarId &&
           args.size == 2 && args'.size == 2 &&
           args'[0]! == .fvar first.fvarId &&
           args'[1]! != .fvar first.fvarId then
          some (final, args[0]!, args[1]!, args'[1]!)
        else none
      | _, _, _, _, _ => none
  | _ => none

/-- Rewrite only the exact established local equivalence. The remaining
    stock pipeline re-infers lifetime, borrowing, reset/reuse and RC. -/
private partial def fuseCode (code : Code .pure) : CompilerM (Code .pure) := do
  if let some (final, a, b, c) := appendChain? code then
    trace[Compiler.appendFusion] "fused three ByteArray segments into one reserved destination"
    return .let { final with value := .const helperName [] #[a, b, c] }
      (.return final.fvarId)
  match code with
  | .let d k =>
    return .let d (← fuseCode k)
  | .fun (.mk f name params ty body) k _ =>
    return .fun (.mk f name params ty (← fuseCode body)) (← fuseCode k)
  | .jp (.mk f name params ty body) k =>
    return .jp (.mk f name params ty (← fuseCode body)) (← fuseCode k)
  | .cases (.mk ty result discr alts) =>
    return .cases (.mk ty result discr
      (← alts.mapM (·.mapCodeM fuseCode)))
  | .return .. | .jmp .. | .unreach .. =>
    return code

private def Decl.fuseAppend (decl : Decl .pure) : CompilerM (Decl .pure) := do
  -- Do not rewrite the fallback branch of the implementation into a call to
  -- itself during a later compiler bootstrap.
  if decl.name == helperName then
    return decl
  let value ← decl.value.mapCodeM fuseCode
  return { decl with value }

/-- Enabled for all Lean source by the built-in pass manager, before inlining. -/
def fuseByteArrayAppend : Pass :=
  Pass.mkPerDeclaration (Name.mkSimple "fuseByteArrayAppend") .base
    Decl.fuseAppend

builtin_initialize
  registerTraceClass (Name.str (Name.mkSimple "Compiler") "appendFusion")

end Lean.Compiler.LCNF
