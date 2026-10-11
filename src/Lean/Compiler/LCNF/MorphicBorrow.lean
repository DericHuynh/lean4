/-
Copyright (c) 2026 Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.ExportAttr
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.Options

public section

namespace Lean.Compiler

/-- Enable conservative interprocedural lifetime/mode inference before ordinary
    borrowing inference. The flag permits an optimized-stock ablation. -/
register_builtin_option compiler.morphicBorrow : Bool := {
  defValue := true
  descr := "infer borrowed lifetime modes and RC retain obligations"
}

end Lean.Compiler

namespace Lean.Compiler.LCNF.MorphicBorrow

open ImpureType

/-- Mode constraints are ordered by required ownership. A retained field needs
    a new owning reference before its source borrow can end. -/
inductive Mode where
  | read
  | retain
  | owned
  deriving Inhabited, BEq, DecidableEq, Repr

def Mode.join : Mode → Mode → Mode
  | .owned, _ | _, .owned => .owned
  | .retain, _ | _, .retain => .retain
  | _, _ => .read

theorem Mode.join_comm (a b : Mode) : a.join b = b.join a := by
  cases a <;> cases b <;> rfl

theorem Mode.join_assoc (a b c : Mode) :
    (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Mode.join_idem (a : Mode) : a.join a = a := by
  cases a <;> rfl

/-- Retained means a borrow may escape only through a fresh owned reference;
    the original RC insertion pass remains responsible for that retain. -/
def Mode.requiresRetain : Mode → Bool
  | .retain => true
  | _ => false

theorem Mode.retain_requiresRetain :
    Mode.requiresRetain .retain = true := by simp [Mode.requiresRetain]

private abbrev Modes := Std.HashMap Name (Array Mode)

private def argUses (x : FVarId) : Arg .impure → Bool
  | .fvar y => y == x
  | _ => false

private def argsUse (x : FVarId) (args : Array (Arg .impure)) : Bool :=
  args.any (argUses x)

/-- Resolve a direct call using the current SCC mode summary or a previously
    compiled borrowing signature. Unknown callees conservatively need ownership. -/
private def calleeModes? (summaries : Modes) (fn : Name) :
    CompilerM (Option (Array Mode)) := do
  if let some modes := summaries[fn]? then
    return some modes
  let some signature ← getImpureSignature? fn | return none
  return some <| signature.params.map fun p =>
    if p.borrow then .read else .owned

private def callUse (x : FVarId) (summaries : Modes) (fn : Name)
    (args : Array (Arg .impure)) : CompilerM Mode := do
  unless argsUse x args do return .read
  let some callee ← calleeModes? summaries fn | return .owned
  if args.size != callee.size then return .owned
  let mut mode := Mode.read
  for i in [:args.size] do
    if argUses x args[i]! then
      mode := mode.join callee[i]!
  return mode

/-- Unknown allocation, mutation, closure or ownership transfers do not
    create inferred-borrow permissions. Calls are handled with validated
    signatures or SCC constraints; retained constructor fields need stock RC. -/
private def letUse (x : FVarId) (summaries : Modes)
    (value : LetValue .impure) : CompilerM Mode := do
  match value with
  | .ctor _ args =>
      return if argsUse x args then .retain else .read
  | .fap fn args =>
      callUse x summaries fn args
  | .reset _ y =>
      return if x == y then .owned else .read
  | .reuse y _ _ args =>
      return if x == y || argsUse x args then .owned else .read
  | .oproj _ y _ | .uproj _ y _ | .sproj _ _ y _ =>
      return if x == y then .owned else .read
  | .isShared _ _ | .unbox _ _ =>
      return .read
  | .box _ y _ =>
      return if x == y then .owned else .read
  | .fvar fn args =>
      return if x == fn || argsUse x args then .owned else .read
  | .pap _ args =>
      return if argsUse x args then .owned else .read
  | .lit .. | .erased => return .read
  | _ => return .owned

private partial def codeUse (x : FVarId) (summaries : Modes)
    (code : Code .impure) : CompilerM Mode := do
  match code with
  | .let decl k =>
      let current ← letUse x summaries decl.value
      let following ← codeUse x summaries k
      return current.join following
  | .jp (.mk _ _ _ _ body) k =>
      let useBody ← codeUse x summaries body
      let useCont ← codeUse x summaries k
      return useBody.join useCont
  | .cases (.mk _ _ _ alts) =>
      let mut result := Mode.read
      for alt in alts do
        result := result.join (← codeUse x summaries alt.getCode)
      return result
  | .jmp _ args =>
      return if argsUse x args then .owned else .read
  | .return y =>
      return if x == y then .owned else .read
  | .unreach .. =>
      return .owned
  | .oset y _ arg k _ =>
      let cont ← codeUse x summaries k
      return if x == y || argUses x arg then .owned else cont
  | .uset y _ z k _ | .sset y _ _ z _ k _ =>
      let cont ← codeUse x summaries k
      return if x == y || x == z then .owned else cont
  | .setTag y _ k _ | .del y k _ =>
      let cont ← codeUse x summaries k
      return if x == y then .owned else cont
  | .inc y _ _ _ k _ | .dec y _ _ _ _ k _ =>
      let cont ← codeUse x summaries k
      return if x == y then .owned else cont

/-- The ABI of exported declarations is fixed. Only safe reference-typed
    parameters of ordinary non-exported declarations can be reconsidered. -/
private def initialModes (decl : Decl .impure) : CompilerM (Array Mode) := do
  let exported := isExport (← getEnv) decl.name
  return decl.params.map fun p =>
    if exported || !decl.safe || !p.type.isPossibleRef then
      .owned
    else
      .read

private def initSCC (decls : Array (Decl .impure)) : CompilerM Modes := do
  let mut result : Modes := {}
  for decl in decls do
    result := result.insert decl.name (← initialModes decl)
  return result

private def advance (decls : Array (Decl .impure))
    (base previous : Modes) : CompilerM Modes := do
  let mut next := previous
  for decl in decls do
    let initial := base[decl.name]?.getD #[]
    let old := previous[decl.name]?.getD #[]
    let mut out : Array Mode := #[]
    for i in [:decl.params.size] do
      let seed := initial[i]?.getD .owned
      let prior := old[i]?.getD .owned
      if seed == .owned then
        out := out.push .owned
      else
        let mode ← match decl.value with
          | .code code => codeUse decl.params[i]!.fvarId previous code
          | .extern .. => pure Mode.owned
        out := out.push (prior.join mode)
    next := next.insert decl.name out
  return next

private def sameModes (decls : Array (Decl .impure)) (a b : Modes) : Bool :=
  decls.all fun decl =>
    (a[decl.name]?.getD #[]) == (b[decl.name]?.getD #[])

/-- A finite-height ascending SCC iteration. A failure to reach a fixed
    point within the conservative bound leaves stock inference unchanged. -/
private def solve? (decls : Array (Decl .impure)) : CompilerM (Option Modes) := do
  let initial ← initSCC decls
  let mut current := initial
  let width := decls.foldl (fun n decl => n + decl.params.size) (0 : Nat)
  for _ in [:2 * width + 2] do
    let next ← advance decls initial current
    if sameModes decls current next then
      return some next
    current := next
  return none

/-- The mandatory ownership solver runs after this pass. Only retained
    constructor/call input modes are annotated; read-only parameters are
    already borrowed by stock Lean. Reference counts remain explicit. -/
private def applyModes (decls : Array (Decl .impure)) (modes : Modes) :
    CompilerM (Array (Decl .impure)) :=
  decls.mapM fun decl => do
    let inferred := modes[decl.name]?.getD #[]
    let mut params := decl.params
    for i in [:params.size] do
      let p := params[i]!
      if inferred[i]?.getD .owned == .retain && !p.borrow then
        params := params.set! i { p with borrow := true }
        trace[Compiler.morphicBorrow]
          "retained-borrow {decl.name} parameter {i}; RC insertion covers escaping storage"
    return { decl with params }

def inferMorphicBorrow : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "inferMorphicBorrow"
  run := fun decls => do
    unless compiler.morphicBorrow.get (← getOptions) do
      return decls
    let some summaries ← solve? decls
      | return decls
    applyModes decls summaries

/-- Observe the resulting modes after stock forced-ownership inference.
    This is diagnostic only, not a resource certificate. -/
def auditMorphicBorrow : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "auditMorphicBorrow"
  run := fun decls => do
    for decl in decls do
      trace[Compiler.morphicBorrow]
        "final {decl.name}: borrowed={decl.params.map (fun p => p.borrow)}"
    return decls

builtin_initialize
  registerTraceClass (Name.str (Name.mkSimple "Compiler") "morphicBorrow") (inherited := true)

end Lean.Compiler.LCNF.MorphicBorrow
