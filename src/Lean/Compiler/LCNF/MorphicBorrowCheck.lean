/-
Copyright (c) 2026 Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.Basic

public section

namespace Lean.Compiler.LCNF.MorphicBorrow.DirectTransfer

private def argUses (x : FVarId) : Arg .impure → Bool
  | .fvar y => y == x
  | _ => false

private def argsUse (x : FVarId) (args : Array (Arg .impure)) : Bool :=
  args.any (argUses x)

/-- Independently reject known operations that consume, move, or expose the
    original owner. Constructors and direct calls remain candidates: the
    normal mode solver and stock RC insertion must justify them separately.
    This checker does not certify nested heap aliases or native semantics. -/
def dangerousValue (x : FVarId) : LetValue .impure → Bool
  | .reset _ y => x == y
  | .reuse y _ _ args => x == y || argsUse x args
  | .oproj _ y => x == y
  | .uproj _ y => x == y
  | .sproj _ _ y => x == y
  | .box _ y => x == y
  | .fvar y args => x == y || argsUse x args
  | .pap _ args => argsUse x args
  | .ctor .. | .fap .. | .lit .. | .erased | .unbox .. | .isShared .. => false
  | _ => true

/-- A total fuel-bounded scan of actual impure LCNF. Exhaustion rejects
    the proposed borrowed mode instead of inventing an ownership proof. -/
def hasDirectTransferAux : Nat → FVarId → Code .impure → Bool
  | 0, _, _ => true
  | fuel + 1, x, code =>
    match code with
    | .let decl k =>
      dangerousValue x decl.value || hasDirectTransferAux fuel x k
    | .jp (.mk _ _ _ _ body) k =>
      hasDirectTransferAux fuel x body || hasDirectTransferAux fuel x k
    | .cases (.mk _ _ _ alts) =>
      alts.any (fun alt => hasDirectTransferAux fuel x alt.getCode)
    | .jmp _ args => argsUse x args
    | .return y => x == y
    | .unreach .. => false
    | .oset y _ arg k _ =>
      x == y || argUses x arg || hasDirectTransferAux fuel x k
    | .uset y _ z k _ | .sset y _ _ z _ k _ =>
      x == y || x == z || hasDirectTransferAux fuel x k
    | .setTag y _ k _ | .del y k _ =>
      x == y || hasDirectTransferAux fuel x k
    | .inc y _ _ _ k _ | .dec y _ _ _ _ k _ =>
      x == y || hasDirectTransferAux fuel x k

def validate (x : FVarId) (code : Code .impure) : Bool :=
  !hasDirectTransferAux (code.size + 1) x code

def NoDirectTransfer (x : FVarId) (code : Code .impure) : Prop :=
  hasDirectTransferAux (code.size + 1) x code = false

/-- Acceptance is evidence about this *actual* LCNF syntax, not a lifetime
    or physical heap theorem. -/
theorem validate_sound (x : FVarId) (code : Code .impure)
    (h : validate x code = true) : NoDirectTransfer x code := by
  unfold validate NoDirectTransfer at *
  cases hx : hasDirectTransferAux (code.size + 1) x code <;>
    simp [hx] at h ⊢

#print axioms validate_sound

end Lean.Compiler.LCNF.MorphicBorrow.DirectTransfer
