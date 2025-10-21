import Lean

namespace Mathlib.Tactic.GetUsedThms

open Lean Elab Tactic

/-- Get Ci associated to a name-/
def Name.getCi (name : Name) (parentFunc : Name) : CoreM ConstantInfo := do
  let .some ci := (← getEnv).find? name
    | throwError "{parentFunc} :: Cannot find name {name}"
  return ci

/-- Bool checking if the array contains the constants of the Expr.-/
def Expr.onlyUsesConsts (e : Expr) (names : Array Name) : Bool :=
  e.getUsedConstants.all (fun name => names.contains name)

/-- test -/
def Name.onlyUsesConstsInType (name : Name) (names : Array Name) : CoreM Bool := do
  let ci ← Name.getCi name decl_name%
  return Expr.onlyUsesConsts ci.type names

/-- test -/
def logicConsts : Array Name := #[
    ``True, ``False,
    ``Not, ``And, ``Or, ``Iff,
    ``Eq
  ]

/-- test -/
def Name.onlyLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name logicConsts

/-- test -/
def Name.isTheorem (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  let .thmInfo _ := ci
    | return false
  return true

/-- test -/
def Expr.getUsedTheorems (e : Expr) : CoreM (Array Name) :=
  e.getUsedConstants.filterM Name.isTheorem

open Lean.Meta in
def isNotSimpTheorem (name : Name) : CoreM Bool := do
  return ! (← isInstance name)

open Meta in
def isNotInstance (name : Name) : CoreM Bool := do
  return !(← getSimpTheorems).lemmaNames.contains (.decl name)

def isNotPrivate (name : Name) : Bool := ! (isPrivateName name)

open Expr in
def isNotType (name : Name) : Bool := ! (isType (.const name []))

open Meta Command in
elab "#constants " id:ident : command => do
  let ci ← getConstInfo <| ← resolveGlobalConstNoOverload id
  match ci.value? with
  | some proof =>
    let mut r ← liftCoreM <| Expr.getUsedTheorems proof
    r ← r.filterM fun name => return !(← liftCoreM <| Name.onlyLogicInType name)
    r ← r.filterM (liftCoreM $ isNotSimpTheorem ·)
    r ← r.filterM (liftCoreM $ isNotInstance ·)
    r := r.filter isNotPrivate
    r := r.filter isNotType
    logInfo m!"Got expression: {r}"
  | none => logInfo m!"No proof found for {id}"

#check Nat.zero_add

#constants Nat.add_comm

end Mathlib.Tactic.GetUsedThms
