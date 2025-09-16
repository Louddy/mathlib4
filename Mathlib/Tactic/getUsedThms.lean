import Lean
import Std
import Aesop

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

open Command in
elab "#constants " id:ident : command => do
  let ci ← getConstInfo <| ← resolveGlobalConstNoOverload id
  match ci.value? with
  | some proof =>
    let r ← liftCoreM <| Expr.getUsedTheorems proof
    let r' ← r.filterM fun name => return !(← liftCoreM <| Name.onlyLogicInType name)
    logInfo m!"Got expression: {r'}"
  | none => logInfo m!"No proof found for {id}"
