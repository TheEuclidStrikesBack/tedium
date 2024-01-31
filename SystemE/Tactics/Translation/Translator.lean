import SystemE.Tactics.Translation.ELang
import SystemE.Relations
import SystemE.Sorts
import SystemE.Tactics.Util
import Lean


open Lean Elab Tactic Meta

namespace SystemE.Tactics.Translation

/- Data structure for storing the declarations extracted from proof context -/
/-
 `consts` : A list of pairs <name, T> : `String` × `ESort` corresponding to geomtetric object variables
 `fetchIdName` : a mapping of free variables to their sanitized name in `consts`.
 `asserts` : A list of `EAssertions`, i.e. propositions in System E
 `numId` : The number of fresh (sanitized) variables which have been created so far
            The `k`'th fresh variable created will have name `fresh_{k-1}`
-/
structure Esmt where
  consts : Array EConst
  fetchIdName : HashMap FVarId String := {}
  asserts : Array EAssertion
  numId : ℕ := 0
deriving Inhabited

abbrev EsmtM := StateT Esmt MetaM

namespace Esmt

def addConstDecl (x : EConst) : EsmtM Unit :=
  modify fun Γ => {Γ with consts := Γ.consts.push x}

def addAssertion (x : EAssertion) : EsmtM Unit :=
  modify fun Γ => {Γ with asserts := Γ.asserts.push x}

def addVar (x : FVarId) (y : String) : EsmtM Unit :=
  modify fun Γ => {Γ with fetchIdName := Γ.fetchIdName.insert x y, numId := Γ.numId + 1}

def getSanitizedName! (fvarId : FVarId) : EsmtM String := do
  return (← get).fetchIdName.find! fvarId

/- Translate an Esmt to a List of Strings, formatted as SMT-Lib2 commands
   This is only really used for tracing/debugging.
-/
private def toArrayString : Esmt → Array String
  | ⟨consts, _, asserts,_⟩ =>
    (consts.map ESort.asConstDecl) ++ (asserts.map (fun a => s!"(assert {EAssertionToString a})"))

def toString (e : Esmt) : String :=
  (toArrayString e).foldl (fun s t => s ++ "\n" ++ t) ""

instance : ToString Esmt := ⟨toString⟩

/- Sanitize a variable name for SMT-Lib2 if it is not purely alphanumeric
   In practice, this is to accomodate things like ` a' `
-/
def sanitize (s : String) : EsmtM String := do
  if s.any (fun e => !e.isAlpha) then
    return "fresh" ++ s!"_{(← get).numId}"
  else
    return s

end Esmt

open Esmt

def getSort! : Expr → ESort
| (Expr.const `Point []) => ESort.Point
| (Expr.const `Line []) => ESort.Line
| (Expr.const `Segment []) => ESort.Segment
| (Expr.const `Circle []) => ESort.Circle
| (Expr.const `Angle []) => ESort.Angle
| (Expr.const `Area []) => ESort.Area
| _ => unreachable!

mutual

/-
  Entry function for the translation of geometric and real-valued terms
  Some objects are easiest to handle using `Expr.getAppFnArgs`, but some
  objects are "nested", for instance `Segment.Length (Segment.endpoints)`
  We handle thse "nested" objects first, and other kinds of objects are handled in `simpleObjs`
-/
partial def translateObject : Expr → EsmtM String
  | Expr.app (Expr.const ``Segment.length _ ) arg => do
    match  (← whnf arg).getAppFnArgs with
    | (``Segment.endpoints, #[(Expr.fvar v1),(Expr.fvar v2)]) => do
      return s!"(SegmentPP {← getSanitizedName! v1} {← getSanitizedName! v2})"
    | _ => dbg_trace "unknown arg to Segment.length" ; failure
  | Expr.app (Expr.const ``Angle.degree _ ) arg => do
    match  (← whnf arg).getAppFnArgs with
    | (``Angle.ofPoints, #[(Expr.fvar v1),(Expr.fvar v2), (Expr.fvar v3)]) =>
      return  s!"(AnglePPP {← getSanitizedName! v1} {← getSanitizedName! v2} {← getSanitizedName! v3})"
    | (``Angle.Right, _) => return "RightAngle"
    | _ => dbg_trace "unknown arg (Angle.degree)"; failure
  | Expr.app (Expr.const ``Triangle.area _ ) arg => do
    match (← whnf arg).getAppFnArgs with
    | (``Triangle.ofPoints, #[(Expr.fvar v1),(Expr.fvar v2),(Expr.fvar v3)]) =>
      return  s!"(AreaPPP {← getSanitizedName! v1} {← getSanitizedName! v2} {← getSanitizedName! v3})"
    | _ => dbg_trace "unknown arg to Triangle.area" failure
  | Expr.fvar v => getSanitizedName! v
  | e => simpleObjs e


/-Translate objects for which all information can be obtained directly from `getAppFnArgs`-/
partial def simpleObjs (e: Expr) : EsmtM String := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, l, r]) => do
    return s!"(+ {← translateObject l} {← translateObject r})"
  | (``HMul.hMul, #[_, _, _, _, l, r]) => do
    return s!"(* {← translateObject l} {← translateObject r})"
  | (``HDiv.hDiv, #[_, _, _, _, l, r]) => do
    return s!"(/ {← translateObject l} {← translateObject r})"
  | (``Angle.ofPoints, #[(Expr.fvar v1),(Expr.fvar v2),(Expr.fvar v3)]) => -- shouldn't be required
    return  s!"(AnglePPP {← getSanitizedName! v1} {← getSanitizedName! v2} {← getSanitizedName! v3})"
  | (``Triangle.ofPoints, #[(Expr.fvar v1),(Expr.fvar v2),(Expr.fvar v3)]) =>
    return  s!"(AreaPPP {← getSanitizedName! v1} {← getSanitizedName! v2} {← getSanitizedName! v3})"
  | (``Angle.Right, _) => return "RightAngle"
  | (``OfNat.ofNat, #[_, _, e]) =>
    match e.getAppFnArgs with
    | (``Zero.toOfNat0, _) => return "0.0"
    | _ => dbg_trace "unknown numeric" ; failure
  | _ => dbg_trace s!"unknown geometric Object kind: {e}"; failure

end

/- Helper functions to create `EAssertions`
   `Γ` : Current SMT encoding state, used for getting sanitized names
   `C` : Binary/Ternary `EAssertion` Constructor
   `e1 e2` : `Expr`s to be translated into strings
-/

private def buildAssertionFrom (C : String → String → EAssertion) (e₁ e₂ : Expr) : EsmtM (EAssertion) := do
  return C (← translateObject e₁) (← translateObject e₂)

private def buildAssertionFrom3 (C : String → String → String → EAssertion) (e₁ e₂ e₃ : Expr) : EsmtM EAssertion := do
  return C (← translateObject e₁) (← translateObject e₂)  (← translateObject e₃)

partial def translateExpr (e : Expr) : EsmtM EAssertion := do
  match e with
  | .mdata _ e' => translateExpr e'
  | .app _ _ =>
    match e.getAppFnArgs with
    | (``Eq, #[_, l, r]) => buildAssertionFrom .eq l r
    | (``LT.lt,#[_, _, l, r]) =>  buildAssertionFrom .lt l r
    | (``LE.le, #[_, _, l, r]) => buildAssertionFrom .lte l r
    | (``GT.gt, #[_, _, l, r]) => buildAssertionFrom .gt l r
    | (``GE.ge, #[_, _, l, r]) => buildAssertionFrom .gte l r
    | (``Point.onLine, #[l, r]) => buildAssertionFrom (fun s l => .erel (.OnL s l)) l r
    | (``Point.isCentre, #[l, r]) =>  buildAssertionFrom (fun s l => .erel (.Centre s l)) l r
    | (``Point.onCircle, #[l, r]) =>  buildAssertionFrom (fun s l => .erel (.OnC s l)) l r
    | (``Point.insideCircle, #[l, r]) =>  buildAssertionFrom (fun s l => .erel (.InC s l)) l r
    | (``between, #[a, b, c]) => buildAssertionFrom3 (fun x y z => .erel (.Between x y z)) a b c
    | (``Point.sameSide, #[a, b, c]) => buildAssertionFrom3 (fun x y z =>  .erel (.SameSide x y z)) a b c
    | (``Circle.intersectsCircle, #[c, d]) => buildAssertionFrom (fun s l => .erel (.IntersectsCC s l)) c d
    | (``Line.intersectsCircle, #[c, d]) => buildAssertionFrom (fun s l => .erel (.IntersectsLC s l)) c d
    | (``Line.intersectsLine, #[c, d]) => buildAssertionFrom (fun s l => .erel (.IntersectsLL s l)) c d
    | (``Ne, #[_, l, r]) => buildAssertionFrom (fun s t => .neg (.eq s t)) l r
    | (``Or, #[l, r]) => return .or (← translateExpr l) (← translateExpr r)
    | (``And, #[l, r]) => return .and (← translateExpr l) (← translateExpr r)
    | (``Not, #[p]) => return .neg (← translateExpr p)
    | x => dbg_trace s!"could not translate expr: {x}"; failure
  | _ => dbg_trace s!"{e} is not an application"; failure

-- I'm not sure what `.mdata` is used for, but it is occasionally encountered parsing the goal
def _root_.Lean.Expr.isFalsemData : Expr → Bool
| .const `False _ => true
| .mdata _ e => isFalsemData e
| _ => false

/- Given a Expr `e` corresponding to the current target, add the negation of `e` to the SMT query.
   Note that if the goal is `False`, then this is a no-op
 -/
def addGoal (Γ : Esmt) (e : Expr) : TacticM Esmt := do
  let e' ← instantiateMVars e
  if e'.isFalsemData then
    return Γ
  else
    let a ← translateExpr e' |>.run' Γ
    return {Γ with asserts := Γ.asserts.push $ EAssertion.neg a}

private def addSanitizedVarName (decl : LocalDecl) : EsmtM Unit := do
  let s := (← decl.fvarId.getUserName).toString
  let nm ← sanitize s
  addVar decl.fvarId nm

private def addEConst (decl : LocalDecl) (τ : Expr) : EsmtM Unit := do
  let x ← getSanitizedName! decl.fvarId
  let s := getSort! τ
  addConstDecl ⟨x,s⟩

private def getESMTfromContextAux : EsmtM Esmt := do
  let ctx ← getLCtx

  -- translate objects (non-prop)
  for decl in ctx do
    let τ ← instantiateMVars decl.type
    if decl.kind != LocalDeclKind.default ∨ (← isProp τ) then
      continue
    addSanitizedVarName decl
    addEConst decl τ
  -- translate propositions
  for decl in ctx do
    let τ ← instantiateMVars decl.type
    if decl.kind != LocalDeclKind.default ∨ !(← isProp τ) then
      continue
    match τ with
    | .forallE .. => continue -- assume this is the goal?
    | x => addAssertion (← translateExpr x)

  get

def getESMTfromContext : TacticM Esmt :=
  withMainContext do
    getESMTfromContextAux.run' {consts := #[], asserts := #[]}

end SystemE.Tactics.Translation
