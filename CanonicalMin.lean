import Canonical
import CanonicalMin.Checker
import CanonicalMin.Search
open Lean Parser Meta Elab Tactic

abbrev DfsM := StateT CanonicalState IO
instance : MonadLiftT CanonicalM DfsM where
  monadLift m s := do m s

mutual
  partial def Canonical.Expr.toTerm (t : Canonical.Expr) (ctx : List (Array String) := []) : CanonicalM MVar := do
    let names := t.lets.map (·.name) ++ t.params.map (·.name)
    t.spine.toSpine (if names.isEmpty then ctx else names :: ctx) names

  partial def Canonical.Spine.toSpine (s : Canonical.Spine) (ctx : List (Array String) := []) (names : Array String) : CanonicalM MVar := do
    let (d, i) := (ctx.zipIdx.findSome? (fun (l, d) => (l.idxOf? s.head).map (d, ·))).get!
    let assn : Assignment := { debruijn := d, index := i, args := (← s.args.mapM (·.toTerm ctx)) }
    let size := (← get).constraints.size
    modify fun x => { x with
      constraints := x.constraints.push #[]
      assignments := x.assignments.push assn
    }
    pure ⟨size, [], names⟩
end

/-- Reads a `Canonical.Expr` as the Π-type `Π lets params . spine`, where each binder's type is
    stored in its `Decl`. A binder without a type is given the type `_u`. -/
partial def Canonical.Expr.toType (ty : Canonical.Expr) (ctx : List (Array String) := []) : CanonicalM TypeMVar := do
  let decls := ty.lets ++ ty.params
  let preferredNames := decls.map (·.name)
  return {
    inputs := ← decls.mapM fun d => (d.type.getD { spine := { head := "_u" } }).toType
      (if preferredNames.isEmpty then ctx else preferredNames :: ctx),
    output := ← ty.toTerm ctx
  }

def disambiguate (str : String) (set : Std.HashSet String) : String := Id.run do
  let mut count := 0
  let mut name := str
  while set.contains name do
    count := count + 1
    name := s!"{str}{count}"
  name

mutual
  partial def MVar.toTerm (s : MVar) (ctx : List (Array String) := []) (set : Std.HashSet String := {}) : CanonicalM Canonical.Expr := do
    let mut set := set
    let mut disambiguated := #[]
    for name in s.preferredNames do
      let name := disambiguate name set
      set := set.insert name
      disambiguated := disambiguated.push name
    return {
      params := disambiguated.map ({ name := · })
      spine := ← s.toSpine (if disambiguated.isEmpty then ctx else disambiguated :: ctx) set
    }

  partial def MVar.toSpine (s : MVar) (ctx : List (Array String)) (set : Std.HashSet String) : CanonicalM Canonical.Spine := do
    match (← get).assignments[s.id]! with
    | none => return Canonical.Spine.mk "_" #[] #[]
    | some assn =>
      let name := (ctx[assn.debruijn]?.bind (·[assn.index]?)).getD "?"
      let args ← assn.args.mapM (·.toTerm ctx set)
      return Canonical.Spine.mk name args #[]
end

partial def MVar.toString (s : MVar) : CanonicalM String := do
  match (← get).assignments[s.id]! with
  | none => pure "_"
  | some assn =>
    let name := (s.lctx[assn.debruijn]?.bind (·.output.preferredNames[assn.index]?)).getD "?"
    let params := (s.lctx[0]?.map (·.output.preferredNames)).getD #[]
    let args := (← assn.args.mapM (·.toString))
    if params.isEmpty && args.isEmpty then return name
    let params := params.foldl (fun x y => s!"{x} {y}") ""
    let args := args.foldl (s!"{·} {·}") ""
    pure s!"(λ{params}. {name}{args})"

def removeTypeInType (typ : Canonical.Expr) : Canonical.Expr :=
  if let some idx := typ.lets.findIdx? (fun d => d.name == "Sort") then
    let uType : Canonical.Expr := { spine := { head := "_u" } }
    { typ with lets := (typ.lets.modify idx ({ · with type := some uType })).push { name := "_u", type := some uType } }
  else typ

def startES : CanonicalM (List Block) := do
  let size := (← get).constraints.size
  modify fun x => { x with
    constraints := x.constraints.push #[]
    assignments := x.assignments.push none
  }
  let mvar := { id := size, lctx := [], preferredNames := #[] }
  let dummy := .vars 0 (some ⟨#[{ inputs := #[], output := mvar }], []⟩)
  return [dummy]

def inhabit (typ : Canonical.Expr) (timeout : Nat) (count : Nat) : DfsM Canonical.CanonicalResult := do
  let result : IO.Ref (Array Canonical.Expr) ← IO.mkRef #[]
  let tmvar ← typ.toType
  let es ← startES
  let typ := Typ.mk tmvar es
  let mvar := MVar.mk (← capacity) [tmvar] tmvar.output.preferredNames
  let tm := Term.mk mvar es
  extend 1
  let time ← IO.monoMsNow
  let steps ← IO.mkRef 0

  process (·.push ·) (← run (check tm typ ⟨1, #[]⟩)).get!.2.2
  try
    iddfs mvar (do
      result.modify (·.push { (← mvar.toTerm) with params := #[] })
      if (← result.get).size >= count then IO.throwServerError ""
    ) (do
      steps.modify (· + 1)
      if (← IO.checkCanceled) || timeout*1000 <= (← IO.monoMsNow) - time then IO.throwServerError ""
    )
  catch _ => pure ()
  return { terms := ← result.get
           attempted_resolutions := 0
           successful_resolutions := 0
           steps := ← steps.get
           last_level_steps := 0
           branching := 0 }

def preprocessIntros (goal : MVarId) (reconstruct : Expr → MetaM Expr) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  goal.withContext do
    let goal := (← mkFreshExprMVar (← goal.getType)).mvarId!
    let (fvars, mvar) ← goal.intros
    let reconstruct' := fun e : Expr => do
      reconstruct (← mkLambdaFVars (fvars.map (.fvar)) e)
    return (mvar, reconstruct')

elab (name := canonicalSeq) "canonical_min" timeout_syntax:(num)? config:optConfig premises_syntax:(Canonical.premises)? : tactic => unsafe do
  let config ← Canonical.canonicalConfig config
  let goal ← getMainGoal
  let consts ← if let some consts := premises_syntax then
    match consts with
    | `(Canonical.premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]
  let (premises, structs) ← Canonical.getPremises goal consts config

  let (goal', reconstruct) ← Canonical.withArityUnfold config.monomorphize do
    Canonical.preprocess goal config structs
  let (goal', reconstruct) ← preprocessIntros goal' reconstruct

  let name := ((← Lean.Elab.Term.getDeclName?).map toString).getD "proof"
  let decl ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
    Canonical.toCanonical name (← goal'.getType) premises (structs.push ``Canonical.Pi) config
  let typ := removeTypeInType decl.type.get!

  if config.debug then
    Elab.admitGoal goal
    dbg_trace typ
    return

  let timeout := if let some timeout := timeout_syntax then timeout.getNat else 5
  let (result, _) ← inhabit typ timeout config.count {}

  let proofs ← Canonical.postprocess result goal' config reconstruct
  Canonical.present proofs goal premises_syntax timeout_syntax
