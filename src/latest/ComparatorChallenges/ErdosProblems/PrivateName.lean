import Lean

open Lean Meta Elab Command

private def comparatorNameWithNumericComponents (s : String) : Name :=
  s.splitOn "." |>.foldl (init := .anonymous) fun name component =>
    match component.toNat? with
    | some n => .num name n
    | none => .str name component

private def comparatorNumericName : Name → Name
  | .anonymous => .anonymous
  | .num parent n => .num (comparatorNumericName parent) n
  | .str parent component =>
      let parent := comparatorNumericName parent
      match component.toNat? with
      | some n => .num parent n
      | none => .str parent component

private def comparatorNumericExpr (e : Expr) : Expr :=
  e.replace fun
    | .const name levels => some <| .const (comparatorNumericName name) levels
    | _ => none

elab "comparator_private_ref " target:str : term => do
  let targetName := comparatorNameWithNumericComponents target.getString
  unless (← getEnv).contains targetName do
    throwError "unknown declaration {targetName}"
  mkConstWithFreshMVarLevels targetName

elab "comparator_copy_declaration " source:ident " as " target:str : command => do
  let sourceName := source.getId
  let some info := (← getEnv).find? sourceName
    | throwError "unknown source declaration {sourceName}"
  let targetName := comparatorNameWithNumericComponents target.getString
  let declaration ← match info with
    | .axiomInfo value =>
        pure <| Declaration.axiomDecl
          { value with name := targetName, type := comparatorNumericExpr value.type }
    | .defnInfo value =>
        pure <| Declaration.defnDecl
          { value with
            name := targetName
            type := comparatorNumericExpr value.type
            value := comparatorNumericExpr value.value }
    | .thmInfo value =>
        pure <| Declaration.thmDecl
          { value with
            name := targetName
            type := comparatorNumericExpr value.type,
            value := comparatorNumericExpr value.value }
    | _ => throwError "unsupported declaration kind for {sourceName}"
  liftCoreM <| addDecl declaration
