import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

attribute [local instance] Classical.propDecidable

open Lean Elab Command

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
            type := comparatorNumericExpr value.type
            value := comparatorNumericExpr value.value }
    | _ => throwError "unsupported declaration kind for {sourceName}"
  liftCoreM <| addAndCompile declaration

noncomputable abbrev _private.ErdosProblems.Erdos427.«0».Erdos427.nthPrime :
    Nat → Nat
  := by
  sorry

comparator_copy_declaration _private.ErdosProblems.Erdos427.«0».Erdos427.nthPrime as "_private.ErdosProblems.Erdos427.0.Erdos427.nthPrime"

theorem ComparatorStaging.Erdos427.erdos427 :
    ∀ (n d : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
        @Exists.{1} Nat fun (k : Nat) ↦
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
            (@Dvd.dvd.{0} Nat Nat.instDvd d
              (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Finset.range k) fun (i : Nat) ↦
                _private.ErdosProblems.Erdos427.«0».Erdos427.nthPrime
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n i)))
  := by
  sorry

comparator_copy_declaration ComparatorStaging.Erdos427.erdos427 as "Erdos427.erdos427"

axiom shiu_consecutive_primes :
    ∀ (l : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) l →
        ∀ (a q : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) q →
            a.Coprime q →
              ∀ (N : Nat),
                @Exists.{1} Nat fun (m : Nat) ↦
                  And (@LE.le.{0} Nat instLENat N m)
                    (∀ (i : Nat),
                      @LT.lt.{0} Nat instLTNat i l →
                        q.ModEq
                          (Nat.nth Nat.Prime
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m i))
                          a)
