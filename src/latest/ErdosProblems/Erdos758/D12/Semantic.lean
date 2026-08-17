import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Data.Finset.Range

namespace Erdos758.D12Certificate

/-! Semantic reconstruction for the dependency-reduced D12 LRAT suite. -/

private def unorderedPairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y ↦ (x, y)) ++ unorderedPairs xs

private def conjunction : List Prop → Prop
  | [] => True
  | [p] => p
  | p :: q :: ps => p ∧ conjunction (q :: ps)

/-- Zero-based index of an unordered pair in the lexicographic list of the 66
pairs from twelve vertices. -/
def edgeIndex12 (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  a * (23 - a) / 2 + b - a - 1

/-- A list of vertex numbers is homogeneous for the given lexicographically
numbered edge assignment. -/
def Homogeneous (edge : Nat → Prop) (s : List Nat) : Prop :=
  conjunction ((unorderedPairs s).map fun ij ↦
      edge (edgeIndex12 ij.1 ij.2)) ∨
    conjunction ((unorderedPairs s).map fun ij ↦
      ¬ edge (edgeIndex12 ij.1 ij.2))

/-- The elementary side conditions saying that a list represents four
different vertices of `Fin 12`. -/
def ValidFour (s : List Nat) : Prop :=
  s.length = 4 ∧ s.Nodup ∧ s.toFinset ⊆ Finset.range 12

private instance (s : List Nat) : Decidable (ValidFour s) := by
  unfold ValidFour
  infer_instance

/-- The elementary side conditions saying that four lists partition `Fin 12`
into triples. -/
def ValidTriplePartition (a b c d : List Nat) : Prop :=
  a.length = 3 ∧ b.length = 3 ∧ c.length = 3 ∧ d.length = 3 ∧
    (a ++ b ++ c ++ d).Nodup ∧
    (a ++ b ++ c ++ d).toFinset = Finset.range 12

private instance (a b c d : List Nat) : Decidable (ValidTriplePartition a b c d) := by
  unfold ValidTriplePartition
  infer_instance

/-- One of the two homogeneous monomials occurs on four different vertices. -/
def HasHomogeneousFour (edge : Nat → Prop) : Prop :=
  ∃ s : List Nat, ValidFour s ∧ Homogeneous edge s

/-- The twelve vertices split into four homogeneous triples. -/
def HasFourHomogeneousTriples (edge : Nat → Prop) : Prop :=
  ∃ a b c d : List Nat,
    ValidTriplePartition a b c d ∧
      Homogeneous edge a ∧ Homogeneous edge b ∧
      Homogeneous edge c ∧ Homogeneous edge d

/-- A DIMACS edge unit is stored with its one-based variable number and its
required Boolean value. -/
def ViolatesUnit (edge : Nat → Prop) : Nat × Bool → Prop
  | (v, true) => ¬ edge (v - 1)
  | (v, false) => edge (v - 1)

def ViolatesUnits (edge : Nat → Prop) (units : List (Nat × Bool)) : Prop :=
  ∃ u ∈ units, ViolatesUnit edge u

def SatisfiesUnit (edge : Nat → Prop) : Nat × Bool → Prop
  | (v, true) => edge (v - 1)
  | (v, false) => ¬ edge (v - 1)

def SatisfiesUnits (edge : Nat → Prop) (units : List (Nat × Bool)) : Prop :=
  ∀ u ∈ units, SatisfiesUnit edge u

/-- The semantic content of a normalized D12 certificate. -/
def D12Outcome (edge : Nat → Prop) (units : List (Nat × Bool)) : Prop :=
  HasHomogeneousFour edge ∨
    HasFourHomogeneousTriples edge ∨ ViolatesUnits edge units

private theorem not_violatesUnit_of_satisfiesUnit (edge : Nat → Prop)
    (u : Nat × Bool) (h : SatisfiesUnit edge u) : ¬ ViolatesUnit edge u := by
  rcases u with ⟨v, expected⟩
  cases expected
  · exact h
  · exact fun hn ↦ hn h

/-- Eliminate the two certificate alternatives ruled out by the graph-side
no-four-set and normalization hypotheses. -/
theorem fourHomogeneousTriples_of_outcome (edge : Nat → Prop)
    (units : List (Nat × Bool)) (hout : D12Outcome edge units)
    (hfour : ¬ HasHomogeneousFour edge) (hunits : SatisfiesUnits edge units) :
    HasFourHomogeneousTriples edge := by
  rcases hout with h | h | h
  · exact (hfour h).elim
  · exact h
  · obtain ⟨u, hu, hv⟩ := h
    exact (not_violatesUnit_of_satisfiesUnit edge u (hunits u hu) hv).elim

private theorem outcome_of_positive_four (edge : Nat → Prop)
    (units : List (Nat × Bool)) (s : List Nat) (hs : ValidFour s)
    (h : conjunction ((unorderedPairs s).map fun ij ↦
      edge (edgeIndex12 ij.1 ij.2))) :
    D12Outcome edge units := by
  exact Or.inl ⟨s, hs, Or.inl h⟩

private theorem outcome_of_negative_four (edge : Nat → Prop)
    (units : List (Nat × Bool)) (s : List Nat) (hs : ValidFour s)
    (h : conjunction ((unorderedPairs s).map fun ij ↦
      ¬ edge (edgeIndex12 ij.1 ij.2))) :
    D12Outcome edge units := by
  exact Or.inl ⟨s, hs, Or.inr h⟩

private theorem outcome_of_factor (edge : Nat → Prop)
    (units : List (Nat × Bool)) (a b c d : List Nat)
    (hp : ValidTriplePartition a b c d)
    (h : Homogeneous edge a ∧ Homogeneous edge b ∧
      Homogeneous edge c ∧ Homogeneous edge d) :
    D12Outcome edge units := by
  exact Or.inr (Or.inl ⟨a, b, c, d, hp, h⟩)

private theorem outcome_of_unit (edge : Nat → Prop)
    (units : List (Nat × Bool)) (u : Nat × Bool) (hu : u ∈ units)
    (h : ViolatesUnit edge u) : D12Outcome edge units := by
  exact Or.inr (Or.inr ⟨u, hu, h⟩)

open Lean Elab Term Meta

private def choose : (k : Nat) → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs =>
      (choose k xs).map (fun ys ↦ x :: ys) ++ choose (k + 1) xs

private def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y ↦ (x, y)) ++ pairs xs

private def edges : List (Nat × Nat) := pairs (List.range 12)
private def triples : List (List Nat) := choose 3 (List.range 12)

private partial def canonicalPartitions : List Nat → List (List (List Nat))
  | [] => [[]]
  | x :: xs =>
      (choose 2 xs).flatMap fun partners =>
        let block := x :: partners
        let rest := xs.filter fun y => !partners.contains y
        (canonicalPartitions rest).map fun tail => block :: tail

private def edgeIndex (i j : Nat) : Nat :=
  (edges.zipIdx.find? fun p => p.1 = (i, j)).get!.2

private def edgeExpr (e : Expr) (i j : Nat) : Expr :=
  mkApp e (mkNatLit (edgeIndex i j))

private def mkAndExpr : List Expr → MetaM Expr
  | [] => pure (mkConst ``True)
  | [p] => pure p
  | p :: ps => return mkApp2 (mkConst ``And) p (← mkAndExpr ps)

private def mkOrExpr : List Expr → MetaM Expr
  | [] => pure (mkConst ``False)
  | [p] => pure p
  | p :: ps => return mkApp2 (mkConst ``Or) p (← mkOrExpr ps)

private def homogeneousParts (e : Expr) (s : List Nat) : MetaM (Expr × Expr) := do
  let es := (pairs s).map fun ij => edgeExpr e ij.1 ij.2
  return (← mkAndExpr es, ← mkAndExpr (es.map fun p => mkApp (mkConst ``Not) p))

private def homogeneousExpr (e : Expr) (s : List Nat) : MetaM Expr := do
  let (pos, neg) ← homogeneousParts e s
  return mkApp2 (mkConst ``Or) pos neg

private partial def balancedOr (xs : Array Expr) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => mkConst ``False
  | 1 => xs[start]!
  | len =>
      let mid := start + len / 2
      mkApp2 (mkConst ``Or) (balancedOr xs start mid) (balancedOr xs mid stop)

private inductive LeafKind
  | positiveFour (s : List Nat)
  | negativeFour (s : List Nat)
  | impossible (pos neg : Expr) (positive : Bool)
  | factor (parts : List (List Nat))
  | unit (var : Nat) (expected : Bool)
  deriving Inhabited

private structure Leaf where
  raw : Expr
  kind : LeafKind
  deriving Inhabited

private def originalLeaf (e : Expr) (units : List (Nat × Bool))
    (fours : Array (List Nat)) (parts : Array (List (List Nat))) (id : Nat) : MetaM Leaf := do
  if id ≤ 990 then
    let s := fours[(id - 1) / 2]!
    let (pos, neg) ← homogeneousParts e s
    if id % 2 = 1 then return ⟨pos, .positiveFour s⟩
    else return ⟨neg, .negativeFour s⟩
  else if id ≤ 1430 then
    let offset := id - 991
    let s := triples[offset / 2]!
    let (pos, neg) ← homogeneousParts e s
    let hom := mkApp2 (mkConst ``Or) pos neg
    if offset % 2 = 0 then
      return ⟨mkApp2 (mkConst ``And) (mkApp (mkConst ``Not) hom) pos,
        .impossible pos neg true⟩
    else
      return ⟨mkApp2 (mkConst ``And) (mkApp (mkConst ``Not) hom) neg,
        .impossible pos neg false⟩
  else if id ≤ 16830 then
    let part := parts[id - 1431]!
    let hs ← part.mapM (homogeneousExpr e)
    return ⟨← mkAndExpr hs, .factor part⟩
  else
    let (v, expected) := units[id - 16831]!
    let p := mkApp e (mkNatLit (v - 1))
    let raw := if expected then mkApp (mkConst ``Not) p else p
    return ⟨raw, .unit v expected⟩

private def leaves (e : Expr) (ids : List Nat)
    (units : List (Nat × Bool)) : MetaM (Array Leaf) := do
  let mut out := #[]
  let fours := (choose 4 (List.range 12)).toArray
  let needParts := ids.any fun id ↦ 1431 ≤ id && id ≤ 16830
  let parts := if needParts then (canonicalPartitions (List.range 12)).toArray else #[]
  for id in ids do
    out := out.push (← originalLeaf e units fours parts id)
  return out

private def rawSpecialization (raw e : Expr) : MetaM Expr := do
  let mut out := raw
  for (i, j) in edges do
    out := mkApp out (edgeExpr e i j)
  for s in triples do
    out := mkApp out (← homogeneousExpr e s)
  return out

private def natListExpr (xs : List Nat) : MetaM Expr :=
  mkListLit (mkConst ``Nat) (xs.map mkNatLit)

private def unitExpr (v : Nat) (expected : Bool) : MetaM Expr :=
  mkAppM ``Prod.mk #[mkNatLit v,
    mkConst (if expected then ``Bool.true else ``Bool.false)]

private def unitMembershipProof (units : List (Nat × Bool))
    (v : Nat) (expected : Bool) : MetaM Expr := do
  let some index := units.idxOf? (v, expected)
    | throwError "unit is absent from the normalization list"
  let values ← units.mapM fun u => unitExpr u.1 u.2
  let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
  let u := values[index]!
  let tail ← mkListLit prodTy (values.drop (index + 1))
  let mut proof := mkApp3 (mkConst ``List.Mem.head [0]) prodTy u tail
  for i in List.range index |>.reverse do
    let as ← mkListLit prodTy (values.drop (i + 1))
    proof := mkApp5 (mkConst ``List.Mem.tail [0]) prodTy u values[i]! as proof
  return proof

private def impossibleProof (pos neg : Expr) (positive : Bool) (h : Expr) : Expr :=
  let hom := mkApp2 (mkConst ``Or) pos neg
  let mono := mkApp3 (mkConst ``And.right) (mkApp (mkConst ``Not) hom)
    (if positive then pos else neg) h
  let notHom := mkApp3 (mkConst ``And.left) (mkApp (mkConst ``Not) hom)
    (if positive then pos else neg) h
  let witness := if positive then
    mkApp3 (mkConst ``Or.inl) pos neg mono
  else
    mkApp3 (mkConst ``Or.inr) pos neg mono
  mkApp notHom witness

private def leafProof (e unitsExpr : Expr) (units : List (Nat × Bool))
    (leaf : Leaf) (h : Expr) : MetaM Expr := do
  match leaf.kind with
  | .positiveFour s =>
      let S ← natListExpr s
      let valid ← mkAppM ``ValidFour #[S]
      let hs ← mkDecideProof valid
      mkAppM ``outcome_of_positive_four #[e, unitsExpr, S, hs, h]
  | .negativeFour s =>
      let S ← natListExpr s
      let valid ← mkAppM ``ValidFour #[S]
      let hs ← mkDecideProof valid
      mkAppM ``outcome_of_negative_four #[e, unitsExpr, S, hs, h]
  | .impossible pos neg positive =>
      let target ← mkAppM ``D12Outcome #[e, unitsExpr]
      return mkApp2 (mkConst ``False.elim [0]) target
        (impossibleProof pos neg positive h)
  | .factor parts =>
      let ps ← parts.mapM natListExpr
      unless ps.length = 4 do throwError "bad partition"
      let a := ps[0]!
      let b := ps[1]!
      let c := ps[2]!
      let d := ps[3]!
      let valid ← mkAppM ``ValidTriplePartition #[a, b, c, d]
      let hp ← mkDecideProof valid
      mkAppM ``outcome_of_factor #[e, unitsExpr, a, b, c, d, hp, h]
  | .unit v expected =>
      let u ← unitExpr v expected
      let hu ← unitMembershipProof units v expected
      mkAppM ``outcome_of_unit #[e, unitsExpr, u, hu, h]

private partial def bridgeRange (e unitsExpr : Expr) (units : List (Nat × Bool)) (ls : Array Leaf)
    (start stop : Nat) (h : Expr) : MetaM Expr := do
  match stop - start with
  | 0 =>
      let target ← mkAppM ``D12Outcome #[e, unitsExpr]
      return mkApp2 (mkConst ``False.elim [0]) target h
  | 1 => leafProof e unitsExpr units ls[start]! h
  | len =>
      let mid := start + len / 2
      let left := balancedOr (ls.map fun l => l.raw) start mid
      let right := balancedOr (ls.map fun l => l.raw) mid stop
      let target ← mkAppM ``D12Outcome #[e, unitsExpr]
      withLocalDeclD `hl left fun hl => do
        let pl ← bridgeRange e unitsExpr units ls start mid hl
        let fl ← mkLambdaFVars #[hl] pl
        withLocalDeclD `hr right fun hr => do
          let pr ← bridgeRange e unitsExpr units ls mid stop hr
          let fr ← mkLambdaFVars #[hr] pr
          return mkApp6 (mkConst ``Or.elim) left right target h fl fr

private partial def decodeList (e : Expr) : MetaM (List Expr) := do
  let e ← withTransparency .all <| whnf e
  match e.getAppFn.constName? with
  | some ``List.nil => return []
  | some ``List.cons =>
      let args := e.getAppArgs
      let head := args[args.size - 2]!
      let tail := args[args.size - 1]!
      return head :: (← decodeList tail)
  | _ => throwError "expected a reducible list, got {e}"

private def decodeNat (e : Expr) : MetaM Nat := do
  let e ← withTransparency .all <| whnf e
  let some n := e.rawNatLit? | throwError "expected a natural literal, got {e}"
  return n

private def decodeBool (e : Expr) : MetaM Bool := do
  let e ← withTransparency .all <| whnf e
  match e.constName? with
  | some ``Bool.true => return true
  | some ``Bool.false => return false
  | _ => throwError "expected a Boolean literal, got {e}"

private def decodeUnit (e : Expr) : MetaM (Nat × Bool) := do
  let e ← withTransparency .all <| whnf e
  unless e.getAppFn.constName? = some ``Prod.mk do
    throwError "expected a pair, got {e}"
  let args := e.getAppArgs
  return (← decodeNat args[args.size - 2]!, ← decodeBool args[args.size - 1]!)

private def bridgedSpecializationWithIds (raw : Expr) (ids : List Nat)
    (unitsExpr e : Expr) : MetaM Expr := do
  let units ← (decodeList unitsExpr).bind fun xs => xs.mapM decodeUnit
  let ls ← leaves e ids units
  unless ls.size = ids.length do throwError "unexpected reduced D12 leaf count: {ls.size}"
  let h ← rawSpecialization raw e
  bridgeRange e unitsExpr units ls 0 ls.size h

private def bridgedSpecialization (raw idsExpr unitsExpr e : Expr) : MetaM Expr := do
  let ids ← (decodeList idsExpr).bind fun xs => xs.mapM decodeNat
  bridgedSpecializationWithIds raw ids unitsExpr e

private def decodeIdText (e : Expr) : MetaM (List Nat) := do
  let e ← withTransparency .all <| whnf e
  let .lit (.strVal text) := e | throwError "expected reduced-clause ID text, got {e}"
  let mut ids := []
  for word in text.split Char.isWhitespace do
    unless word.isEmpty do
      let some id := word.toNat? | throwError "invalid clause ID {word}"
      ids := id :: ids
  return ids.reverse

private def caseLeavesFromText (idsExpr unitsExpr e : Expr) : MetaM
    (List Nat × List (Nat × Bool) × Array Leaf) := do
  let ids ← decodeIdText idsExpr
  let units ← (decodeList unitsExpr).bind fun xs => xs.mapM decodeUnit
  let ls ← leaves e ids units
  unless ls.size = ids.length do throwError "unexpected reduced D12 leaf count: {ls.size}"
  return (ids, units, ls)

private def checkRange (ls : Array Leaf) (start stop : Nat) : MetaM Unit := do
  unless start < stop && stop ≤ ls.size do
    throwError "invalid D12 semantic range [{start}, {stop}) for {ls.size} clauses"

private def semanticRangeType (idsExpr unitsExpr e : Expr)
    (start stop : Nat) : MetaM Expr := do
  let (_, _, ls) ← caseLeavesFromText idsExpr unitsExpr e
  checkRange ls start stop
  let raw := balancedOr (ls.map fun l ↦ l.raw) start stop
  let target ← mkAppM ``D12Outcome #[e, unitsExpr]
  mkArrow raw target

private def semanticRangeProof (idsExpr unitsExpr e : Expr)
    (start stop : Nat) : MetaM Expr := do
  let (_, units, ls) ← caseLeavesFromText idsExpr unitsExpr e
  checkRange ls start stop
  let raw := balancedOr (ls.map fun l ↦ l.raw) start stop
  withLocalDeclD `h raw fun h => do
    let proof ← bridgeRange e unitsExpr units ls start stop h
    mkLambdaFVars #[h] proof

syntax "d12CaseSemantic(" term ", " term ", " term ", " term ")" : term
syntax "d12CaseSemanticFile(" term ", " term ", " term ", " term ")" : term
syntax "d12CaseRaw(" term ", " term ")" : term
syntax "d12CaseRange(" term ", " term ", " term ", " num ", " num ")" : term
syntax "d12CaseRangeProof(" term ", " term ", " term ", " num ", " num ")" : term

elab_rules : term
  | `(d12CaseSemantic($raw, $ids, $units, $e)) => do
      let natListTy := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
      let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
      let unitListTy := mkApp (mkConst ``List [.zero]) prodTy
      bridgedSpecialization (← elabTerm raw none)
        (← elabTerm ids (some natListTy)) (← elabTerm units (some unitListTy))
        (← elabTerm e none)
  | `(d12CaseSemanticFile($raw, $ids, $units, $e)) => do
      let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
      let unitListTy := mkApp (mkConst ``List [.zero]) prodTy
      let idsExpr ← elabTerm ids (some (mkConst ``String))
      bridgedSpecializationWithIds (← elabTerm raw none) (← decodeIdText idsExpr)
        (← elabTerm units (some unitListTy)) (← elabTerm e none)
  | `(d12CaseRaw($raw, $e)) => do
      rawSpecialization (← elabTerm raw none) (← elabTerm e none)
  | `(d12CaseRange($ids, $units, $e, $start, $stop)) => do
      let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
      let unitListTy := mkApp (mkConst ``List [.zero]) prodTy
      let idsExpr ← elabTerm ids (some (mkConst ``String))
      let unitsExpr ← elabTerm units (some unitListTy)
      let some start := start.raw.isNatLit? | throwError "natural range start expected"
      let some stop := stop.raw.isNatLit? | throwError "natural range stop expected"
      semanticRangeType idsExpr unitsExpr (← elabTerm e none) start stop
  | `(d12CaseRangeProof($ids, $units, $e, $start, $stop)) => do
      let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
      let unitListTy := mkApp (mkConst ``List [.zero]) prodTy
      let idsExpr ← elabTerm ids (some (mkConst ``String))
      let unitsExpr ← elabTerm units (some unitListTy)
      let some start := start.raw.isNatLit? | throwError "natural range start expected"
      let some stop := stop.raw.isNatLit? | throwError "natural range stop expected"
      semanticRangeProof idsExpr unitsExpr (← elabTerm e none) start stop

end Erdos758.D12Certificate
