/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedCodeAssembly
import ErdosProblems.Erdos1165.AnnularRecursiveProfileShape
import ErdosProblems.Erdos1165.AnnularProfileChildClockIdentification
import Mathlib.Data.List.SplitLengths

/-!
# A fixed-level frontier of a recursive profile code

The recursive profile code is rooted at the first free coarse scale.  The
padded renewal instead sees all descendants at one later fixed scale.  This
file records that ordered frontier without changing any literal child code.
The construction is purely structural: a node is traversed in chronological
parent-major order, while a code already at the target level contributes one
frontier item.
-/

namespace Erdos1165.AsymmetricPaddedRecursiveFrontier

open scoped ENNReal

open AnnularRecursiveDecoratedProfileCode
open AnnularOffspringKernelRadial
open AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveProfileShape ThickPoint
open AnnularProfileNestedEdge AnnularProfileChildClockIdentification
open MarkedBridgeFactorization
open PathInsertion ProfileGapChain

noncomputable section

/-- One literal recursive gap occurring at the target frontier level. -/
structure RecursiveFrontierItem
    (n p : ℕ) (center : Point) : Type where
  tree : ProfileRefinementTree
  entrance : ProfileCycleMiddlePoint n p center
  endpoint : ProfileCycleOuterPoint n p center
  code : RecursiveProfileGapCode n p center tree entrance endpoint

/-- Recursive product mass carried by one frontier item. -/
def RecursiveFrontierItem.mass
    {n p : ℕ} {center : Point} (item : RecursiveFrontierItem n p center) :
    ℝ≥0∞ :=
  recursiveProfileGapCodeMass n p center item.tree item.entrance item.endpoint
    item.code

/-- Transport a frontier item along an equality of its level. -/
def RecursiveFrontierItem.castLevel
    {n k p : ℕ} {center : Point} (h : k = p)
    (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (code : RecursiveProfileGapCode n k center tree u w) :
    RecursiveFrontierItem n p center := by
  subst p
  exact ⟨tree, u, w, code⟩

mutual
  /-- Ordered target-level descendants of one recursive gap code. -/
  def recursiveProfileGapFrontier
      (n p : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        k + depth = p →
        RecursiveProfileGapCode n k center tree u w →
          List (RecursiveFrontierItem n p center)
    | 0, k, tree, u, w, hlevel, code =>
        [RecursiveFrontierItem.castLevel hlevel tree u w code]
    | _depth + 1, _k, .leaf, _u, _w, _hlevel, _code => []
    | depth + 1, k, .node forest, u, w, hlevel, code =>
        recursiveProfileForestFrontier n p center depth k forest u w
          hlevel code

  /-- Ordered target-level descendants of a chronological recursive forest. -/
  def recursiveProfileForestFrontier
      (n p : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        k + (depth + 1) = p →
        RecursiveProfileForestCode n k center forest u w →
          List (RecursiveFrontierItem n p center)
    | _depth, _k, .nil, _u, _w, _hlevel, _code => []
    | depth, k, .cons child tail, u, w, hlevel, code =>
        recursiveProfileGapFrontier n p center depth (k + 1) child
            code.1 code.2.1 (by omega) code.2.2.2.1 ++
          recursiveProfileForestFrontier n p center depth k tail
            code.2.1 w hlevel code.2.2.2.2
end

mutual
  /-- Product mass of all literal pieces strictly above the requested
  frontier in one recursive gap.  A branch which dies before the frontier
  contributes its complete mass here. -/
  def recursiveProfileGapFrontierPrefixMass
      (n : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileGapCode n k center tree u w → ℝ≥0∞
    | 0, _k, _tree, _u, _w, _code => 1
    | _depth + 1, k, .leaf, u, w, code =>
        recursiveProfileGapCodeMass n k center .leaf u w code
    | depth + 1, k, .node forest, u, w, code =>
        recursiveProfileForestFrontierPrefixMass n center depth k forest u w
          code

  /-- Forest version of the shallow frontier-prefix mass. -/
  def recursiveProfileForestFrontierPrefixMass
      (n : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileForestCode n k center forest u w → ℝ≥0∞
    | _depth, k, .nil, u, w, code =>
        recursiveProfileForestCodeMass n k center .nil u w code
    | depth, k, .cons child tail, u, w, code =>
        stoppedWordMass code.2.2.1.1 *
          recursiveProfileGapFrontierPrefixMass n center depth (k + 1)
            child code.1 code.2.1 code.2.2.2.1 *
          recursiveProfileForestFrontierPrefixMass n center depth k tail
            code.2.1 w code.2.2.2.2
end

mutual
  /-- Cutting a recursive gap at a fixed later level preserves its mass
  exactly: shallow retained pieces multiply the target-level code masses. -/
  theorem recursiveProfileGapCodeMass_eq_frontier
      (n p : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (hlevel : k + depth = p)
        (code : RecursiveProfileGapCode n k center tree u w),
        recursiveProfileGapCodeMass n k center tree u w code =
          recursiveProfileGapFrontierPrefixMass n center depth k tree u w code *
            ((recursiveProfileGapFrontier n p center depth k tree u w hlevel
              code).map RecursiveFrontierItem.mass).prod
    | 0, k, tree, u, w, hlevel, code => by
        simp only [recursiveProfileGapFrontierPrefixMass,
          recursiveProfileGapFrontier, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one, one_mul]
        simp only [Nat.add_zero] at hlevel
        subst p
        rfl
    | _depth + 1, k, .leaf, u, w, _hlevel, code => by
        simp [recursiveProfileGapFrontierPrefixMass,
          recursiveProfileGapFrontier]
    | depth + 1, k, .node forest, u, w, hlevel, code =>
        recursiveProfileForestCodeMass_eq_frontier n p center depth k forest
          u w hlevel code

  /-- Forest version of the exact frontier mass factorization. -/
  theorem recursiveProfileForestCodeMass_eq_frontier
      (n p : ℕ) (center : Point) :
      ∀ (depth k : ℕ) (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (hlevel : k + (depth + 1) = p)
        (code : RecursiveProfileForestCode n k center forest u w),
        recursiveProfileForestCodeMass n k center forest u w code =
          recursiveProfileForestFrontierPrefixMass n center depth k forest u w
              code *
            ((recursiveProfileForestFrontier n p center depth k forest u w
              hlevel code).map RecursiveFrontierItem.mass).prod
    | _depth, k, .nil, u, w, _hlevel, code => by
        simp [recursiveProfileForestFrontierPrefixMass,
          recursiveProfileForestFrontier]
    | depth, k, .cons child tail, u, w, hlevel, code => by
        simp only [recursiveProfileForestCodeMass,
          recursiveProfileForestFrontierPrefixMass,
          recursiveProfileForestFrontier, List.map_append, List.prod_append]
        rw [recursiveProfileGapCodeMass_eq_frontier n p center depth (k + 1)
          child code.1 code.2.1 (by omega) code.2.2.2.1,
          recursiveProfileForestCodeMass_eq_frontier n p center depth k tail
            code.2.1 w hlevel code.2.2.2.2]
        ac_rfl
end

/-! ## Parent-major list normalization -/

private theorem splitLengths_getElem_eq_drop_take {α : Type*} :
    ∀ (sizes : List ℕ) (values : List α) (i : ℕ)
      (hi : i < sizes.length),
      (sizes.splitLengths values)[i]'(by simpa) =
        (values.drop (sizes.take i).sum).take sizes[i] := by
  intro sizes
  induction sizes with
  | nil => simp
  | cons head tail ih =>
      intro values i hi
      cases i with
      | zero => simp [List.splitLengths]
      | succ i =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          simp only [List.splitLengths_cons, List.getElem_cons_succ,
            List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
          rw [ih (values.drop head) i hi]
          rw [List.drop_drop]

/-- Concatenating the local offspring lists in parent order gives the
canonical global child list. -/
theorem flatten_parentMajor
    {a b : ℕ} (g : GapPattern a b) {α : Type*} (f : Fin b → α) :
    (List.ofFn fun i : Fin a =>
      List.ofFn fun j : Fin (gapMultiplicity g i) =>
        f (gapChildIndexEquiv g ⟨i, j⟩)).flatten = List.ofFn f := by
  let sizes := List.ofFn fun i : Fin a => gapMultiplicity g i
  let values := List.ofFn f
  let groups := sizes.splitLengths values
  have hsum : sizes.sum = b := by
    simp only [sizes, List.sum_ofFn, sum_gapMultiplicity]
  have hgroups : groups.flatten = values := by
    apply List.flatten_splitLengths
    simpa only [values, List.length_ofFn, hsum] using (le_refl b)
  calc
    _ = groups.flatten := by
      congr 1
      apply List.ext_getElem
      · simp [groups, sizes]
      · intro i hiLeft hiRight
        simp only [List.length_ofFn] at hiLeft
        have hiSizes : i < sizes.length := by
          simpa only [groups, List.length_splitLengths] using hiRight
        rw [splitLengths_getElem_eq_drop_take sizes values i hiSizes]
        apply List.ext_getElem
        · simp only [List.length_ofFn, List.length_take, List.length_drop,
            sizes, values, List.getElem_ofFn]
          have htake : (sizes.take (i + 1)).sum ≤ sizes.sum :=
            (List.take_sublist (i + 1) sizes).sum_le_sum (by omega)
          have htakeEq : (sizes.take i).sum + sizes[i] =
              (sizes.take (i + 1)).sum := by
            simpa only [List.sum_append, List.sum_singleton] using
              congrArg List.sum
                (List.take_concat_get' sizes i (by simpa [sizes] using hiLeft))
          rw [← htakeEq] at htake
          simp only [hsum, sizes, List.getElem_ofFn] at htake
          omega
        · intro j hjLeft hjRight
          rw [List.getElem_take, List.getElem_drop]
          simp only [values, List.getElem_ofFn, sizes]
          congr 1
          apply Fin.ext
          rw [gapChildIndexEquiv_val]
          congr 1
          have hprefList :
              List.ofFn (fun h : Fin i =>
                gapMultiplicity g (Fin.castLE hiLeft.le h)) =
                sizes.take i := by
            apply List.ext_getElem
            · simp [sizes, hiLeft.le]
            · intro h hhLeft hhRight
              simp [sizes]
          calc
            (∑ h : Fin i, gapMultiplicity g (Fin.castLE hiLeft.le h)) =
                (List.ofFn (fun h : Fin i =>
                  gapMultiplicity g (Fin.castLE hiLeft.le h))).sum := by
                    rw [List.sum_ofFn]
            _ = (sizes.take i).sum := congrArg List.sum hprefList
    _ = List.ofFn f := by simpa only [values] using hgroups

mutual
  /-- The same fixed-level frontier after erasing literal endpoints and codes. -/
  def profileRefinementTreeFrontier :
      ℕ → ProfileRefinementTree → List ProfileRefinementTree
    | 0, tree => [tree]
    | _depth + 1, .leaf => []
    | depth + 1, .node forest =>
        profileRefinementForestFrontier depth forest

  /-- Forest version of `profileRefinementTreeFrontier`. -/
  def profileRefinementForestFrontier :
      ℕ → ProfileRefinementForest → List ProfileRefinementTree
    | _depth, .nil => []
    | depth, .cons child tail =>
        profileRefinementTreeFrontier depth child ++
          profileRefinementForestFrontier depth tail
end

/-- Cutting a list-wrapped forest applies the tree frontier to each child
and concatenates the results in chronological order. -/
theorem profileRefinementForestFrontier_ofList :
    ∀ (depth : ℕ) (children : List ProfileRefinementTree),
      profileRefinementForestFrontier depth
          (ProfileRefinementForest.ofList children) =
        children.flatMap (profileRefinementTreeFrontier depth)
  | _depth, [] => rfl
  | depth, child :: tail => by
      simp only [ProfileRefinementForest.ofList,
        profileRefinementForestFrontier, List.flatMap_cons,
        profileRefinementForestFrontier_ofList depth tail]

private theorem flatMap_flatten {α β : Type*}
    (lists : List (List α)) (f : α → List β) :
    lists.flatten.flatMap f =
      (lists.map fun values => values.flatMap f).flatten := by
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  rfl

/-- Canonical root list after descending a prescribed number of edges in a
gap chain.  The proof argument only rules out descending past the chain. -/
def profileRefinementTreesAtDepth :
    ∀ {a : ℕ} (rest : List ℕ) (chain : GapChain (a :: rest))
      (depth : ℕ), depth ≤ rest.length → List ProfileRefinementTree
  | a, rest, chain, 0, _ =>
      List.ofFn fun i : Fin a => profileRefinementTrees a rest chain i
  | _a, [], _chain, _depth + 1, hdepth => by simp at hdepth
  | _a, b :: rest, chain, depth + 1, hdepth =>
      profileRefinementTreesAtDepth rest chain.2 depth (by simpa using hdepth)

/-- The structural fixed-depth frontier of the canonical root forest is the
canonical root forest at that later depth. -/
theorem flatMap_profileRefinementTreeFrontier_profileRefinementTrees :
    ∀ {a : ℕ} (rest : List ℕ) (chain : GapChain (a :: rest))
      (depth : ℕ) (hdepth : depth ≤ rest.length),
      (List.ofFn fun i : Fin a => profileRefinementTrees a rest chain i).flatMap
          (profileRefinementTreeFrontier depth) =
        profileRefinementTreesAtDepth rest chain depth hdepth
  | _a, rest, chain, 0, _hdepth => by
      simp only [profileRefinementTreesAtDepth]
      rw [show profileRefinementTreeFrontier 0 =
          fun tree : ProfileRefinementTree => [tree] by
            funext tree
            simp [profileRefinementTreeFrontier]]
      exact List.flatMap_singleton' _
  | _a, [], _chain, depth + 1, hdepth => by simp at hdepth
  | a, b :: rest, chain, depth + 1, hdepth => by
      let children : Fin b → ProfileRefinementTree := fun j =>
        profileRefinementTrees b rest chain.2 j
      calc
        (List.ofFn fun i : Fin a =>
            profileRefinementTrees a (b :: rest) chain i).flatMap
              (profileRefinementTreeFrontier (depth + 1)) =
            (List.ofFn fun i : Fin a =>
              (List.ofFn fun j : Fin (gapMultiplicity chain.1 i) =>
                children (gapChildIndexEquiv chain.1 ⟨i, j⟩)).flatMap
                  (profileRefinementTreeFrontier depth)).flatten := by
                    rw [List.flatMap_def]
                    congr 1
                    apply List.ext_getElem
                    · simp
                    · intro i hiLeft hiRight
                      simp only [List.getElem_map, List.getElem_ofFn,
                        profileRefinementTrees,
                        profileRefinementTreeFrontier]
                      exact profileRefinementForestFrontier_ofList _ _
        _ = ((List.ofFn fun i : Fin a =>
              List.ofFn fun j : Fin (gapMultiplicity chain.1 i) =>
                children (gapChildIndexEquiv chain.1 ⟨i, j⟩)).flatten).flatMap
                  (profileRefinementTreeFrontier depth) := by
                    rw [flatMap_flatten]
                    simp only [List.map_ofFn]
                    congr 1
        _ = (List.ofFn children).flatMap
              (profileRefinementTreeFrontier depth) := by
                rw [flatten_parentMajor]
        _ = profileRefinementTreesAtDepth rest chain.2 depth
              (by simpa using hdepth) := by
                exact flatMap_profileRefinementTreeFrontier_profileRefinementTrees
                  rest chain.2 depth (by simpa using hdepth)
        _ = profileRefinementTreesAtDepth (b :: rest) chain
              (depth + 1) hdepth := by rfl

mutual
  /-- Erasing a literal frontier leaves the structural tree frontier. -/
  theorem map_tree_recursiveProfileGapFrontier
    (n p : ℕ) (center : Point) :
    ∀ (depth k : ℕ) (tree : ProfileRefinementTree)
      (u : ProfileCycleMiddlePoint n k center)
      (w : ProfileCycleOuterPoint n k center)
      (hlevel : k + depth = p)
      (code : RecursiveProfileGapCode n k center tree u w),
      (recursiveProfileGapFrontier n p center depth k tree u w hlevel code).map
          RecursiveFrontierItem.tree =
        profileRefinementTreeFrontier depth tree
  | 0, k, _tree, _u, _w, hlevel, _code => by
      simp only [Nat.add_zero] at hlevel
      have : k = p := hlevel
      subst p
      simp only [recursiveProfileGapFrontier, List.map_cons, List.map_nil,
        profileRefinementTreeFrontier]
      rfl
  | _depth + 1, _k, .leaf, _u, _w, _hlevel, _code => rfl
  | depth + 1, k, .node forest, u, w, hlevel, code =>
      map_tree_recursiveProfileForestFrontier n p center depth k forest u w
        hlevel code

  /-- Forest version of `map_tree_recursiveProfileGapFrontier`. -/
  theorem map_tree_recursiveProfileForestFrontier
    (n p : ℕ) (center : Point) :
    ∀ (depth k : ℕ) (forest : ProfileRefinementForest)
      (u : ProfileCycleMiddlePoint n k center)
      (w : ProfileCycleOuterPoint n k center)
      (hlevel : k + (depth + 1) = p)
      (code : RecursiveProfileForestCode n k center forest u w),
      (recursiveProfileForestFrontier n p center depth k forest u w hlevel
          code).map RecursiveFrontierItem.tree =
        profileRefinementForestFrontier depth forest
  | _depth, _k, .nil, _u, _w, _hlevel, _code => rfl
  | depth, k, .cons child tail, u, w, hlevel, code => by
      simp only [recursiveProfileForestFrontier,
        profileRefinementForestFrontier, List.map_append]
      rw [map_tree_recursiveProfileGapFrontier,
        map_tree_recursiveProfileForestFrontier]
end

end


end Erdos1165.AsymmetricPaddedRecursiveFrontier
