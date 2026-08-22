/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialProfileWords
import ErdosProblems.Erdos1165.AnnularRadialChainLower
import ErdosProblems.Erdos1165.ProfileGapChain
import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.SplitLengths

/-!
# Exact contour enumeration for chronological radial words

This file supplies the finite combinatorial part of the chronological
radial-word argument.  A chain of weak compositions is rendered as the
depth-first contour of the associated ordered forest.  Cutting each rendered
parent immediately after its returns to the parent level recovers both the
child forest and the weak-composition multiplicities.  In particular, the
rendering is injective; no independence or branching-law premise is used.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialContourEnumeration

open AppendixFirstMoment PathInsertion ProfileGapChain
  AnnularIntegratedProfileKernel AnnularRadialLabelWord
  AnnularRadialProfileWords AnnularRadialChainLower
  TerminalNegativeBinomialWindow
  ExcursionTransition NegativeBinomial

noncomputable section

/-! ## Rendering weak-composition chains -/

/-- Depth-first contour forest.  An entry of `values` is the number of
parents at that level.  At the last level every parent makes the deterministic
return to the preceding level. -/
def contourForest : (base : ℕ) → (values : List ℕ) →
    GapChain values → List (List ℕ)
  | _, [], _ => []
  | base, [a], _ => List.replicate a [base, base - 1]
  | base, a :: b :: rest, chain =>
      let children := contourForest (base + 1) (b :: rest) chain.2
      let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
      let groups := sizes.splitLengths children
      groups.map fun group ↦ base :: group.flatten ++ [base - 1]

@[simp] theorem length_contourForest : ∀ (base : ℕ) (values : List ℕ)
    (chain : GapChain values),
    (contourForest base values chain).length = values.headD 0
  | _, [], _ => by simp [contourForest]
  | _, [_], _ => by simp [contourForest]
  | base, a :: b :: rest, chain => by
      simp [contourForest]

/-- The one-root contour word. -/
def contourWord (values : List ℕ) (chain : GapChain values) : List ℕ :=
  (contourForest 1 values chain).headD []

/-- Shape invariant needed by the inverse parser. -/
def ExcursionShape (base : ℕ) (path : List ℕ) : Prop :=
  ∃ middle : List ℕ,
    path = base :: middle ++ [base - 1] ∧
      ∀ x ∈ base :: middle, base ≤ x

private theorem all_ge_of_excursionShape {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) : ∀ x ∈ path, base - 1 ≤ x := by
  intro x hx
  obtain ⟨middle, rfl, hmiddle⟩ := h
  change x ∈ (base :: middle) ++ [base - 1] at hx
  rcases List.mem_append.mp hx with hleft | hright
  · exact (Nat.sub_le base 1).trans (hmiddle x hleft)
  · simp only [List.mem_singleton] at hright
    rw [hright]

private theorem excursionShape_renderParent
    {base : ℕ} (hbase : 0 < base) {children : List (List ℕ)}
    (hchildren : ∀ child ∈ children, ExcursionShape (base + 1) child) :
    ExcursionShape base (base :: children.flatten ++ [base - 1]) := by
  have hge : ∀ x ∈ children.flatten, base ≤ x := by
    intro x hx
    obtain ⟨child, hchild, hxchild⟩ := List.mem_flatten.mp hx
    exact all_ge_of_excursionShape (hchildren child hchild) x hxchild
  refine ⟨children.flatten, rfl, ?_⟩
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · exact hge x hx

theorem contourForest_excursionShape : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values) path,
      path ∈ contourForest base values chain → ExcursionShape base path
  | _, _, [], _, _, h => by simp [contourForest] at h
  | base, hbase, [a], _, path, hpath => by
      simp only [contourForest, List.mem_replicate] at hpath
      rcases hpath with ⟨_, rfl⟩
      refine ⟨[], by simp, by simp⟩
  | base, hbase, a :: b :: rest, chain, path, hpath => by
      simp only [contourForest, List.mem_map] at hpath
      obtain ⟨group, hgroup, rfl⟩ := hpath
      apply excursionShape_renderParent hbase
      intro child hchild
      apply contourForest_excursionShape (base + 1) (by omega)
        (b :: rest) chain.2 child
      have hflatten :
          ((List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)).splitLengths
            (contourForest (base + 1) (b :: rest) chain.2)).flatten =
              contourForest (base + 1) (b :: rest) chain.2 := by
        apply List.flatten_splitLengths
        rw [length_contourForest]
        simp only [List.headD_cons]
        rw [List.sum_ofFn, sum_gapMultiplicity]
      rw [← hflatten]
      exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩

/-! ## The inverse cut -/

/-- Cut a parent contour immediately after every return to `base`. -/
def contourChildren (base : ℕ) (path : List ℕ) : List (List ℕ) :=
  path.tail.dropLast.splitBy (fun x _ ↦ decide (x ≠ base))

private theorem isChain_cutRelation_of_shape
    {base : ℕ} {path : List ℕ}
    (h : ExcursionShape (base + 1) path) :
    path.IsChain (fun x _ ↦ decide (x ≠ base)) := by
  obtain ⟨middle, rfl, hmiddle⟩ := h
  have hnonbase : ∀ x ∈ (base + 1) :: middle, x ≠ base := by
    intro x hx hxeq
    have := hmiddle x hx
    omega
  have aux : ∀ pre : List ℕ,
      (∀ x ∈ pre, x ≠ base) →
      (pre ++ [base]).IsChain (fun x _ ↦ decide (x ≠ base)) := by
    intro pre hp
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [decide_eq_true_eq]
    have hiPre : i < pre.length := by
      simpa only [List.length_append, List.length_singleton, Nat.add_lt_add_iff_right]
        using hi
    rw [List.getElem_append_left hiPre]
    exact hp pre[i] (List.getElem_mem hiPre)
  simpa only [Nat.add_sub_cancel] using
    aux ((base + 1) :: middle) hnonbase

private theorem splitBy_flatten_excursionChildren
    {base : ℕ} {children : List (List ℕ)}
    (hchildren : ∀ child ∈ children, ExcursionShape (base + 1) child) :
    children.flatten.splitBy (fun x _ ↦ decide (x ≠ base)) = children := by
  apply List.splitBy_flatten
  · intro hnil
    exact (hchildren [] hnil).elim fun middle h ↦ by simp at h
  · intro child hchild
    exact isChain_cutRelation_of_shape (hchildren child hchild)
  · induction children with
    | nil => simp
    | cons child children ih =>
        rw [List.isChain_cons]
        constructor
        · intro next hnext
          have hc := hchildren child (by simp)
          have hnmem : next ∈ children := List.mem_of_mem_head? hnext
          have hn := hchildren next (by simp [hnmem])
          obtain ⟨cm, hcEq, _⟩ := hc
          obtain ⟨nm, hnEq, _⟩ := hn
          refine ⟨by simp [hcEq], by simp [hnEq], ?_⟩
          simp [hcEq]
        · apply ih
          intro c hc
          exact hchildren c (by simp [hc])

@[simp] theorem contourChildren_renderParent
    {base : ℕ} {children : List (List ℕ)}
    (hchildren : ∀ child ∈ children, ExcursionShape (base + 1) child) :
    contourChildren base (base :: children.flatten ++ [base - 1]) = children := by
  simpa [contourChildren] using
    (splitBy_flatten_excursionChildren hchildren)

/-- Applying the inverse cut to every rendered parent recovers the complete
next-level forest. -/
theorem flatten_map_contourChildren_contourForest :
    ∀ (base : ℕ), 0 < base → ∀ (a b : ℕ) (rest : List ℕ)
      (chain : GapChain (a :: b :: rest)),
      ((contourForest base (a :: b :: rest) chain).map
          (contourChildren base)).flatten =
        contourForest (base + 1) (b :: rest) chain.2 := by
  intro base hbase a b rest chain
  let children := contourForest (base + 1) (b :: rest) chain.2
  let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
  let groups := sizes.splitLengths children
  have hshape : ∀ child ∈ children, ExcursionShape (base + 1) child := by
    intro child hchild
    exact contourForest_excursionShape (base + 1) (by omega)
      (b :: rest) chain.2 child hchild
  have hgroupShape : ∀ group ∈ groups, ∀ child ∈ group,
      ExcursionShape (base + 1) child := by
    intro group hgroup child hchild
    apply hshape child
    have hflat : groups.flatten = children := by
      apply List.flatten_splitLengths
      dsimp only [sizes, children]
      rw [length_contourForest]
      simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
      exact le_rfl
    rw [← hflat]
    exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
  simp only [contourForest, children, sizes, groups, List.map_map,
    Function.comp_def]
  rw [List.map_congr_left (fun group hgroup ↦
    contourChildren_renderParent (hgroupShape group hgroup))]
  have hflat : groups.flatten = children := by
    apply List.flatten_splitLengths
    dsimp only [sizes, children]
    rw [length_contourForest]
    simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
    exact le_rfl
  simpa using hflat

/-- The number of parsed children of each rendered parent recovers the
weak-composition vector. -/
theorem map_length_contourChildren_contourForest :
    ∀ (base : ℕ), 0 < base → ∀ (a b : ℕ) (rest : List ℕ)
      (chain : GapChain (a :: b :: rest)),
      (contourForest base (a :: b :: rest) chain).map
          (fun path ↦ (contourChildren base path).length) =
        List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i) := by
  intro base hbase a b rest chain
  let children := contourForest (base + 1) (b :: rest) chain.2
  let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
  let groups := sizes.splitLengths children
  have hshape : ∀ child ∈ children, ExcursionShape (base + 1) child := by
    intro child hchild
    exact contourForest_excursionShape (base + 1) (by omega)
      (b :: rest) chain.2 child hchild
  have hgroupShape : ∀ group ∈ groups, ∀ child ∈ group,
      ExcursionShape (base + 1) child := by
    intro group hgroup child hchild
    apply hshape child
    have hflat : groups.flatten = children := by
      apply List.flatten_splitLengths
      dsimp only [sizes, children]
      rw [length_contourForest]
      simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
      exact le_rfl
    rw [← hflat]
    exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
  simp only [contourForest, children, sizes, groups, List.map_map,
    Function.comp_def]
  rw [List.map_congr_left (fun group hgroup ↦ congrArg List.length
    (contourChildren_renderParent (hgroupShape group hgroup)))]
  apply List.map_splitLengths_length
  dsimp only [sizes, children]
  rw [length_contourForest]
  simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
  exact le_rfl

private theorem gapPattern_ext_of_multiplicity_eq
    {a b : ℕ} {left right : GapPattern a b}
    (h : (∀ i, gapMultiplicity left i = gapMultiplicity right i)) :
    left = right := by
  apply Sym.ext
  rw [Multiset.ext]
  intro i
  exact h i

/-- The depth-first contour forest remembers the complete weak-composition
chain. -/
theorem contourForest_injective (base : ℕ) (hbase : 0 < base) :
    ∀ (values : List ℕ), Function.Injective (contourForest base values)
  | [] => by
      intro left right _
      cases left
      cases right
      rfl
  | [_] => by
      intro left right _
      cases left
      cases right
      rfl
  | a :: b :: rest => by
      intro left right hrender
      have hsizes : List.ofFn (fun i : Fin a ↦ gapMultiplicity left.1 i) =
          List.ofFn (fun i : Fin a ↦ gapMultiplicity right.1 i) := by
        rw [← map_length_contourChildren_contourForest base hbase a b rest left,
          ← map_length_contourChildren_contourForest base hbase a b rest right,
          hrender]
      have hpattern : left.1 = right.1 := by
        apply gapPattern_ext_of_multiplicity_eq
        intro i
        exact congrFun (List.ofFn_injective hsizes) i
      have htailRender :
          contourForest (base + 1) (b :: rest) left.2 =
            contourForest (base + 1) (b :: rest) right.2 := by
        rw [← flatten_map_contourChildren_contourForest base hbase a b rest left,
          ← flatten_map_contourChildren_contourForest base hbase a b rest right,
          hrender]
      have htail : left.2 = right.2 :=
        contourForest_injective (base + 1) (by omega) (b :: rest) htailRender
      exact Prod.ext hpattern htail

/-! ## Edge counts of a rendered contour -/

/-- Number of directed occurrences `source → target` in a natural-number
label list. -/
def natStepCount (source target : ℕ) : List ℕ → ℕ
  | left :: right :: tail =>
      (if left = source ∧ right = target then 1 else 0) +
        natStepCount source target (right :: tail)
  | _ => 0

private def boundaryStepCount (source target : ℕ) :
    Option ℕ → Option ℕ → ℕ
  | some left, some right => if left = source ∧ right = target then 1 else 0
  | _, _ => 0

private theorem natStepCount_append (source target : ℕ) :
    ∀ (left right : List ℕ),
      natStepCount source target (left ++ right) =
        natStepCount source target left +
          boundaryStepCount source target left.getLast? right.head? +
            natStepCount source target right
  | [], right => by simp [natStepCount, boundaryStepCount]
  | [x], [] => by simp [natStepCount, boundaryStepCount]
  | [x], y :: ys => by simp [natStepCount, boundaryStepCount]
  | x :: y :: xs, right => by
      simp only [List.cons_append, natStepCount]
      change (if x = source ∧ y = target then 1 else 0) +
          natStepCount source target ((y :: xs) ++ right) = _
      rw [natStepCount_append source target (y :: xs) right]
      simp only [List.getLast?_cons, Option.getD_some, Nat.add_assoc]

private theorem head?_eq_of_excursionShape {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) : path.head? = some base := by
  obtain ⟨middle, rfl, _⟩ := h
  simp

private theorem getLast?_eq_of_excursionShape {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) : path.getLast? = some (base - 1) := by
  obtain ⟨middle, rfl, _⟩ := h
  exact List.getLast?_eq_some_iff.mpr ⟨base :: middle, rfl⟩

private theorem natStepCount_flatten_excursions
    (source target base : ℕ) : ∀ (children : List (List ℕ)),
    (∀ child ∈ children, ExcursionShape (base + 1) child) →
    natStepCount source target children.flatten =
      (children.map (natStepCount source target)).sum +
        children.tail.length *
          (if source = base ∧ target = base + 1 then 1 else 0)
  | [], _ => by simp [natStepCount]
  | [child], hchildren => by simp [natStepCount]
  | child :: next :: rest, hchildren => by
      rw [List.flatten_cons,
        natStepCount_append source target child (next :: rest).flatten]
      have hc := hchildren child (by simp)
      have hn := hchildren next (by simp)
      have hrest : ∀ c ∈ next :: rest, ExcursionShape (base + 1) c := by
        intro c hc
        exact hchildren c (by simp [hc])
      rw [getLast?_eq_of_excursionShape hc]
      have hhead : (next :: rest).flatten.head? = some (base + 1) := by
        simp only [List.flatten_cons]
        rw [List.head?_append_of_ne_nil]
        · exact head?_eq_of_excursionShape hn
        · intro hnil
          simpa [hnil] using head?_eq_of_excursionShape hn
      rw [hhead]
      rw [natStepCount_flatten_excursions source target base (next :: rest) hrest]
      simp only [boundaryStepCount, List.tail_cons, List.length_cons,
        List.map_cons, List.sum_cons, Nat.add_sub_cancel]
      simp only [Nat.add_comm base 1]
      split_ifs <;> omega

private theorem head?_flatten_excursions
    {base : ℕ} : ∀ {children : List (List ℕ)}, children ≠ [] →
    (∀ child ∈ children, ExcursionShape (base + 1) child) →
    children.flatten.head? = some (base + 1)
  | [], hne, _ => (hne rfl).elim
  | child :: rest, _, hchildren => by
      rw [List.flatten_cons, List.head?_append_of_ne_nil]
      · exact head?_eq_of_excursionShape (hchildren child (by simp))
      · intro hnil
        simpa [hnil] using
          head?_eq_of_excursionShape (hchildren child (by simp))

private theorem getLast?_flatten_excursions
    {base : ℕ} : ∀ {children : List (List ℕ)}, children ≠ [] →
    (∀ child ∈ children, ExcursionShape (base + 1) child) →
    children.flatten.getLast? = some base
  | [], hne, _ => (hne rfl).elim
  | [child], _, hchildren => by
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
        Nat.add_sub_cancel] using
          getLast?_eq_of_excursionShape (hchildren child (by simp))
  | child :: next :: rest, _, hchildren => by
      rw [List.flatten_cons, List.getLast?_append]
      have htail := getLast?_flatten_excursions (base := base)
        (children := next :: rest) (by simp)
        (fun c hc ↦ hchildren c (by simp [hc]))
      rw [htail]
      simp

private theorem natStepCount_renderParent
    (source target base : ℕ) (children : List (List ℕ))
    (hchildren : ∀ child ∈ children, ExcursionShape (base + 1) child) :
    natStepCount source target (base :: children.flatten ++ [base - 1]) =
      (children.map (natStepCount source target)).sum +
        children.length *
          (if source = base ∧ target = base + 1 then 1 else 0) +
        (if source = base ∧ target = base - 1 then 1 else 0) := by
  classical
  cases children with
  | nil => simp [natStepCount, eq_comm]
  | cons child rest =>
      have hc := hchildren child (by simp)
      have hflatNe : (child :: rest).flatten ≠ [] := by
        intro hnil
        have : child = [] := by
          have := congrArg List.length hnil
          simp only [List.flatten_cons, List.length_append, List.length_nil,
            Nat.add_eq_zero] at this
          exact List.eq_nil_of_length_eq_zero this.1
        simpa [this] using head?_eq_of_excursionShape hc
      rw [show base :: (child :: rest).flatten ++ [base - 1] =
          [base] ++ (child :: rest).flatten ++ [base - 1] by rfl,
        natStepCount_append source target
          ([base] ++ (child :: rest).flatten) [base - 1],
        natStepCount_append source target [base] (child :: rest).flatten]
      have hhead : (child :: rest).flatten.head? = some (base + 1) := by
        exact head?_flatten_excursions (by simp) hchildren
      have hlast : (child :: rest).flatten.getLast? = some base :=
        getLast?_flatten_excursions (by simp) hchildren
      have happLast : ([base] ++ (child :: rest).flatten).getLast? = some base := by
        rw [List.getLast?_append]
        rw [hlast]
        simp
      rw [hhead, happLast]
      rw [natStepCount_flatten_excursions source target base (child :: rest)
        hchildren]
      simp only [natStepCount, List.length_cons, List.tail_cons,
        List.getLast?_singleton, List.head?_singleton]
      by_cases hup : source = base ∧ target = base + 1
      · by_cases hdown : source = base ∧ target = base - 1
        · simp [boundaryStepCount, hup, hdown, eq_comm]
          omega
        · simp [boundaryStepCount, hup, hdown, eq_comm]
          omega
      · by_cases hdown : source = base ∧ target = base - 1
        · have hne : base + 1 ≠ base - 1 := by omega
          simp [boundaryStepCount, hup, hdown, eq_comm, hne]
        · simp [boundaryStepCount, hup, hdown, eq_comm]

private theorem natStepCount_eq_zero_of_source_not_mem_dropLast
    {source target : ℕ} : ∀ {path : List ℕ},
    source ∉ path.dropLast → natStepCount source target path = 0
  | [], _ => rfl
  | [_], _ => rfl
  | left :: right :: tail, hsource => by
      rw [natStepCount]
      have hleft : left ≠ source := by
        intro heq
        apply hsource
        simp [heq]
      rw [if_neg (fun h ↦ hleft h.1)]
      simp only [Nat.zero_add]
      apply natStepCount_eq_zero_of_source_not_mem_dropLast
      intro hmem
      apply hsource
      rw [List.dropLast_cons_of_ne_nil (x := left) (l := right :: tail) (by simp)]
      exact List.mem_cons_of_mem left hmem

private theorem natStepCount_parentLowerUp_eq_zero
    {base : ℕ} {path : List ℕ} (h : ExcursionShape (base + 1) path) :
    natStepCount base (base + 1) path = 0 := by
  apply natStepCount_eq_zero_of_source_not_mem_dropLast
  obtain ⟨middle, rfl, hmiddle⟩ := h
  intro hmem
  simp only [List.dropLast_concat, List.mem_cons] at hmem
  rcases hmem with hbad | hbad
  · omega
  · have := hmiddle base (by simp [hbad])
    omega

private theorem sum_map_groupFormula
    (f : List ℕ → ℕ) (coefficient : ℕ) :
    ∀ groups : List (List (List ℕ)),
      (groups.map (fun group ↦ (group.map f).sum +
        group.length * coefficient)).sum =
      (groups.flatten.map f).sum + groups.flatten.length * coefficient
  | [] => by simp
  | group :: groups => by
      rw [List.map_cons, List.sum_cons, sum_map_groupFormula f coefficient]
      simp only [List.flatten_cons, List.map_append, List.sum_append,
        List.length_append]
      ring

/-- Total number of upward edges from level `base + offset` to the next
level in a rendered forest.  It is exactly the corresponding next entry of
the prescribed count vector. -/
theorem contourForest_upcrossingCount : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values) (offset : ℕ),
      ((contourForest base values chain).map
        (natStepCount (base + offset) (base + offset + 1))).sum =
      (values.drop (offset + 1)).headD 0
  | _, _, [], _, offset => by simp [contourForest]
  | base, hbase, [a], _, offset => by
      simp only [contourForest, List.map_replicate, List.sum_replicate]
      have hzero : natStepCount (base + offset) (base + offset + 1)
          [base, base - 1] = 0 := by
        simp [natStepCount]
        omega
      rw [hzero]
      simp
  | base, hbase, a :: b :: rest, chain, offset => by
      let children := contourForest (base + 1) (b :: rest) chain.2
      let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
      let groups := sizes.splitLengths children
      have hshape : ∀ child ∈ children, ExcursionShape (base + 1) child := by
        intro child hchild
        exact contourForest_excursionShape (base + 1) (by omega)
          (b :: rest) chain.2 child hchild
      have hflat : groups.flatten = children := by
        apply List.flatten_splitLengths
        dsimp only [sizes, children]
        rw [length_contourForest]
        simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
        exact le_rfl
      have hgroupShape : ∀ group ∈ groups, ∀ child ∈ group,
          ExcursionShape (base + 1) child := by
        intro group hgroup child hchild
        apply hshape child
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
      simp only [contourForest, children, sizes, groups, List.map_map,
        Function.comp_def]
      rw [List.map_congr_left (fun group hgroup ↦
        natStepCount_renderParent (base + offset) (base + offset + 1)
          base group (hgroupShape group hgroup))]
      simp only [if_neg (by omega : ¬(base + offset = base ∧
        base + offset + 1 = base - 1)), Nat.add_zero]
      rw [sum_map_groupFormula
        (natStepCount (base + offset) (base + offset + 1))
        (if base + offset = base ∧ base + offset + 1 = base + 1 then 1 else 0)]
      rw [hflat]
      change (children.map
          (natStepCount (base + offset) (base + offset + 1))).sum +
          children.length *
            (if base + offset = base ∧ base + offset + 1 = base + 1
              then 1 else 0) = _
      rw [length_contourForest]
      simp only [List.headD_cons]
      cases offset with
      | zero =>
          have hchildZero : (children.map (natStepCount base (base + 1))).sum = 0 := by
            apply List.sum_eq_zero
            intro count hcount
            obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcount
            exact natStepCount_parentLowerUp_eq_zero (hshape child hchild)
          simpa [hchildZero]
      | succ offset =>
          have ih := contourForest_upcrossingCount (base + 1) (by omega)
            (b :: rest) chain.2 offset
          have hsource : base + (offset + 1) = base + 1 + offset := by omega
          have htarget : base + (offset + 1) + 1 = base + 1 + offset + 1 := by omega
          rw [hsource]
          change ((contourForest (base + 1) (b :: rest) chain.2).map
              (natStepCount (base + 1 + offset) (base + 1 + offset + 1))).sum +
              b * (if base + 1 + offset = base ∧
                base + 1 + offset + 1 = base + 1 then 1 else 0) = _
          rw [ih]
          have hne : base + 1 + offset ≠ base := by omega
          simp [hne]

private theorem natStepCount_parentDown_eq_zero
    {base : ℕ} {path : List ℕ} (h : ExcursionShape (base + 1) path) :
    natStepCount base (base - 1) path = 0 := by
  apply natStepCount_eq_zero_of_source_not_mem_dropLast
  obtain ⟨middle, rfl, hmiddle⟩ := h
  intro hmem
  simp only [List.dropLast_concat] at hmem
  have := hmiddle base hmem
  omega

/-- Total number of downward edges from `base + offset` to the preceding
level in a rendered forest.  It is the count at that source level. -/
theorem contourForest_downcrossingCount : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values) (offset : ℕ),
      ((contourForest base values chain).map
        (natStepCount (base + offset) (base + offset - 1))).sum =
      (values.drop offset).headD 0
  | _, _, [], _, offset => by simp [contourForest]
  | base, hbase, [a], _, offset => by
      simp only [contourForest, List.map_replicate, List.sum_replicate]
      cases offset with
      | zero =>
          simp only [Nat.add_zero]
          have hone : natStepCount base (base - 1) [base, base - 1] = 1 := by
            simp [natStepCount]
          rw [hone]
          simp [nsmul_eq_mul]
      | succ offset =>
          have hzero : natStepCount (base + (offset + 1))
              (base + (offset + 1) - 1) [base, base - 1] = 0 := by
            simp [natStepCount]
          rw [hzero]
          simp
  | base, hbase, a :: b :: rest, chain, offset => by
      let children := contourForest (base + 1) (b :: rest) chain.2
      let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
      let groups := sizes.splitLengths children
      have hshape : ∀ child ∈ children, ExcursionShape (base + 1) child := by
        intro child hchild
        exact contourForest_excursionShape (base + 1) (by omega)
          (b :: rest) chain.2 child hchild
      have hflat : groups.flatten = children := by
        apply List.flatten_splitLengths
        dsimp only [sizes, children]
        rw [length_contourForest]
        simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
        exact le_rfl
      have hgroupShape : ∀ group ∈ groups, ∀ child ∈ group,
          ExcursionShape (base + 1) child := by
        intro group hgroup child hchild
        apply hshape child
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
      simp only [contourForest, children, sizes, groups, List.map_map,
        Function.comp_def]
      rw [List.map_congr_left (fun group hgroup ↦
        natStepCount_renderParent (base + offset) (base + offset - 1)
          base group (hgroupShape group hgroup))]
      have hup : ¬(base + offset = base ∧
          base + offset - 1 = base + 1) := by omega
      simp only [if_neg hup, Nat.mul_zero, Nat.add_zero]
      cases offset with
      | zero =>
          simp only [Nat.add_zero]
          have hchildrenZero : (children.map
              (natStepCount base (base - 1))).sum = 0 := by
            apply List.sum_eq_zero
            intro count hcount
            obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcount
            exact natStepCount_parentDown_eq_zero (hshape child hchild)
          have hgroupsLen : groups.length = a := by simp [groups, sizes]
          have hgroupSum : (groups.map (fun group ↦
              (group.map (natStepCount base (base - 1))).sum)).sum =
              (children.map (natStepCount base (base - 1))).sum := by
            have h := sum_map_groupFormula
              (natStepCount base (base - 1)) 0 groups
            simp only [Nat.mul_zero, Nat.add_zero] at h
            simpa [hflat] using h
          rw [List.sum_map_add, hgroupSum, hchildrenZero]
          simp [hgroupsLen, nsmul_eq_mul]
      | succ offset =>
          have hdown : ¬(base + (offset + 1) = base ∧
              base + (offset + 1) - 1 = base - 1) := by omega
          simp only [if_neg hdown, Nat.add_zero]
          have hgroupSum : (groups.map (fun group ↦
              (group.map (natStepCount (base + (offset + 1))
                (base + (offset + 1) - 1))).sum)).sum =
              (children.map (natStepCount (base + (offset + 1))
                (base + (offset + 1) - 1))).sum := by
            have h := sum_map_groupFormula
              (natStepCount (base + (offset + 1))
                (base + (offset + 1) - 1)) 0 groups
            simp only [Nat.mul_zero, Nat.add_zero] at h
            simpa [hflat] using h
          rw [hgroupSum]
          rw [show children = contourForest (base + 1) (b :: rest) chain.2 by rfl]
          have ih := contourForest_downcrossingCount (base + 1) (by omega)
            (b :: rest) chain.2 offset
          rw [List.drop_succ_cons]
          rw [show base + (offset + 1) - 1 = base + offset by omega]
          rw [show base + 1 + offset = base + (offset + 1) by omega] at ih
          rw [show base + (offset + 1) - 1 = base + offset by omega] at ih
          exact ih

/-! ## Length, adjacency, and range -/

private theorem sum_length_eq_sum_pred_add_length
    {paths : List (List ℕ)} (hne : ∀ path ∈ paths, path ≠ []) :
    (paths.map List.length).sum =
      (paths.map (fun path ↦ path.length - 1)).sum + paths.length := by
  induction paths with
  | nil => simp
  | cons path paths ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hp : path.length - 1 + 1 = path.length := by
        apply Nat.sub_add_cancel
        exact List.length_pos_iff.mpr (hne path (by simp))
      rw [ih (fun q hq ↦ hne q (by simp [hq]))]
      omega

private theorem renderParent_transitionLength
    (base : ℕ) (children : List (List ℕ)) :
    (base :: children.flatten ++ [base - 1]).length - 1 =
      (children.map List.length).sum + 1 := by
  simp [List.length_flatten]

theorem contourForest_transitionLength : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values),
      ((contourForest base values chain).map
        (fun path ↦ path.length - 1)).sum =
      2 * values.sum - values.headD 0
  | _, _, [], _ => by simp [contourForest]
  | base, hbase, [a], _ => by
      simp only [contourForest, List.map_replicate, List.sum_replicate,
        List.length_cons, List.length_nil, Nat.add_zero, List.headD_cons,
        List.sum_cons, List.sum_nil, nsmul_eq_mul, Nat.cast_id]
      norm_num
      omega
  | base, hbase, a :: b :: rest, chain => by
      let children := contourForest (base + 1) (b :: rest) chain.2
      let sizes := List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)
      let groups := sizes.splitLengths children
      have hflat : groups.flatten = children := by
        apply List.flatten_splitLengths
        dsimp only [sizes, children]
        rw [length_contourForest]
        simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
        exact le_rfl
      have hchildrenShape : ∀ child ∈ children,
          ExcursionShape (base + 1) child := by
        intro child hchild
        exact contourForest_excursionShape (base + 1) (by omega)
          (b :: rest) chain.2 child hchild
      have hchildrenNe : ∀ child ∈ children, child ≠ [] := by
        intro child hchild hnil
        obtain ⟨middle, hEq, _⟩ := hchildrenShape child hchild
        simp [hnil] at hEq
      have ih := contourForest_transitionLength (base + 1) (by omega)
        (b :: rest) chain.2
      simp only [contourForest, children, sizes, groups, List.map_map,
        Function.comp_def]
      rw [List.map_congr_left (fun group _ ↦
        renderParent_transitionLength base group)]
      have hgroupSum :
          (groups.map (fun group ↦ (group.map List.length).sum + 1)).sum =
            (children.map List.length).sum + groups.length := by
        have aux : ∀ gs : List (List (List ℕ)),
            (gs.map (fun group ↦ (group.map List.length).sum + 1)).sum =
              (gs.flatten.map List.length).sum + gs.length := by
          intro gs
          induction gs with
          | nil => simp
          | cons group gs ihg =>
              simp only [List.map_cons, List.sum_cons, List.length_cons,
                List.flatten_cons, List.map_append, List.sum_append]
              rw [ihg]
              omega
        rw [aux, hflat]
      rw [hgroupSum]
      have hgroupsLen : groups.length = a := by
        simp [groups, sizes]
      rw [hgroupsLen]
      dsimp only [children]
      rw [sum_length_eq_sum_pred_add_length hchildrenNe, ih,
        length_contourForest]
      simp only [List.headD_cons, List.sum_cons]
      omega

private theorem excursionShape_ne_nil {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) : path ≠ [] := by
  obtain ⟨middle, rfl, _⟩ := h
  simp

private theorem excursionShape_head {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) : path.head (excursionShape_ne_nil h) = base := by
  obtain ⟨middle, rfl, _⟩ := h
  rfl

private theorem excursionShape_getLast {base : ℕ} {path : List ℕ}
    (h : ExcursionShape base path) :
    path.getLast (excursionShape_ne_nil h) = base - 1 := by
  rw [← Option.some_inj, ← List.getLast?_eq_getLast]
  exact getLast?_eq_of_excursionShape h

private theorem isChain_flatten_excursions
    {base : ℕ} {children : List (List ℕ)}
    (hshape : ∀ child ∈ children, ExcursionShape (base + 1) child)
    (hchain : ∀ child ∈ children,
      child.IsChain (fun x y ↦ Nat.dist x y = 1)) :
    children.flatten.IsChain (fun x y ↦ Nat.dist x y = 1) := by
  induction children with
  | nil => simp
  | cons child children ih =>
      rw [List.flatten_cons, List.isChain_append]
      refine ⟨hchain child (by simp),
        ih (fun c hc ↦ hshape c (by simp [hc]))
          (fun c hc ↦ hchain c (by simp [hc])), ?_⟩
      intro x hx y hy
      have hc := hshape child (by simp)
      have hxEq : x = base := by
        have hlastOpt := getLast?_eq_of_excursionShape hc
        simp only [Nat.add_sub_cancel] at hlastOpt
        rw [hlastOpt] at hx
        exact Option.some.inj hx.symm
      have hchildrenNe : children ≠ [] := by
        intro hnil
        simp [hnil] at hy
      let first := children.head hchildrenNe
      have hfirstMem : first ∈ children := List.head_mem hchildrenNe
      have hfirstShape := hshape first (by simp [hfirstMem])
      have hyEq : y = base + 1 := by
        have hheadFlat : children.flatten.head? = some (base + 1) :=
          head?_flatten_excursions hchildrenNe
            (fun c hc ↦ hshape c (by simp [hc]))
        have : y ∈ children.flatten.head? := hy
        rw [hheadFlat] at this
        exact Option.some.inj this.symm
      subst x
      subst y
      simp [Nat.dist]

private theorem isChain_renderParent
    {base : ℕ} {children : List (List ℕ)}
    (hbase : 0 < base)
    (hshape : ∀ child ∈ children, ExcursionShape (base + 1) child)
    (hchain : ∀ child ∈ children,
      child.IsChain (fun x y ↦ Nat.dist x y = 1)) :
    (base :: children.flatten ++ [base - 1]).IsChain
      (fun x y ↦ Nat.dist x y = 1) := by
  cases children with
  | nil =>
      change [base, base - 1].IsChain (fun x y ↦ Nat.dist x y = 1)
      rw [List.isChain_pair]
      simp [Nat.dist]
      omega
  | cons child rest =>
      have hflatChain := isChain_flatten_excursions hshape hchain
      rw [show base :: (child :: rest).flatten ++ [base - 1] =
          [base] ++ (child :: rest).flatten ++ [base - 1] by rfl,
        List.isChain_append]
      refine ⟨?_, by simp, ?_⟩
      · rw [List.isChain_append]
        refine ⟨by simp, hflatChain, ?_⟩
        intro x hx y hy
        simp only [List.getLast?_singleton, Option.mem_def] at hx
        have hxEq : x = base := Option.some.inj hx.symm
        subst x
        have hhead := head?_flatten_excursions (base := base) (by simp) hshape
        rw [hhead] at hy
        simp only [Option.mem_def] at hy
        have hyEq : y = base + 1 := Option.some.inj hy.symm
        subst y
        simp [Nat.dist]
      · intro x hx y hy
        have hlast := getLast?_flatten_excursions (base := base) (by simp) hshape
        rw [List.getLast?_append, hlast] at hx
        simp only [Option.some_or, Option.mem_def] at hx
        have hxEq : x = base := Option.some.inj hx.symm
        subst x
        simp only [List.head?_singleton, Option.mem_def] at hy
        have hyEq : y = base - 1 := Option.some.inj hy.symm
        subst y
        simp [Nat.dist]
        omega

theorem contourForest_adjacent : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values) path,
      path ∈ contourForest base values chain →
      path.IsChain (fun x y ↦ Nat.dist x y = 1)
  | _, _, [], _, _, h => by simp [contourForest] at h
  | base, hbase, [a], _, path, hpath => by
      simp only [contourForest, List.mem_replicate] at hpath
      rcases hpath with ⟨_, rfl⟩
      rw [List.isChain_pair]
      simp [Nat.dist]
      omega
  | base, hbase, a :: b :: rest, chain, path, hpath => by
      simp only [contourForest, List.mem_map] at hpath
      obtain ⟨group, hgroup, rfl⟩ := hpath
      apply isChain_renderParent hbase
      · intro child hchild
        apply contourForest_excursionShape (base + 1) (by omega)
          (b :: rest) chain.2 child
        have hflat :
            ((List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)).splitLengths
              (contourForest (base + 1) (b :: rest) chain.2)).flatten =
                contourForest (base + 1) (b :: rest) chain.2 := by
          apply List.flatten_splitLengths
          rw [length_contourForest]
          simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
          exact le_rfl
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
      · intro child hchild
        apply contourForest_adjacent (base + 1) (by omega)
          (b :: rest) chain.2 child
        have hflat :
            ((List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)).splitLengths
              (contourForest (base + 1) (b :: rest) chain.2)).flatten =
                contourForest (base + 1) (b :: rest) chain.2 := by
          apply List.flatten_splitLengths
          rw [length_contourForest]
          simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
          exact le_rfl
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩

theorem contourForest_lt_base_add_length : ∀ (base : ℕ), 0 < base →
    ∀ (values : List ℕ) (chain : GapChain values) path,
      path ∈ contourForest base values chain →
      ∀ x ∈ path, x < base + values.length
  | _, _, [], _, _, h => by simp [contourForest] at h
  | base, hbase, [a], _, path, hpath => by
      simp only [contourForest, List.mem_replicate] at hpath
      rcases hpath with ⟨_, rfl⟩
      intro x hx
      change x ∈ [base, base - 1] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · subst x
        simp only [List.length_cons, List.length_nil, Nat.add_zero]
        omega
      · subst x
        simp only [List.length_cons, List.length_nil, Nat.add_zero]
        omega
  | base, hbase, a :: b :: rest, chain, path, hpath => by
      simp only [contourForest, List.mem_map] at hpath
      obtain ⟨group, hgroup, rfl⟩ := hpath
      intro x hx
      change x ∈ (base :: group.flatten) ++ [base - 1] at hx
      rcases List.mem_append.mp hx with hleft | hlast
      rw [List.mem_cons] at hleft
      rcases hleft with rfl | hx
      · simp
      · obtain ⟨child, hchild, hxchild⟩ := List.mem_flatten.mp hx
        have hflat :
            ((List.ofFn (fun i : Fin a ↦ gapMultiplicity chain.1 i)).splitLengths
              (contourForest (base + 1) (b :: rest) chain.2)).flatten =
                contourForest (base + 1) (b :: rest) chain.2 := by
          apply List.flatten_splitLengths
          rw [length_contourForest]
          simp only [List.headD_cons, List.sum_ofFn, sum_gapMultiplicity]
          exact le_rfl
        have hchildGlobal : child ∈
            contourForest (base + 1) (b :: rest) chain.2 := by
          rw [← hflat]
          exact List.mem_flatten.mpr ⟨group, hgroup, hchild⟩
        have := contourForest_lt_base_add_length (base + 1) (by omega)
          (b :: rest) chain.2 child hchildGlobal x hxchild
        simp only [List.length_cons] at this ⊢
        omega
      · simp only [List.mem_singleton] at hlast
        subst x
        simp only [List.length_cons]
        omega

end

end Erdos1165.AnnularRadialContourEnumeration
