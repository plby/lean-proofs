/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialContourMass

/-!
# Converse contour enumeration for chronological radial words

Every positive nearest-neighbour excursion is the depth-first contour of the
ordered forest obtained by cutting at successive returns to each level.  This
module supplies the converse to the injective contour construction and uses it
to identify the ideal fixed-profile word sum.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialContourSurjection

open AppendixFirstMoment PathInsertion ProfileGapChain
  AnnularIntegratedProfileKernel AnnularRadialLabelWord
  AnnularRadialProfileWords AnnularRadialChainLower
  AnnularRadialReferenceEdge AnnularRadialContourEnumeration
  AnnularRadialContourMass AnnularIdealReferenceCounts
  TerminalNegativeBinomialWindow ExcursionTransition NegativeBinomial ThickPoint

noncomputable section

/-! ## Weak compositions from a vector of child counts -/

private noncomputable def gapPatternOfMultiplicitiesEq
    {a b : ℕ} (f : Fin a → ℕ) (h : ∑ i, f i = b) : GapPattern a b :=
  Sym.mk (∑ i : Fin a, f i • ({i} : Multiset (Fin a))) (by simp [h])

@[simp] private theorem gapMultiplicity_gapPatternOfMultiplicitiesEq
    {a b : ℕ} (f : Fin a → ℕ) (h : ∑ i, f i = b) (i : Fin a) :
    gapMultiplicity (gapPatternOfMultiplicitiesEq f h) i = f i := by
  simp only [gapMultiplicity, gapPatternOfMultiplicitiesEq, Sym.coe_mk]
  rw [Multiset.count_sum']
  simp only [Multiset.count_nsmul, Multiset.count_singleton]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [if_neg (Ne.symm hji)]
  · simp

private theorem splitLengths_flatten_by_lengths {A : Type*} :
    ∀ groups : List (List A),
      (groups.map List.length).splitLengths groups.flatten = groups
  | [] => by simp
  | group :: groups => by
      simp only [List.map_cons, List.flatten_cons, List.splitLengths_cons]
      rw [List.take_append_length, List.drop_append_length]
      rw [splitLengths_flatten_by_lengths groups]

/-! ## Cutting arbitrary excursions -/

private def IsContourExcursion (base : ℕ) (path : List ℕ) : Prop :=
  ExcursionShape base path ∧
    path.IsChain (fun x y ↦ Nat.dist x y = 1)

private theorem contourChildren_flatten {base : ℕ} {path : List ℕ}
    (_hshape : ExcursionShape base path) :
    (contourChildren base path).flatten = path.tail.dropLast := by
  simp [contourChildren]

private theorem render_contourChildren {base : ℕ} {path : List ℕ}
    (hshape : ExcursionShape base path) :
    base :: (contourChildren base path).flatten ++ [base - 1] = path := by
  obtain ⟨middle, rfl, _⟩ := hshape
  simp [contourChildren]

private theorem source_property_of_isChain
    {A : Type*} {P : A → Prop} : ∀ {path : List A},
    path.IsChain (fun x _ ↦ P x) → ∀ x ∈ path.dropLast, P x
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | left :: right :: tail, hchain, x, hx => by
      rw [List.dropLast_cons_of_ne_nil (by simp)] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hchain.rel
      · exact source_property_of_isChain hchain.tail x hx

private theorem parsedChildren_head_eq
    {base : ℕ} {groups : List (List ℕ)}
    (hnonempty : [] ∉ groups)
    (hadj : groups.IsChain (fun left right ↦
      ∀ x ∈ left.getLast?, ∀ y ∈ right.head?, Nat.dist x y = 1))
    (hcut : groups.IsChain (fun left right ↦
      ∃ (hl : left ≠ []) (_hr : right ≠ []),
        decide (left.getLast hl ≠ base) = false))
    (hfirst : ∀ first ∈ groups.head?, first.head? = some (base + 1))
    (hge : ∀ x ∈ groups.flatten, base ≤ x) :
    ∀ child ∈ groups, child.head? = some (base + 1) := by
  induction groups with
  | nil => simp
  | cons first rest ih =>
      intro child hchild
      rcases List.mem_cons.mp hchild with hchildEq | hchild
      · subst child
        exact hfirst first (by simp)
      · have hrestNe : rest ≠ [] := List.ne_nil_of_mem hchild
        obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil hrestNe
        have hnextNe : next ≠ [] := by
          intro hnil
          apply hnonempty
          simp [hnil]
        obtain ⟨hl, hr, hlast⟩ := hcut.rel
        have hlastEq : first.getLast hl = base := by
          simpa using of_decide_eq_false hlast
        have hdist : Nat.dist base (next.head hnextNe) = 1 := by
          apply hadj.rel
          · rw [List.getLast?_eq_some_getLast hl, hlastEq]
            simp
          · exact List.head?_eq_some_head hnextNe
        have hnextGe : base ≤ next.head hnextNe := by
          apply hge
          simp only [List.flatten_cons, List.mem_append]
          exact Or.inr (Or.inl (List.head_mem hnextNe))
        have hnextEq : next.head hnextNe = base + 1 := by
          simp [Nat.dist] at hdist
          omega
        have htailNonempty : [] ∉ next :: rest := fun h ↦
          hnonempty (List.mem_cons_of_mem first h)
        apply ih htailNonempty hadj.tail hcut.tail
        · intro head hhead
          have : head = next := by simpa using hhead.symm
          subst head
          rw [List.head?_eq_some_head hnextNe, hnextEq]
        · intro x hx
          apply hge
          exact List.mem_append_right first hx
        · exact hchild

private theorem parsedChildren_getLast_eq
    {base : ℕ} {groups : List (List ℕ)}
    (hnonempty : [] ∉ groups)
    (hcut : groups.IsChain (fun left right ↦
      ∃ (hl : left ≠ []) (_hr : right ≠ []),
        decide (left.getLast hl ≠ base) = false))
    (hlast : ∀ last ∈ groups.getLast?, last.getLast? = some base) :
    ∀ child ∈ groups, child.getLast? = some base := by
  induction groups with
  | nil => simp
  | cons first rest ih =>
      intro child hchild
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hchild
          subst child
          exact hlast first (by simp)
      | cons next rest =>
          rcases List.mem_cons.mp hchild with rfl | hchild
          · obtain ⟨hl, hr, hfirstLast⟩ := hcut.rel
            rw [List.getLast?_eq_some_getLast]
            exact congrArg some (by
              simpa using of_decide_eq_false hfirstLast)
          · have htailNonempty : [] ∉ next :: rest := fun h ↦
              hnonempty (List.mem_cons_of_mem first h)
            apply ih htailNonempty hcut.tail
            · intro last hlastMem
              apply hlast last
              simpa using hlastMem
            · exact hchild

private theorem contourChildren_excursions
    {base : ℕ} {path : List ℕ}
    (hbase : 0 < base) (hpath : IsContourExcursion base path) :
    ∀ child ∈ contourChildren base path,
      IsContourExcursion (base + 1) child := by
  intro child hchild
  obtain ⟨middle, hpathEq, hge⟩ := hpath.1
  let groups := middle.splitBy (fun x _ ↦ decide (x ≠ base))
  have hgroups : contourChildren base path = groups := by
    simp [contourChildren, hpathEq, groups]
  rw [hgroups] at hchild
  have hnonempty : [] ∉ groups := List.nil_notMem_splitBy _ _
  have hflatten : groups.flatten = middle := List.flatten_splitBy _ _
  have hmiddleChain : middle.IsChain (fun x y ↦ Nat.dist x y = 1) := by
    rw [hpathEq] at hpath
    exact (List.isChain_append.mp hpath.2.tail).1
  have hgroupAdj : groups.IsChain (fun left right ↦
      ∀ x ∈ left.getLast?, ∀ y ∈ right.head?, Nat.dist x y = 1) := by
    exact (List.isChain_flatten hnonempty).mp (by simpa [hflatten] using hmiddleChain) |>.2
  have hgroupCut : groups.IsChain (fun left right ↦
      ∃ (hl : left ≠ []) (hr : right ≠ []),
        decide (left.getLast hl ≠ base) = false) := by
    simpa [groups] using List.isChain_getLast_head_splitBy
      (fun x _ ↦ decide (x ≠ base)) middle
  have hmiddleHead : ∀ first ∈ groups.head?, first.head? = some (base + 1) := by
    by_cases hmiddleNe : middle = []
    · intro first hfirst
      have hgroupsNil : groups = [] := by simp [groups, hmiddleNe]
      rw [hgroupsNil] at hfirst
      simp at hfirst
    · intro first hfirst
      have hfirstSome : groups.head? = some first := by
        simpa [Option.mem_def] using hfirst
      obtain ⟨groupTail, hgroupsCons⟩ :=
        List.head?_eq_some_iff.mp hfirstSome
      have hfirstNe : first ≠ [] := by
        intro hnil
        apply hnonempty
        rw [hgroupsCons]
        simp [hnil]
      have hhead := List.head_head_splitBy
        (fun x _ ↦ decide (x ≠ base)) hmiddleNe
      have hchainEq : (base :: middle ++ [base - 1]).IsChain
          (fun x y ↦ Nat.dist x y = 1) := by rw [← hpathEq]; exact hpath.2
      have hfirstStep : Nat.dist base (middle.head hmiddleNe) = 1 := by
        have hprefix := (List.isChain_append.mp hchainEq).1
        have hrel := (List.isChain_cons.mp hprefix).1
        apply hrel
        exact List.head?_eq_some_head hmiddleNe
      have hmiddleHeadGe : base ≤ middle.head hmiddleNe :=
        hge _ (by simp)
      have hmiddleHeadEq : middle.head hmiddleNe = base + 1 := by
        simp [Nat.dist] at hfirstStep
        omega
      rw [List.head?_eq_some_head hfirstNe]
      congr 1
      have hgroupsHead :
          groups.head (List.splitBy_ne_nil.mpr hmiddleNe) = first := by
        simp [hgroupsCons]
      have hgroupsHeadNe :
          groups.head (List.splitBy_ne_nil.mpr hmiddleNe) ≠ [] := by
        rw [hgroupsHead]
        exact hfirstNe
      calc
        first.head hfirstNe =
            (groups.head (List.splitBy_ne_nil.mpr hmiddleNe)).head
              hgroupsHeadNe := by simp [hgroupsHead]
        _ = middle.head hmiddleNe := hhead
        _ = base + 1 := hmiddleHeadEq
  have hmiddleLast : ∀ last ∈ groups.getLast?, last.getLast? = some base := by
    by_cases hmiddleNe : middle = []
    · intro last hlast
      have hgroupsNil : groups = [] := by simp [groups, hmiddleNe]
      rw [hgroupsNil] at hlast
      simp at hlast
    · intro last hlast
      have hlastSome : groups.getLast? = some last := by
        simpa [Option.mem_def] using hlast
      obtain ⟨groupInit, hgroupsLast⟩ :=
        List.getLast?_eq_some_iff.mp hlastSome
      have hlastNe : last ≠ [] := by
        intro hnil
        apply hnonempty
        rw [hgroupsLast]
        simp [hnil]
      have hlastLast := List.getLast_getLast_splitBy
        (fun x _ ↦ decide (x ≠ base)) hmiddleNe
      have hchainEq : (base :: middle ++ [base - 1]).IsChain
          (fun x y ↦ Nat.dist x y = 1) := by rw [← hpathEq]; exact hpath.2
      have hlastStep : Nat.dist (middle.getLast hmiddleNe) (base - 1) = 1 := by
        have hboundary := (List.isChain_append.mp hchainEq.tail).2.2
        apply hboundary
        · rw [List.getLast?_eq_some_getLast hmiddleNe]
          simp
        · simp
      have hmiddleLastGe : base ≤ middle.getLast hmiddleNe :=
        hge _ (by simp [List.getLast_mem hmiddleNe])
      have hmiddleLastEq : middle.getLast hmiddleNe = base := by
        simp [Nat.dist] at hlastStep
        omega
      rw [List.getLast?_eq_some_getLast hlastNe]
      congr 1
      have hgroupsGetLast :
          groups.getLast (List.splitBy_ne_nil.mpr hmiddleNe) = last := by
        simp [hgroupsLast]
      have hgroupsGetLastNe :
          groups.getLast (List.splitBy_ne_nil.mpr hmiddleNe) ≠ [] := by
        rw [hgroupsGetLast]
        exact hlastNe
      calc
        last.getLast hlastNe =
            (groups.getLast (List.splitBy_ne_nil.mpr hmiddleNe)).getLast
              hgroupsGetLastNe := by simp [hgroupsGetLast]
        _ = middle.getLast hmiddleNe := hlastLast
        _ = base := hmiddleLastEq
  have hhead : child.head? = some (base + 1) := by
    apply parsedChildren_head_eq hnonempty hgroupAdj hgroupCut hmiddleHead
    · intro x hx
      rw [hflatten] at hx
      exact hge x (by simp [hx])
    · exact hchild
  have hlast : child.getLast? = some base := by
    exact parsedChildren_getLast_eq hnonempty hgroupCut hmiddleLast child hchild
  have hchildChain : child.IsChain (fun x y ↦ Nat.dist x y = 1) := by
    exact ((List.isChain_flatten hnonempty).mp (by simpa [hflatten] using hmiddleChain)).1
      child hchild
  have hcutChain : child.IsChain (fun x _ ↦ x ≠ base) := by
    exact (List.isChain_of_mem_splitBy hchild).imp (by simp)
  have hsource : ∀ x ∈ child.dropLast, x ≠ base :=
    source_property_of_isChain hcutChain
  have hchildNe : child ≠ [] := List.ne_nil_of_mem_splitBy hchild
  refine ⟨?_, hchildChain⟩
  rw [List.head?_eq_some_iff] at hhead
  obtain ⟨tail, rfl⟩ := hhead
  have htailNe : tail ≠ [] := by
    intro hnil
    subst tail
    simp at hlast
  have htailLast : tail.getLast? = some base := by
    simpa only [List.getLast?_cons_of_ne_nil htailNe] using hlast
  let inner := tail.dropLast
  have htailEq : tail = inner ++ [base] := by
    symm
    exact List.dropLast_append_getLast? base htailLast
  refine ⟨inner, ?_, ?_⟩
  · rw [htailEq, Nat.add_sub_cancel]
    simp only [List.cons_append]
  intro x hx
  have hxDrop : x ∈ ((base + 1) :: tail).dropLast := by
    rw [List.dropLast_cons_of_ne_nil htailNe]
    exact hx
  have hxNe := hsource x hxDrop
  have hxMiddle : x ∈ middle := by
    rw [← hflatten]
    exact List.mem_flatten.mpr ⟨(base + 1) :: tail, hchild, by
      exact List.mem_of_mem_dropLast hxDrop⟩
  have hxGe := hge x (by simp [hxMiddle])
  omega

/-! ## Fixed-depth forest surjectivity -/

private def parsedChildForest (base : ℕ) (forest : List (List ℕ)) :
    List (List ℕ) :=
  (forest.map (contourChildren base)).flatten

private theorem parsedChildForest_excursions
    {base : ℕ} (hbase : 0 < base) {forest : List (List ℕ)}
    (hforest : ∀ path ∈ forest, IsContourExcursion base path) :
    ∀ child ∈ parsedChildForest base forest,
      IsContourExcursion (base + 1) child := by
  intro child hchild
  obtain ⟨groups, hgroups, hchildGroups⟩ := List.mem_flatten.mp hchild
  obtain ⟨path, hpath, hgroupsEq⟩ := List.mem_map.mp hgroups
  subst groups
  exact contourChildren_excursions hbase (hforest path hpath) child hchildGroups

private theorem parsedChildForest_bound
    {base depth : ℕ} {forest : List (List ℕ)}
    (hforest : ∀ path ∈ forest, IsContourExcursion base path)
    (hbound : ∀ path ∈ forest, ∀ x ∈ path, x < base + (depth + 1)) :
    ∀ child ∈ parsedChildForest base forest,
      ∀ x ∈ child, x < (base + 1) + depth := by
  intro child hchild x hx
  obtain ⟨groups, hgroups, hchildGroups⟩ := List.mem_flatten.mp hchild
  obtain ⟨path, hpath, hgroupsEq⟩ := List.mem_map.mp hgroups
  subst groups
  have hxMiddle : x ∈ (contourChildren base path).flatten :=
    List.mem_flatten.mpr ⟨child, hchildGroups, hx⟩
  rw [contourChildren_flatten (hforest path hpath).1] at hxMiddle
  have hxPath := List.mem_of_mem_tail (List.mem_of_mem_dropLast hxMiddle)
  have := hbound path hpath x hxPath
  omega

private theorem map_render_contourChildren
    {base : ℕ} {forest : List (List ℕ)}
    (hforest : ∀ path ∈ forest, IsContourExcursion base path) :
    (forest.map (contourChildren base)).map
        (fun group ↦ base :: group.flatten ++ [base - 1]) = forest := by
  rw [List.map_map]
  simpa only [List.map_id, Function.comp_apply] using
    (List.map_congr_left (l := forest)
      (f := (fun group ↦ base :: group.flatten ++ [base - 1]) ∘
        contourChildren base) (g := id) (by
          intro path hpath
          exact render_contourChildren (hforest path hpath).1))

private theorem exists_contourForest_of_bound :
    ∀ depth base : ℕ, 0 < base → ∀ forest : List (List ℕ),
      (∀ path ∈ forest, IsContourExcursion base path) →
      (∀ path ∈ forest, ∀ x ∈ path, x < base + depth) →
      ∃ (values : List ℕ) (chain : GapChain values),
        values.length = depth ∧
        values.headD 0 = forest.length ∧
        contourForest base values chain = forest
  | 0, base, hbase, forest, hforest, hbound => by
      have hforestNil : forest = [] := by
        by_contra hne
        obtain ⟨path, hpath⟩ := List.exists_mem_of_ne_nil forest hne
        obtain ⟨middle, hpathEq, _⟩ := (hforest path hpath).1
        have hbaseMem : base ∈ path := by simp [hpathEq]
        have := hbound path hpath base hbaseMem
        omega
      subst forest
      exact ⟨[], (), by simp, by simp, by simp [contourForest]⟩
  | depth + 1, base, hbase, forest, hforest, hbound => by
      let parentGroups := forest.map (contourChildren base)
      let children := parentGroups.flatten
      have hchildrenGood : ∀ child ∈ children,
          IsContourExcursion (base + 1) child := by
        simpa [children, parentGroups, parsedChildForest] using
          parsedChildForest_excursions hbase hforest
      have hchildrenBound : ∀ child ∈ children,
          ∀ x ∈ child, x < (base + 1) + depth := by
        simpa [children, parentGroups, parsedChildForest] using
          parsedChildForest_bound hforest hbound
      obtain ⟨tailValues, tailChain, htailLength, htailHead,
          htailRender⟩ :=
        exists_contourForest_of_bound depth (base + 1) (by omega)
          children hchildrenGood hchildrenBound
      cases tailValues with
      | nil =>
          have hchildrenNil : children = [] := by
            simpa [contourForest] using htailRender.symm
          have hparentGroupsEmpty : ∀ group ∈ parentGroups, group = [] := by
            intro group hgroup
            by_contra hgroupNe
            obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil group hgroupNe
            have : x ∈ children := by
              dsimp only [children]
              exact List.mem_flatten.mpr ⟨group, hgroup, hx⟩
            simp [hchildrenNil] at this
          have hpathSimple : ∀ path ∈ forest, path = [base, base - 1] := by
            intro path hpath
            have hgroupMem : contourChildren base path ∈ parentGroups := by
              exact List.mem_map.mpr ⟨path, hpath, rfl⟩
            have hgroupNil := hparentGroupsEmpty _ hgroupMem
            have hr := render_contourChildren (hforest path hpath).1
            simpa [hgroupNil] using hr.symm
          have hdepth : depth = 0 := by simpa using htailLength.symm
          subst depth
          refine ⟨[forest.length], (), by simp, by simp, ?_⟩
          simp only [contourForest]
          symm
          exact List.eq_replicate_length.mpr hpathSimple
      | cons b rest =>
          have hb : b = children.length := by
            simpa using htailHead
          let f : Fin forest.length → ℕ := fun i ↦
            (contourChildren base forest[i]).length
          have hsum : ∑ i, f i = children.length := by
            rw [← List.sum_ofFn]
            rw [show List.ofFn f =
                forest.map (fun path ↦ (contourChildren base path).length) by
              simpa [f] using List.ofFn_getElem_eq_map forest
                (fun path ↦ (contourChildren base path).length)]
            simp only [children, parentGroups, List.map_map,
              Function.comp_def, List.length_flatten]
          have hsumb : ∑ i, f i = b := hsum.trans hb.symm
          let pattern : GapPattern forest.length b :=
            gapPatternOfMultiplicitiesEq f hsumb
          refine ⟨forest.length :: b :: rest,
            (pattern, tailChain), by simp [htailLength], by simp, ?_⟩
          simp only [contourForest]
          rw [htailRender]
          have hsizes :
              List.ofFn (fun i : Fin forest.length ↦
                gapMultiplicity pattern i) = parentGroups.map List.length := by
            rw [show List.ofFn (fun i : Fin forest.length ↦
                gapMultiplicity pattern i) = List.ofFn f by
              congr 1
              funext i
              simp [pattern]]
            calc
              List.ofFn f = forest.map
                  (fun path ↦ (contourChildren base path).length) := by
                simpa [f] using List.ofFn_getElem_eq_map forest
                  (fun path ↦ (contourChildren base path).length)
              _ = parentGroups.map List.length := by
                simp [parentGroups, List.map_map, Function.comp_def]
          rw [hsizes]
          change ((parentGroups.map List.length).splitLengths children).map
              (fun group ↦ base :: group.flatten ++ [base - 1]) = forest
          dsimp only [children]
          rw [splitLengths_flatten_by_lengths]
          simpa [parentGroups] using map_render_contourChildren hforest

/-! ## Specialization to bounded radial words -/

private theorem radialListUpcrossingCount_eq_natStepCount
    {n k : ℕ} (labels : List (Fin (n + 2))) :
    radialListUpcrossingCount k labels =
      natStepCount (k - 1) k (labels.map Fin.val) := by
  induction labels with
  | nil => rfl
  | cons left tail ih =>
      cases tail with
      | nil => rfl
      | cons right tail =>
          simp only [List.map_cons, radialListUpcrossingCount, natStepCount]
          simpa using ih

private theorem radialLabelWord_natPath_isContourExcursion
    {n L : ℕ} (word : RadialLabelWord n L) :
    IsContourExcursion 1 (word.toList.map Fin.val) := by
  let path := word.toList.map Fin.val
  have hpathNe : path ≠ [] := by
    simp [path, RadialLabelWord.toList]
  have hhead : path.head? = some 1 := by
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr hpathNe)]
    congr 1
    simp only [path, List.getElem_map, RadialLabelWord.toList,
      List.getElem_ofFn]
    change (word.level ⟨0, by omega⟩ : ℕ) = 1
    simpa using congrArg Fin.val word.startsAtOne
  have hlast : path.getLast? = some 0 := by
    rw [List.getLast?_eq_some_getLast hpathNe]
    congr 1
    simp only [path, List.getLast_map, RadialLabelWord.toList,
      List.getLast_ofFn]
    change (word.level (Fin.last L) : ℕ) = 0
    simpa using congrArg Fin.val word.endsAtZero
  rw [List.head?_eq_some_iff] at hhead
  obtain ⟨tail, hpathEq⟩ := hhead
  have htailNe : tail ≠ [] := by
    intro hnil
    subst tail
    simp [hpathEq] at hlast
  have htailLast : tail.getLast? = some 0 := by
    rw [hpathEq, List.getLast?_cons_of_ne_nil htailNe] at hlast
    exact hlast
  let middle := tail.dropLast
  have htailEq : tail = middle ++ [0] := by
    symm
    exact List.dropLast_append_getLast? 0 htailLast
  have hshape : ExcursionShape 1 path := by
    refine ⟨middle, ?_, ?_⟩
    · rw [hpathEq, htailEq]
      norm_num
    intro x hx
    have hxPathDrop : x ∈ path.dropLast := by
      rw [hpathEq, htailEq]
      change x ∈ ((1 :: middle) ++ [0]).dropLast
      rw [List.dropLast_concat]
      exact hx
    have hxNe : x ≠ 0 := by
      obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hxPathDrop
      subst x
      have hiL : i < L := by
        simpa [path, RadialLabelWord.toList] using hi
      have hiPath : i < path.length := by
        rw [List.length_dropLast] at hi
        omega
      have hdropGet : path.dropLast[i] = path[i] := by simp
      have hget : path[i]'hiPath = (word.level ⟨i, by omega⟩ : ℕ) := by
        simp only [path, List.getElem_map, RadialLabelWord.toList,
          List.getElem_ofFn]
      rw [hdropGet, hget]
      exact word.beforeFinal_ne_zero ⟨i, hiL⟩
    omega
  refine ⟨hshape, ?_⟩
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hiL : i < L := by
    simpa [path, RadialLabelWord.toList] using hi
  have hleft : path[i] = (word.level ⟨i, by omega⟩ : ℕ) := by
    simp only [path, List.getElem_map, RadialLabelWord.toList,
      List.getElem_ofFn]
  have hright : path[i + 1] = (word.level ⟨i + 1, by omega⟩ : ℕ) := by
    simp only [path, List.getElem_map, RadialLabelWord.toList,
      List.getElem_ofFn]
  rw [hleft, hright]
  exact word.adjacent ⟨i, hiL⟩

private theorem radialLabelWord_natPath_bound
    {n L : ℕ} (word : RadialLabelWord n L) :
    ∀ x ∈ word.toList.map Fin.val, x < n + 2 := by
  intro x hx
  obtain ⟨label, _, rfl⟩ := List.mem_map.mp hx
  exact label.isLt

private theorem radialUpcrossingCount_eq_natStepCount
    {n L : ℕ} (word : RadialLabelWord n L) (k : Fin (n + 2))
    (hk : (k : ℕ) ≠ 0) :
    radialUpcrossingCount word k =
      natStepCount ((k : ℕ) - 1) k (word.toList.map Fin.val) := by
  rw [radialUpcrossingCount, dif_neg hk]
  exact radialListUpcrossingCount_eq_natStepCount word.toList

private theorem drop_headD_eq_getElem
    {A : Type*} [Inhabited A] (values : List A) (i : ℕ)
    (hi : i < values.length) :
    (values.drop i).headD default = values[i] := by
  rw [List.headD_eq_head?_getD]
  rw [List.head?_drop]
  rw [List.getElem?_eq_getElem hi]
  simp

private theorem contourWord_transport {left right : List ℕ}
    (h : left = right) (chain : GapChain (1 :: left)) :
    contourWord (1 :: right) (h ▸ chain) =
      contourWord (1 :: left) chain := by
  subst right
  rfl

theorem exists_fixedProfileWithCutoff_gapChain_contourWord_eq
    {n cutoff : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (word : BoundedRadialLabelWord n cutoff)
    (hfixed : IsFixedProfileRadialWordWithCutoff n cutoff delta m word) :
    ∃ (b : ℕ),
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3) ∧
      ∃ chain : GapChain (1 :: (profileList m ++ [b])),
        contourWord (1 :: (profileList m ++ [b])) chain =
          word.2.toList.map Fin.val := by
  let path := word.2.toList.map Fin.val
  obtain ⟨values, chain, hvaluesLength, hvaluesHead, hforest⟩ :=
    exists_contourForest_of_bound (n + 1) 1 (by omega) [path]
      (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst p
        exact radialLabelWord_natPath_isContourExcursion word.2)
      (by
        intro p hp x hx
        simp only [List.mem_singleton] at hp
        subst p
        have := radialLabelWord_natPath_bound word.2 x hx
        omega)
  have hforestOne : contourForest 1 values chain = [path] := hforest
  have hvaluesNe : values ≠ [] := by
    intro hnil
    rw [hnil] at hvaluesLength
    simp at hvaluesLength
  obtain ⟨a, tail, hvaluesEq⟩ := List.exists_cons_of_ne_nil hvaluesNe
  subst values
  have ha : a = 1 := by simpa using hvaluesHead
  subst a
  let b := radialUpcrossingCount word.2 ⟨n + 1, by omega⟩
  have hbLower : ⌈terminalLower n delta⌉₊ ≤ b := by
    apply Nat.ceil_le.mpr
    exact hfixed.2.1
  have hbUpper : b ≤ n ^ 3 := hfixed.2.2
  refine ⟨b, Finset.mem_Icc.mpr ⟨hbLower, hbUpper⟩, ?_⟩
  have htailLength : tail.length = n := by
    simpa using hvaluesLength
  have htailEq : tail = profileList m ++ [b] := by
    apply List.ext_get
    · simp [htailLength, profileList]
      omega
    · intro i hiTail hiTarget
      have hiN : i < n := by simpa [htailLength] using hiTail
      have hcount := contourForest_upcrossingCount 1 (by omega)
        (1 :: tail) chain i
      rw [hforestOne] at hcount
      simp only [List.map_singleton, List.sum_singleton] at hcount
      have hdrop : ((1 :: tail).drop (i + 1)).headD 0 = tail[i] := by
        rw [show (1 :: tail).drop (i + 1) = tail.drop i by simp]
        exact drop_headD_eq_getElem tail i hiTail
      rw [hdrop] at hcount
      by_cases hiInternal : i < n - 1
      · let j : Fin (n - 1) := ⟨i, hiInternal⟩
        have hradial := radialUpcrossingCount_eq_natStepCount word.2
          ⟨scaleIndex j, by dsimp [scaleIndex, j]; omega⟩
          (by dsimp [scaleIndex, j]; omega)
        have hfixedJ := hfixed.1 j
        have hcount' : natStepCount (scaleIndex j - 1) (scaleIndex j) path =
            tail[i] := by
          simpa [scaleIndex, j, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hcount
        rw [show path = word.2.toList.map Fin.val by rfl,
          ← hradial, hfixedJ] at hcount'
        have htargetElem : (profileList m ++ [b])[i] = m j := by
          rw [List.getElem_append_left]
          · simp [profileList, j]
          · simpa only [profileList, List.length_ofFn] using hiInternal
        calc
          tail.get ⟨i, hiTail⟩ = m j := hcount'.symm
          _ = (profileList m ++ [b]).get ⟨i, hiTarget⟩ := htargetElem.symm
      · have hiLast : i = n - 1 := by omega
        subst i
        have hradial := radialUpcrossingCount_eq_natStepCount word.2
          ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ (Nat.succ_ne_zero n)
        have hcount' : natStepCount n (n + 1) path = tail[n - 1] := by
          have hsource : 1 + (n - 1) = n := by omega
          have htarget : 1 + (n - 1) + 1 = n + 1 := by omega
          simpa only [hsource, htarget] using hcount
        change radialUpcrossingCount word.2 ⟨n + 1, _⟩ =
          natStepCount n (n + 1) (word.2.toList.map Fin.val) at hradial
        rw [show path = word.2.toList.map Fin.val by rfl,
          ← hradial] at hcount'
        change b = tail[n - 1] at hcount'
        have htargetElem : (profileList m ++ [b])[n - 1] = b := by
          rw [List.getElem_append_right]
          · simp [profileList]
          · simp [profileList]
        calc
          tail.get ⟨n - 1, hiTail⟩ = b := hcount'.symm
          _ = (profileList m ++ [b]).get ⟨n - 1, hiTarget⟩ := htargetElem.symm
  let targetChain : GapChain (1 :: (profileList m ++ [b])) :=
    htailEq ▸ chain
  refine ⟨targetChain, ?_⟩
  rw [show contourWord (1 :: (profileList m ++ [b])) targetChain =
      contourWord (1 :: tail) chain by
    exact contourWord_transport htailEq chain]
  unfold contourWord
  rw [hforestOne]
  rfl

/-- Standard-cutoff wrapper for the generic converse contour parser. -/
theorem exists_fixedProfile_gapChain_contourWord_eq
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n))
    (hfixed : IsFixedProfileRadialWord n delta m word) :
    ∃ (b : ℕ),
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3) ∧
      ∃ chain : GapChain (1 :: (profileList m ++ [b])),
        contourWord (1 :: (profileList m ++ [b])) chain =
          word.2.toList.map Fin.val := by
  apply exists_fixedProfileWithCutoff_gapChain_contourWord_eq hn word
  simpa only [IsFixedProfileRadialWord,
    IsFixedProfileRadialWordWithCutoff] using hfixed

/-! ## A right inverse to the successful-contour construction -/

/-- The finite code space of an admissible terminal count together with all
ordered-forest gap data for the prescribed radial profile. -/
abbrev SuccessfulContourCode
    (n : ℕ) (delta : ℝ) (m : Profile n) :=
  Σ b : {b : ℕ // b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)},
    GapChain (1 :: (profileList m ++ [b.1]))

/-- Render a contour code using the exact profile-dependent cutoff. -/
noncomputable def exactSuccessfulContourCodeWord
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (code : SuccessfulContourCode n delta m) :
    {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
      IsFixedProfileRadialWordWithCutoff n
        (exactProfileRadialWordMaxTransitions m) delta m word} :=
  ⟨exactSuccessfulContourWord hn code.1.1
      (Finset.mem_Icc.mp code.1.2).2 code.2,
    exactSuccessfulContourWord_isFixed hn code.1.1 code.1.2 code.2⟩

/-- Render a successful contour code as a fixed-profile chronological radial
word. -/
noncomputable def successfulContourCodeWord
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (code : SuccessfulContourCode n delta m) :
    {word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) //
      IsFixedProfileRadialWord n delta m word} :=
  ⟨successfulContourWord hn hdelta hm code.1.1
      (Finset.mem_Icc.mp code.1.2).2 code.2,
    successfulContourWord_isFixed hn hdelta hm code.1.1 code.1.2 code.2⟩

private theorem boundedRadialLabelWord_eq_of_toList_map_val_eq
    {n maxTransitions : ℕ}
    {left right : BoundedRadialLabelWord n maxTransitions}
    (hpath : left.2.toList.map Fin.val = right.2.toList.map Fin.val) :
    left = right := by
  rcases left with ⟨leftLength, left⟩
  rcases right with ⟨rightLength, right⟩
  have hlengthNat : (leftLength : ℕ) = (rightLength : ℕ) := by
    have hlength := congrArg List.length hpath
    simp only [List.length_map, RadialLabelWord.length_toList] at hlength
    omega
  have hlength : leftLength = rightLength := Fin.ext hlengthNat
  subst rightLength
  have hlist : left.toList = right.toList := by
    apply List.ext_get
    · simp
    · intro i hiLeft hiRight
      apply Fin.ext
      have hget := congrArg (fun path : List ℕ ↦ path[i]?) hpath
      simp only [List.getElem?_map] at hget
      rw [List.getElem?_eq_getElem hiLeft,
        List.getElem?_eq_getElem hiRight] at hget
      simpa using hget
  have hword : left = right := by
    apply RadialLabelWord.ext
    apply List.ofFn_injective
    exact hlist
  exact Sigma.ext rfl (heq_of_eq hword)

/-- Exact-cutoff contour rendering is surjective for every internal profile.
No parabolic-window hypothesis is needed. -/
theorem exactSuccessfulContourCodeWord_surjective
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n} :
    Function.Surjective (exactSuccessfulContourCodeWord hn
      (delta := delta) (m := m)) := by
  intro word
  obtain ⟨b, hb, chain, hpath⟩ :=
    exists_fixedProfileWithCutoff_gapChain_contourWord_eq
      hn word.1 word.2
  let terminal : {b : ℕ //
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)} := ⟨b, hb⟩
  let code : SuccessfulContourCode n delta m := ⟨terminal, chain⟩
  refine ⟨code, Subtype.ext ?_⟩
  apply boundedRadialLabelWord_eq_of_toList_map_val_eq
  dsimp only [exactSuccessfulContourCodeWord, code, terminal]
  rw [exactSuccessfulContourWord_toList_vals]
  exact hpath

/-- Canonical contour code for an exact-cutoff word. -/
noncomputable def exactFixedProfileRadialWordContourCode
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (word : {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
      IsFixedProfileRadialWordWithCutoff n
        (exactProfileRadialWordMaxTransitions m) delta m word}) :
    SuccessfulContourCode n delta m :=
  Classical.choose (exactSuccessfulContourCodeWord_surjective hn word)

@[simp] theorem exactSuccessfulContourCodeWord_exactFixedProfileRadialWordContourCode
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (word : {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
      IsFixedProfileRadialWordWithCutoff n
        (exactProfileRadialWordMaxTransitions m) delta m word}) :
    exactSuccessfulContourCodeWord hn
        (exactFixedProfileRadialWordContourCode hn word) = word :=
  Classical.choose_spec (exactSuccessfulContourCodeWord_surjective hn word)

theorem exactFixedProfileRadialWordContourCode_injective
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n} :
    Function.Injective
      (exactFixedProfileRadialWordContourCode hn (delta := delta) (m := m)) := by
  intro left right heq
  rw [← exactSuccessfulContourCodeWord_exactFixedProfileRadialWordContourCode
      hn left,
    ← exactSuccessfulContourCodeWord_exactFixedProfileRadialWordContourCode
      hn right,
    heq]

/-- Every fixed-profile chronological radial word is rendered by a successful
contour code.  This is the converse to the contour-code injection used in the
lower enumeration. -/
theorem successfulContourCodeWord_surjective
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    Function.Surjective (successfulContourCodeWord hn hdelta hm) := by
  intro word
  obtain ⟨b, hb, chain, hpath⟩ :=
    exists_fixedProfile_gapChain_contourWord_eq hn word.1 word.2
  let terminal : {b : ℕ //
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)} := ⟨b, hb⟩
  let code : SuccessfulContourCode n delta m := ⟨terminal, chain⟩
  refine ⟨code, Subtype.ext ?_⟩
  apply boundedRadialLabelWord_eq_of_toList_map_val_eq
  dsimp only [successfulContourCodeWord, code, terminal]
  rw [successfulContourWord_toList_vals]
  exact hpath

/-- A canonical successful contour code chosen for each fixed-profile word. -/
noncomputable def fixedProfileRadialWordContourCode
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (word : {word : BoundedRadialLabelWord n
        (profileRadialWordMaxTransitions n) //
        IsFixedProfileRadialWord n delta m word}) :
    SuccessfulContourCode n delta m :=
  Classical.choose (successfulContourCodeWord_surjective hn hdelta hm word)

@[simp] theorem successfulContourCodeWord_fixedProfileRadialWordContourCode
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (word : {word : BoundedRadialLabelWord n
        (profileRadialWordMaxTransitions n) //
        IsFixedProfileRadialWord n delta m word}) :
    successfulContourCodeWord hn hdelta hm
        (fixedProfileRadialWordContourCode hn hdelta hm word) = word :=
  Classical.choose_spec (successfulContourCodeWord_surjective hn hdelta hm word)

theorem fixedProfileRadialWordContourCode_injective
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    Function.Injective (fixedProfileRadialWordContourCode hn hdelta hm) := by
  intro left right heq
  rw [← successfulContourCodeWord_fixedProfileRadialWordContourCode
      hn hdelta hm left,
    ← successfulContourCodeWord_fixedProfileRadialWordContourCode
      hn hdelta hm right,
    heq]

end

end Erdos1165.AnnularRadialContourSurjection
