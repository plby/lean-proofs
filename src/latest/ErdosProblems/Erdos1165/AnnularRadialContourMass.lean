/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialContourEnumeration
import ErdosProblems.Erdos1165.AnnularRadialReferenceEdge
import ErdosProblems.Erdos1165.AnnularIdealReferenceCounts

/-!
# Contour words as bounded chronological radial words

This file packages the exact ordered-forest contours as literal radial-label
words.  It is kept separate from the geometric row estimates: the only input
here is the scalar ideal edge row.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialContourMass

open AppendixFirstMoment PathInsertion ProfileGapChain
  ProfileSmallBall
  AnnularIntegratedProfileKernel AnnularRadialLabelWord
  AnnularRadialProfileWords AnnularRadialChainLower
  AnnularRadialReferenceEdge AnnularRadialContourEnumeration
  AnnularIdealReferenceCounts
  TerminalNegativeBinomialWindow ExcursionTransition NegativeBinomial
  ThickPoint

noncomputable section

/-! ## Packaging a natural-number path -/

/-- Turn a nonempty bounded nearest-neighbour list, starting at one and
ending for the first time at zero, into a literal radial word. -/
private noncomputable def radialWordOfNatPath
    (n : ℕ) (path : List ℕ) (hne : path ≠ [])
    (hbound : ∀ x ∈ path, x < n + 2)
    (hstart : path.head? = some 1)
    (hadj : path.IsChain (fun x y ↦ Nat.dist x y = 1))
    (hbefore : ∀ i (hi : i < path.length),
      i + 1 < path.length → path[i]'hi ≠ 0)
    (hend : path.getLast? = some 0) :
    RadialLabelWord n (path.length - 1) := by
  have hlen : path.length - 1 + 1 = path.length :=
    Nat.sub_add_cancel (List.length_pos_iff.mpr hne)
  let index : Fin (path.length - 1 + 1) → Fin path.length :=
    fun j ↦ Fin.cast hlen j
  let level : Fin (path.length - 1 + 1) → Fin (n + 2) :=
    fun j ↦ ⟨path.get (index j), hbound _ (List.get_mem path (index j))⟩
  refine
    { level := level
      startsAtOne := ?_
      adjacent := ?_
      beforeFinal_ne_zero := ?_
      endsAtZero := ?_ }
  · apply Fin.ext
    have hzero : (index ⟨0, by omega⟩ : ℕ) = 0 := rfl
    have hheadElem : path[0] = 1 := by
      have := hstart
      rw [List.head?_eq_getElem?] at this
      rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr hne)] at this
      exact Option.some.inj this
    simpa [level, index, List.get_eq_getElem, hzero] using hheadElem
  · intro j
    have hj : (j : ℕ) + 1 < path.length := by omega
    have hstep := List.isChain_iff_getElem.mp hadj (j : ℕ) hj
    simpa [level, index, List.get_eq_getElem] using hstep
  · intro j
    have hj : (j : ℕ) + 1 < path.length := by omega
    simpa [level, index, List.get_eq_getElem] using
      hbefore (j : ℕ) (by omega) hj
  · apply Fin.ext
    have hlastElem : path[path.length - 1] = 0 := by
      rw [← List.getLast_eq_getElem hne]
      rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
      exact hend
    simpa [level, index, List.get_eq_getElem] using hlastElem

private theorem radialWordOfNatPath_toList_vals
    (n : ℕ) (path : List ℕ) (hne : path ≠ [])
    (hbound : ∀ x ∈ path, x < n + 2)
    (hstart hadj hbefore hend) :
    ((radialWordOfNatPath n path hne hbound hstart hadj hbefore hend).toList.map
      Fin.val) = path := by
  apply List.ext_get
  · simp [RadialLabelWord.toList]
    exact Nat.sub_add_cancel (List.length_pos_iff.mpr hne)
  · intro i hi₁ hi₂
    cases i with
    | zero => simp [radialWordOfNatPath, RadialLabelWord.toList]
    | succ i => simp [radialWordOfNatPath, RadialLabelWord.toList]

/-! ## The one-root contour -/

private theorem contourForest_one_eq_singleton
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    contourForest 1 (1 :: tail) chain = [contourWord (1 :: tail) chain] := by
  have hlen := length_contourForest 1 (1 :: tail) chain
  simp only [List.headD_cons] at hlen
  unfold contourWord
  generalize hforest : contourForest 1 (1 :: tail) chain = forest at hlen ⊢
  cases forest with
  | nil => simp at hlen
  | cons path rest =>
      cases rest with
      | nil => simp
      | cons next rest => simp at hlen

private theorem contourWord_mem_forest
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    contourWord (1 :: tail) chain ∈ contourForest 1 (1 :: tail) chain := by
  rw [contourForest_one_eq_singleton]
  simp

private theorem contourWord_shape
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    ExcursionShape 1 (contourWord (1 :: tail) chain) :=
  contourForest_excursionShape 1 (by omega) (1 :: tail) chain _
    (contourWord_mem_forest tail chain)

private theorem contourWord_start
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    (contourWord (1 :: tail) chain).head? = some 1 := by
  obtain ⟨middle, hpath, _⟩ := contourWord_shape tail chain
  rw [hpath]
  simp

private theorem contourWord_end
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    (contourWord (1 :: tail) chain).getLast? = some 0 := by
  obtain ⟨middle, hpath, _⟩ := contourWord_shape tail chain
  rw [hpath]
  norm_num
  exact List.getLast?_eq_some_iff.mpr ⟨1 :: middle, rfl⟩

private theorem before_final_ne_zero_of_excursionShape
    {path : List ℕ} (hshape : ExcursionShape 1 path) :
    ∀ i (hi : i < path.length), i + 1 < path.length → path[i]'hi ≠ 0 := by
  obtain ⟨middle, rfl, hge⟩ := hshape
  intro i hi hiLast
  norm_num at hi hiLast ⊢
  have hiPrefix : i < (1 :: middle).length := by
    simp only [List.length_cons, List.length_append, List.length_singleton] at hiLast ⊢
    omega
  change ((1 :: middle) ++ [0])[i] ≠ 0
  rw [List.getElem_append_left hiPrefix]
  have hxge := hge (1 :: middle)[i] (List.getElem_mem hiPrefix)
  omega

private theorem contourWord_before_final_ne_zero
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    ∀ i (hi : i < (contourWord (1 :: tail) chain).length),
      i + 1 < (contourWord (1 :: tail) chain).length →
        (contourWord (1 :: tail) chain)[i]'hi ≠ 0 :=
  before_final_ne_zero_of_excursionShape (contourWord_shape tail chain)

private theorem contourWord_adjacent
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    (contourWord (1 :: tail) chain).IsChain
      (fun x y ↦ Nat.dist x y = 1) :=
  contourForest_adjacent 1 (by omega) (1 :: tail) chain _
    (contourWord_mem_forest tail chain)

private theorem contourWord_length
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    (contourWord (1 :: tail) chain).length - 1 =
      2 * (1 :: tail).sum - 1 := by
  have h := contourForest_transitionLength 1 (by omega) (1 :: tail) chain
  rw [contourForest_one_eq_singleton] at h
  simpa using h

private theorem contourWord_upcrossingCount
    (tail : List ℕ) (chain : GapChain (1 :: tail)) (offset : ℕ) :
    natStepCount (1 + offset) (1 + offset + 1)
        (contourWord (1 :: tail) chain) =
      ((1 :: tail).drop (offset + 1)).headD 0 := by
  have h := contourForest_upcrossingCount 1 (by omega)
    (1 :: tail) chain offset
  rw [contourForest_one_eq_singleton] at h
  simpa using h

private theorem contourWord_downcrossingCount
    (tail : List ℕ) (chain : GapChain (1 :: tail)) (offset : ℕ) :
    natStepCount (1 + offset) (1 + offset - 1)
        (contourWord (1 :: tail) chain) =
      ((1 :: tail).drop offset).headD 0 := by
  have h := contourForest_downcrossingCount 1 (by omega)
    (1 :: tail) chain offset
  rw [contourForest_one_eq_singleton] at h
  simpa using h

private theorem contourWord_injective (tail : List ℕ) :
    Function.Injective (contourWord (1 :: tail)) := by
  intro left right hword
  apply contourForest_injective 1 (by omega) (1 :: tail)
  rw [contourForest_one_eq_singleton, contourForest_one_eq_singleton, hword]

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
          simp only [List.map_cons, radialListUpcrossingCount, natStepCount,
            Fin.val_mk]
          simpa using ih

private theorem radialLabelWord_sourcesNonzero
    {n L : ℕ} (word : RadialLabelWord n L) :
    SourcesNonzero (word.level ⟨0, by omega⟩) word.toList.tail := by
  apply sourcesNonzero_of_getElem (word.level ⟨0, by omega⟩) word.toList.tail
  intro i hi hiLast
  cases i with
  | zero =>
      have hL : 0 < L := by
        simp [RadialLabelWord.toList, List.ofFn_succ] at hiLast
        omega
      simpa [RadialLabelWord.toList, List.ofFn_succ] using
        word.beforeFinal_ne_zero ⟨0, hL⟩
  | succ i =>
      have hiFin : i + 1 < L := by
        simp [RadialLabelWord.toList, List.ofFn_succ] at hiLast
        omega
      simpa [RadialLabelWord.toList, List.ofFn_succ] using
        word.beforeFinal_ne_zero ⟨i + 1, hiFin⟩

private theorem radialLabelWord_toList_isChain
    {n L : ℕ} (word : RadialLabelWord n L) :
    word.toList.IsChain
      (fun (left right : Fin (n + 2)) ↦
        Nat.dist (left : ℕ) (right : ℕ) = 1) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hiL : i < L := by
    rw [word.length_toList] at hi
    omega
  simp only [RadialLabelWord.toList, List.getElem_ofFn]
  have hstep := word.adjacent ⟨i, hiL⟩
  change Nat.dist (word.level ⟨i, by omega⟩)
    (word.level ⟨i + 1, by omega⟩) = 1 at hstep
  exact hstep

/-! ## Successful contour words -/

private theorem profileList_sum_le_three_mul_cube
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    (profileList m).sum ≤ 3 * n ^ 3 := by
  have hentry : ∀ a ∈ profileList m, a ≤ 3 * n ^ 2 := by
    rw [profileList, List.forall_mem_ofFn_iff]
    exact constrainedProfile_entry_le_three_mul_n_sq hdelta hm
  have hsum := List.sum_le_card_nsmul (profileList m) (3 * n ^ 2) hentry
  have hlength : (profileList m).length = n - 1 := by simp [profileList]
  calc
    (profileList m).sum ≤ (n - 1) * (3 * n ^ 2) := by
      simpa [hlength, nsmul_eq_mul] using hsum
    _ ≤ n * (3 * n ^ 2) :=
      Nat.mul_le_mul_right (3 * n ^ 2) (Nat.sub_le n 1)
    _ = 3 * n ^ 3 := by ring

private theorem profile_drop_headD
    {n : ℕ} (m : Profile n) (i : Fin (n - 1)) (b : ℕ) :
    ((1 :: (profileList m ++ [b])).drop (i.val + 1)).headD 0 = m i := by
  change ((1 :: (profileList m ++ [b])).drop (i.val + 1)).headD 0 = m i
  rw [List.drop_cons (by omega), Nat.add_sub_cancel]
  have hi : i.val < (profileList m).length := by simp [profileList]
  rw [show (profileList m ++ [b]).drop i.val =
      (profileList m ++ [b])[i.val]'(by
        simp only [List.length_append, List.length_singleton]
        omega) ::
        (profileList m ++ [b]).drop (i.val + 1) by
      exact List.drop_eq_getElem_cons (by simpa [profileList] using hi)]
  simp only [List.headD_cons]
  rw [List.getElem_append_left hi]
  simp [profileList]

private theorem terminal_drop_headD
    {n : ℕ} (hn : 2 ≤ n) (m : Profile n) (b : ℕ) :
    ((1 :: (profileList m ++ [b])).drop n).headD 0 = b := by
  change ((1 :: (profileList m ++ [b])).drop n).headD 0 = b
  rw [List.drop_cons (by omega)]
  have hlength : (profileList m).length = n - 1 := by simp [profileList]
  rw [show n - 1 = (profileList m).length by exact hlength.symm]
  simp

/-- The contour word for an arbitrary exact profile, packaged in that
profile's own finite cutoff. -/
noncomputable def exactSuccessfulContourWord
    {n : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    BoundedRadialLabelWord n (exactProfileRadialWordMaxTransitions m) := by
  let values := 1 :: (profileList m ++ [b])
  let path := contourWord values chain
  have hmem : path ∈ contourForest 1 values chain := by
    exact contourWord_mem_forest (profileList m ++ [b]) chain
  have hstart : path.head? = some 1 := by
    exact contourWord_start (profileList m ++ [b]) chain
  have hne : path ≠ [] := by
    intro hnil
    simp [hnil] at hstart
  have hbound : ∀ x ∈ path, x < n + 2 := by
    intro x hx
    have hrange := contourForest_lt_base_add_length 1 (by omega)
      values chain path hmem x hx
    dsimp only [values] at hrange
    have hvaluesLength : values.length = n + 1 := by
      dsimp only [values]
      simp [profileList]
      omega
    rw [hvaluesLength] at hrange
    omega
  have hadj : path.IsChain (fun x y ↦ Nat.dist x y = 1) := by
    exact contourWord_adjacent (profileList m ++ [b]) chain
  have hbefore : ∀ i (hi : i < path.length),
      i + 1 < path.length → path[i]'hi ≠ 0 := by
    exact contourWord_before_final_ne_zero (profileList m ++ [b]) chain
  have hend : path.getLast? = some 0 := by
    exact contourWord_end (profileList m ++ [b]) chain
  have htransition := contourWord_length (profileList m ++ [b]) chain
  have hlengthBound : path.length - 1 ≤
      exactProfileRadialWordMaxTransitions m := by
    change path.length - 1 =
      2 * (1 :: (profileList m ++ [b])).sum - 1 at htransition
    rw [htransition]
    simp only [List.sum_cons, List.sum_append, List.sum_singleton,
      List.sum_nil, add_zero]
    unfold exactProfileRadialWordMaxTransitions
    omega
  let word := radialWordOfNatPath n path hne hbound hstart hadj hbefore hend
  exact ⟨⟨path.length - 1, by omega⟩, word⟩

theorem exactSuccessfulContourWord_toList_vals
    {n : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    ((exactSuccessfulContourWord hn b hb chain).2.toList.map Fin.val) =
      contourWord (1 :: (profileList m ++ [b])) chain := by
  unfold exactSuccessfulContourWord
  dsimp only
  apply radialWordOfNatPath_toList_vals

theorem exactSuccessfulContourWord_isFixed
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (b : ℕ)
    (hb : b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3))
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    IsFixedProfileRadialWordWithCutoff n
      (exactProfileRadialWordMaxTransitions m) delta m
      (exactSuccessfulContourWord hn b (Finset.mem_Icc.mp hb).2 chain) := by
  have hbBounds := Finset.mem_Icc.mp hb
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (if hk : scaleIndex i = 0 then 0 else
      radialListUpcrossingCount (scaleIndex i)
        (exactSuccessfulContourWord hn b hbBounds.2 chain).2.toList) = m i
    rw [dif_neg (by unfold scaleIndex; omega)]
    rw [radialListUpcrossingCount_eq_natStepCount]
    rw [exactSuccessfulContourWord_toList_vals]
    have hcount := contourWord_upcrossingCount
      (profileList m ++ [b]) chain i.val
    simp only [scaleIndex]
    rw [show i.val + 2 - 1 = 1 + i.val by omega,
      show i.val + 2 = 1 + i.val + 1 by omega,
      hcount, profile_drop_headD]
  · have hcount : radialUpcrossingCount
      (exactSuccessfulContourWord hn b hbBounds.2 chain).2
          ⟨n + 1, by omega⟩ = b := by
      unfold radialUpcrossingCount
      rw [dif_neg (by omega : n + 1 ≠ 0)]
      simp only [Fin.val_mk]
      rw [radialListUpcrossingCount_eq_natStepCount]
      rw [exactSuccessfulContourWord_toList_vals]
      have h := contourWord_upcrossingCount
        (profileList m ++ [b]) chain (n - 1)
      rw [show n + 1 - 1 = 1 + (n - 1) by omega,
        show n + 1 = 1 + (n - 1) + 1 by omega, h,
        show n - 1 + 1 = n by omega, terminal_drop_headD hn]
    rw [hcount]
    exact Nat.ceil_le.mp hbBounds.1
  · have hcount : radialUpcrossingCount
      (exactSuccessfulContourWord hn b hbBounds.2 chain).2
          ⟨n + 1, by omega⟩ = b := by
      unfold radialUpcrossingCount
      rw [dif_neg (by omega : n + 1 ≠ 0)]
      simp only [Fin.val_mk]
      rw [radialListUpcrossingCount_eq_natStepCount]
      rw [exactSuccessfulContourWord_toList_vals]
      have h := contourWord_upcrossingCount
        (profileList m ++ [b]) chain (n - 1)
      rw [show n + 1 - 1 = 1 + (n - 1) by omega,
        show n + 1 = 1 + (n - 1) + 1 by omega, h,
        show n - 1 + 1 = n by omega, terminal_drop_headD hn]
    simpa [hcount] using hbBounds.2

/-! ## Finite variable-parameter gap-chain sum -/

/-- At contour level `level`, regular rows use one half and the last
nontrivial row uses the terminal success parameter. -/
private def contourSuccess (n level : ℕ) : ℝ :=
  if level < n then 1 / 2 else terminalSuccess n

/-- Product of geometric decision masses attached to a complete gap chain,
with the success parameter allowed to depend on the contour level. -/
private def contourGapChainMass (n : ℕ) :
    (level : ℕ) → (values : List ℕ) → GapChain values → ℝ
  | _, [], _ => 1
  | _, [_], _ => 1
  | level, _a :: b :: rest, chain =>
      (∏ i, geometricOffspringMass (contourSuccess n level)
        (gapMultiplicity chain.1 i)) *
        contourGapChainMass n (level + 1) (b :: rest) chain.2

/-- Product of the corresponding negative-binomial transition masses. -/
private def contourTransitionProduct (n : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | _, [_] => 1
  | level, a :: b :: rest =>
      NegativeBinomial.mass (contourSuccess n level) a b *
        contourTransitionProduct n (level + 1) (b :: rest)

/-- The chain-independent product of all chronological decision masses. -/
private def contourDecisionProduct (n : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | _, [_] => 1
  | level, a :: b :: rest =>
      contourSuccess n level ^ a * (1 - contourSuccess n level) ^ b *
        contourDecisionProduct n (level + 1) (b :: rest)

/-- Positivity is required only for populations which are sources of a
negative-binomial transition; the final target may be zero. -/
private def ContourSourcesPositive : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => 0 < a ∧ ContourSourcesPositive (b :: rest)

private theorem contourGapChainMass_eq_contourDecisionProduct
    (n level : ℕ) : ∀ (values : List ℕ) (chain : GapChain values),
    contourGapChainMass n level values chain =
      contourDecisionProduct n level values
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, chain => by
      simp only [contourGapChainMass, contourDecisionProduct]
      rw [show (∏ i, geometricOffspringMass (contourSuccess n level)
          (gapMultiplicity chain.1 i)) =
          contourSuccess n level ^ a * (1 - contourSuccess n level) ^ b by
        simpa [gapMultiplicity, offspringMultiplicity] using
          prod_geometricOffspringMass (contourSuccess n level) chain.1]
      rw [contourGapChainMass_eq_contourDecisionProduct n (level + 1)
        (b :: rest) chain.2]

private theorem sum_contourGapChainMass_eq_contourTransitionProduct
    (n level : ℕ) : ∀ values : List ℕ,
    ContourSourcesPositive values →
      ∑ chain : GapChain values, contourGapChainMass n level values chain =
        contourTransitionProduct n level values
  | [], _ => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | [_a], _ => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | a :: b :: rest, hpos => by
      have ha : 0 < a := hpos.1
      have htail : ContourSourcesPositive (b :: rest) := hpos.2
      change (∑ chain : GapPattern a b × GapChain (b :: rest),
        (∏ i, geometricOffspringMass (contourSuccess n level)
          (gapMultiplicity chain.1 i)) *
          contourGapChainMass n (level + 1) (b :: rest) chain.2) = _
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [sum_contourGapChainMass_eq_contourTransitionProduct n (level + 1)
        (b :: rest) htail]
      have hsum := sum_offspringPattern_weight ha b (contourSuccess n level)
      rw [show (∑ i : GapPattern a b,
          ∏ x, geometricOffspringMass (contourSuccess n level)
            (gapMultiplicity i x)) =
          NegativeBinomial.mass (contourSuccess n level) a b by
        simpa [gapMultiplicity, offspringMultiplicity] using hsum]
      rfl

private theorem contourSuccess_nonneg {n level : ℕ} (hn : 2 ≤ n) :
    0 ≤ contourSuccess n level := by
  unfold contourSuccess
  split_ifs
  · norm_num
  · exact (terminalSuccess_pos hn).le

private theorem contourSuccess_le_one {n level : ℕ} (hn : 2 ≤ n) :
    contourSuccess n level ≤ 1 := by
  unfold contourSuccess
  split_ifs
  · norm_num
  · exact terminalSuccess_le_one hn

private theorem contourGapChainMass_nonneg {n level : ℕ} (hn : 2 ≤ n) :
    ∀ {values : List ℕ} (chain : GapChain values),
      0 ≤ contourGapChainMass n level values chain
  | [], _ => by simp [contourGapChainMass]
  | [_], _ => by simp [contourGapChainMass]
  | _a :: b :: rest, chain => by
      apply mul_nonneg
      · apply Finset.prod_nonneg
        intro i _
        unfold geometricOffspringMass
        exact mul_nonneg (contourSuccess_nonneg hn)
          (pow_nonneg (sub_nonneg.mpr (contourSuccess_le_one hn)) _)
      · exact contourGapChainMass_nonneg hn chain.2

private theorem sum_ofReal_contourGapChainMass_eq
    {n level : ℕ} (hn : 2 ≤ n) (values : List ℕ)
    (hpos : ContourSourcesPositive values) :
    ∑ chain : GapChain values,
        ENNReal.ofReal (contourGapChainMass n level values chain) =
      ENNReal.ofReal (contourTransitionProduct n level values) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun chain _ ↦ contourGapChainMass_nonneg hn chain),
    sum_contourGapChainMass_eq_contourTransitionProduct n level values hpos]

private theorem contourSourcesPositive_append_singleton (b : ℕ) :
    ∀ (values : List ℕ), (∀ a ∈ values, 0 < a) →
      ContourSourcesPositive (values ++ [b])
  | [], _ => by simp [ContourSourcesPositive]
  | [a], hpos => by
      exact ⟨hpos a (by simp), by simp [ContourSourcesPositive]⟩
  | a :: c :: rest, hpos => by
      refine ⟨hpos a (by simp), ?_⟩
      exact contourSourcesPositive_append_singleton b (c :: rest)
        (fun x hx ↦ hpos x (by simp [hx]))

private theorem contourTransitionProduct_append_singleton
    (n b : ℕ) : ∀ (values : List ℕ) (level : ℕ)
    (hne : values ≠ [])
    (hpos : ∀ a ∈ values, 0 < a)
    (hlastLevel : level + values.length - 1 = n),
    contourTransitionProduct n level (values ++ [b]) =
      transitionProduct values *
        NegativeBinomial.mass (terminalSuccess n) (values.getLast hne) b
  | [], _, hne, _, _ => (hne rfl).elim
  | [a], level, _, _, hlastLevel => by
      have hlevel : level = n := by simp at hlastLevel; omega
      subst level
      simp [contourTransitionProduct, contourSuccess]
  | a :: c :: rest, level, hne, hpos, hlastLevel => by
      have hlevel : level < n := by
        simp only [List.length_cons] at hlastLevel
        omega
      have ha : 0 < a := hpos a (by simp)
      have htailPos : ∀ x ∈ c :: rest, 0 < x :=
        fun x hx ↦ hpos x (by simp [hx])
      have htailLevel : level + 1 + (c :: rest).length - 1 = n := by
        simp only [List.length_cons] at hlastLevel ⊢
        omega
      have ih := contourTransitionProduct_append_singleton n b (c :: rest)
        (level + 1) (by simp) htailPos htailLevel
      simp only [List.cons_append, contourTransitionProduct]
      rw [contourSuccess, if_pos hlevel]
      rw [← transitionMass_of_pos ha c]
      rw [show c :: (rest ++ [b]) = (c :: rest) ++ [b] by rfl]
      rw [ih]
      rw [transitionProduct_cons_cons]
      have hlastEq : (a :: c :: rest).getLast hne =
          (c :: rest).getLast (by simp) := List.getLast_cons (by simp)
      rw [hlastEq]
      ring

private theorem contourDecisionProduct_append_singleton
    (n b : ℕ) : ∀ (values : List ℕ) (level : ℕ)
    (hne : values ≠ [])
    (hlastLevel : level + values.length - 1 = n),
    contourDecisionProduct n level (values ++ [b]) =
      (1 / 2 : ℝ) ^ radialWordLength values *
        terminalSuccess n ^ values.getLast hne *
        (1 - terminalSuccess n) ^ b
  | [], _, hne, _ => (hne rfl).elim
  | [a], level, _, hlastLevel => by
      have hlevel : level = n := by simp at hlastLevel; omega
      subst level
      simp [contourDecisionProduct, contourSuccess, radialWordLength]
  | a :: c :: rest, level, hne, hlastLevel => by
      have hlevel : level < n := by
        simp only [List.length_cons] at hlastLevel
        omega
      have htailLevel : level + 1 + (c :: rest).length - 1 = n := by
        simp only [List.length_cons] at hlastLevel ⊢
        omega
      have ih := contourDecisionProduct_append_singleton n b (c :: rest)
        (level + 1) (by simp) htailLevel
      simp only [List.cons_append, contourDecisionProduct]
      rw [contourSuccess, if_pos hlevel]
      rw [show c :: (rest ++ [b]) = (c :: rest) ++ [b] by rfl, ih]
      have hlastEq : (a :: c :: rest).getLast hne =
          (c :: rest).getLast (by simp) := List.getLast_cons (by simp)
      rw [hlastEq]
      simp only [radialWordLength, pow_add]
      norm_num only [one_div]
      ring

private theorem radialWordLength_add_head_add_last_eq_two_mul_sum :
    ∀ (values : List ℕ) (hne : values ≠ []),
      radialWordLength values + values.head hne + values.getLast hne =
        2 * values.sum
  | [], hne => (hne rfl).elim
  | [a], _ => by simp [radialWordLength]; omega
  | a :: b :: rest, hne => by
      have ih := radialWordLength_add_head_add_last_eq_two_mul_sum
        (b :: rest) (by simp)
      rw [radialWordLength]
      rw [List.getLast_cons (by simp)]
      simp only [List.head_cons, List.sum_cons]
      simp only [List.head_cons, List.sum_cons] at ih
      omega

private theorem contourTransitionProduct_profile_terminal
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) (b : ℕ) :
    contourTransitionProduct n 1 (1 :: (profileList m ++ [b])) =
      firstProfileTransitionMass hn m * profileWeight m *
        NegativeBinomial.mass (terminalSuccess n)
          (terminalProfileCount hn m) b := by
  let values : List ℕ := 1 :: profileList m
  have hne : values ≠ [] := by simp [values]
  have hpos : ∀ a ∈ values, 0 < a := by
    intro a ha
    simp only [values, List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have htwo := constrainedProfile_all_entries_two_le hdelta hm a ha
      omega
  have hlength : values.length = n := by
    simp [values, profileList]
    omega
  have hlastLevel : 1 + values.length - 1 = n := by omega
  have hmain := contourTransitionProduct_append_singleton n b values 1
    hne hpos hlastLevel
  have hprofileNe : profileList m ≠ [] := by
    simp [profileList]
    omega
  have hlast : values.getLast hne = terminalProfileCount hn m := by
    change (1 :: profileList m).getLast _ = terminalProfileCount hn m
    rw [List.getLast_cons hprofileNe]
    unfold profileList at hprofileNe ⊢
    rw [List.getLast_ofFn]
    unfold terminalProfileCount
    congr 1
  have htransition : transitionProduct values =
      firstProfileTransitionMass hn m * profileWeight m := by
    have hprofileHead : (profileList m).head hprofileNe =
        m ⟨0, by omega⟩ := by
      unfold profileList at hprofileNe ⊢
      rw [List.head_ofFn]
    change transitionProduct (1 :: profileList m) = _
    calc
      transitionProduct (1 :: profileList m) =
          AppendixFirstMoment.transitionMass 1
            ((profileList m).head hprofileNe) *
            transitionProduct (profileList m) := by
        conv_lhs => rw [← List.cons_head_tail hprofileNe]
        rw [transitionProduct_cons_cons, List.cons_head_tail hprofileNe]
      _ = firstProfileTransitionMass hn m * profileWeight m := by
        rw [hprofileHead]
        rfl
  simpa [values, htransition, hlast] using hmain

/-- The bounded chronological radial word rendered by one successful
ordered-forest contour. -/
noncomputable def successfulContourWord
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) := by
  let values := 1 :: (profileList m ++ [b])
  let path := contourWord values chain
  have hmem : path ∈ contourForest 1 values chain := by
    exact contourWord_mem_forest (profileList m ++ [b]) chain
  have hstart : path.head? = some 1 := by
    exact contourWord_start (profileList m ++ [b]) chain
  have hne : path ≠ [] := by
    intro hnil
    simp [hnil] at hstart
  have hbound : ∀ x ∈ path, x < n + 2 := by
    intro x hx
    have hrange := contourForest_lt_base_add_length 1 (by omega)
      values chain path hmem x hx
    dsimp only [values] at hrange
    have hvaluesLength : values.length = n + 1 := by
      dsimp only [values]
      simp [profileList]
      omega
    rw [hvaluesLength] at hrange
    omega
  have hadj : path.IsChain (fun x y ↦ Nat.dist x y = 1) := by
    exact contourWord_adjacent (profileList m ++ [b]) chain
  have hbefore : ∀ i (hi : i < path.length),
      i + 1 < path.length → path[i]'hi ≠ 0 := by
    exact contourWord_before_final_ne_zero (profileList m ++ [b]) chain
  have hend : path.getLast? = some 0 := by
    exact contourWord_end (profileList m ++ [b]) chain
  have hprofileSum := profileList_sum_le_three_mul_cube hdelta hm
  have hvaluesSum : values.sum = 1 + (profileList m).sum + b := by
    dsimp only [values]
    simp
    omega
  have hsum : values.sum ≤ 1 + 4 * n ^ 3 := by
    rw [hvaluesSum]
    omega
  have htransition := contourWord_length (profileList m ++ [b]) chain
  have hlengthBound : path.length - 1 ≤ profileRadialWordMaxTransitions n := by
    change path.length - 1 = 2 * values.sum - 1 at htransition
    rw [htransition]
    unfold profileRadialWordMaxTransitions
    omega
  let word := radialWordOfNatPath n path hne hbound hstart hadj hbefore hend
  exact ⟨⟨path.length - 1, by omega⟩, word⟩

theorem successfulContourWord_toList_vals
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    ((successfulContourWord hn hdelta hm b hb chain).2.toList.map Fin.val) =
      contourWord (1 :: (profileList m ++ [b])) chain := by
  unfold successfulContourWord
  dsimp only
  apply radialWordOfNatPath_toList_vals

theorem successfulContourWord_isFixed
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (b : ℕ)
    (hb : b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3))
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    IsFixedProfileRadialWord n delta m
      (successfulContourWord hn hdelta hm b (Finset.mem_Icc.mp hb).2 chain) := by
  have hbBounds := Finset.mem_Icc.mp hb
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (if hk : scaleIndex i = 0 then 0 else
      radialListUpcrossingCount (scaleIndex i)
        (successfulContourWord hn hdelta hm b hbBounds.2 chain).2.toList) = m i
    rw [dif_neg (by unfold scaleIndex; omega)]
    rw [radialListUpcrossingCount_eq_natStepCount]
    rw [successfulContourWord_toList_vals]
    have hcount := contourWord_upcrossingCount
      (profileList m ++ [b]) chain i.val
    simp only [scaleIndex]
    rw [show i.val + 2 - 1 = 1 + i.val by omega,
      show i.val + 2 = 1 + i.val + 1 by omega,
      hcount, profile_drop_headD]
  · have hcount : radialUpcrossingCount
      (successfulContourWord hn hdelta hm b hbBounds.2 chain).2
          ⟨n + 1, by omega⟩ = b := by
      unfold radialUpcrossingCount
      rw [dif_neg (by omega : n + 1 ≠ 0)]
      simp only [Fin.val_mk]
      rw [radialListUpcrossingCount_eq_natStepCount]
      rw [successfulContourWord_toList_vals]
      have h := contourWord_upcrossingCount
        (profileList m ++ [b]) chain (n - 1)
      rw [show n + 1 - 1 = 1 + (n - 1) by omega,
        show n + 1 = 1 + (n - 1) + 1 by omega, h,
        show n - 1 + 1 = n by omega, terminal_drop_headD hn]
    rw [hcount]
    exact Nat.ceil_le.mp hbBounds.1
  · have hcount : radialUpcrossingCount
      (successfulContourWord hn hdelta hm b hbBounds.2 chain).2
          ⟨n + 1, by omega⟩ = b := by
      unfold radialUpcrossingCount
      rw [dif_neg (by omega : n + 1 ≠ 0)]
      simp only [Fin.val_mk]
      rw [radialListUpcrossingCount_eq_natStepCount]
      rw [successfulContourWord_toList_vals]
      have h := contourWord_upcrossingCount
        (profileList m ++ [b]) chain (n - 1)
      rw [show n + 1 - 1 = 1 + (n - 1) by omega,
        show n + 1 = 1 + (n - 1) + 1 by omega, h,
        show n - 1 + 1 = n by omega, terminal_drop_headD hn]
    simpa [hcount] using hbBounds.2

private theorem successfulContourWord_reference_eq_mass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    radialChainReference (annularIdealEdge n)
        ((successfulContourWord hn hdelta hm b hb chain).2.level
          ⟨0, by omega⟩)
        (successfulContourWord hn hdelta hm b hb chain).2.toList.tail =
      ENNReal.ofReal
        (contourGapChainMass n 1 (1 :: (profileList m ++ [b])) chain) := by
  let word := successfulContourWord hn hdelta hm b hb chain
  let values : List ℕ := 1 :: (profileList m ++ [b])
  let path : List ℕ := contourWord values chain
  have hcons : word.2.level ⟨0, by omega⟩ :: word.2.toList.tail =
      word.2.toList := by
    simp [RadialLabelWord.toList, List.ofFn_succ]
  have hchain : (word.2.level ⟨0, by omega⟩ :: word.2.toList.tail).IsChain
      (fun (left right : Fin (n + 2)) ↦
        Nat.dist (left : ℕ) (right : ℕ) = 1) := by
    rw [hcons]
    exact radialLabelWord_toList_isChain word.2
  have hsources : SourcesNonzero (word.2.level ⟨0, by omega⟩)
      word.2.toList.tail := radialLabelWord_sourcesNonzero word.2
  have hmapped :
      ((word.2.level ⟨0, by omega⟩ :: word.2.toList.tail).map Fin.val) =
        path := by
    rw [hcons]
    simpa [word, values, path] using
      successfulContourWord_toList_vals hn hdelta hm b hb chain
  have hchainNat :
      ((word.2.level ⟨0, by omega⟩ :: word.2.toList.tail).map Fin.val).IsChain
        (fun left right : ℕ ↦ Nat.dist left right = 1) := by
    rw [hmapped]
    simpa [path, values] using
      contourWord_adjacent (profileList m ++ [b]) chain
  have hdown : directedLabelStepCount n (n - 1)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail =
        terminalProfileCount hn m := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := contourWord_downcrossingCount
      (profileList m ++ [b]) chain (n - 1)
    dsimp only [path, values]
    have h' : natStepCount n (n - 1)
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop (n - 1)).headD 0 := by
      simpa only [show 1 + (n - 1) = n by omega,
        show 1 + (n - 1) - 1 = n - 1 by omega] using h
    rw [h']
    have hp := profile_drop_headD m (⟨n - 2, by omega⟩ : Fin (n - 1)) b
    rw [show (n - 2) + 1 = n - 1 by omega] at hp
    simpa [terminalProfileCount] using hp
  have hup : directedLabelStepCount n (n + 1)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = b := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := contourWord_upcrossingCount
      (profileList m ++ [b]) chain (n - 1)
    dsimp only [path, values]
    have h' : natStepCount n (n + 1)
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop n).headD 0 := by
      simpa only [show 1 + (n - 1) = n by omega,
        show 1 + (n - 1) + 1 = n + 1 by omega,
        show n - 1 + 1 = n by omega] using h
    rw [h', terminal_drop_headD hn]
  have hreturn : directedLabelStepCount (n + 1) n
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = b := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := contourWord_downcrossingCount
      (profileList m ++ [b]) chain n
    dsimp only [path, values]
    have h' : natStepCount (n + 1) n
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop n).headD 0 := by
      simpa only [show 1 + n = n + 1 by omega,
        show 1 + n - 1 = n by omega,
        show n + 1 - 1 = n by omega] using h
    rw [h', terminal_drop_headD hn]
  let initialValues : List ℕ := 1 :: profileList m
  have hinitialNe : initialValues ≠ [] := by simp [initialValues]
  have hprofileNe : profileList m ≠ [] := by
    simp [profileList]
    omega
  have hinitialLast : initialValues.getLast hinitialNe =
      terminalProfileCount hn m := by
    change (1 :: profileList m).getLast _ = terminalProfileCount hn m
    rw [List.getLast_cons hprofileNe]
    unfold profileList at hprofileNe ⊢
    rw [List.getLast_ofFn]
    unfold terminalProfileCount
    congr 1
  have hinitialLength : initialValues.length = n := by
    simp [initialValues, profileList]
    omega
  have htargetLength : word.2.toList.tail.length = path.length - 1 := by
    have hlen := congrArg List.length hmapped
    simp only [List.length_map, List.length_cons] at hlen
    omega
  have hcontourLength : path.length - 1 = 2 * values.sum - 1 := by
    simpa [path, values] using
      contourWord_length (profileList m ++ [b]) chain
  have hvaluesSum : values.sum = initialValues.sum + b := by
    simp [values, initialValues]
    omega
  have hradial := radialWordLength_add_head_add_last_eq_two_mul_sum
    initialValues hinitialNe
  have hinitialHead : initialValues.head hinitialNe = 1 := by
    simp [initialValues]
  have hpartition := regular_add_terminal_counts_eq_length hn
    (word.2.level ⟨0, by omega⟩) word.2.toList.tail hchain hsources
  have hregular : regularSourceStepCount
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail =
        radialWordLength initialValues := by
    rw [hdown, hup, hreturn, htargetLength] at hpartition
    rw [hinitialHead, hinitialLast] at hradial
    omega
  have hlastLevel : 1 + initialValues.length - 1 = n := by omega
  have hdecision := contourDecisionProduct_append_singleton n b initialValues 1
    hinitialNe hlastLevel
  have hdecision' : contourDecisionProduct n 1 values =
      (1 / 2 : ℝ) ^ radialWordLength initialValues *
        terminalSuccess n ^ terminalProfileCount hn m *
        (1 - terminalSuccess n) ^ b := by
    simpa [values, initialValues, hinitialLast] using hdecision
  have hmass := contourGapChainMass_eq_contourDecisionProduct n 1 values chain
  have href := annularIdealReference_eq_countProduct hn
    (word.2.level ⟨0, by omega⟩) word.2.toList.tail hchain hsources
  change radialChainReference (annularIdealEdge n)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = _
  rw [href, hregular, hdown, hup]
  rw [show contourGapChainMass n 1
      (1 :: (profileList m ++ [b])) chain =
        contourDecisionProduct n 1 values by simpa [values] using hmass]
  rw [hdecision']
  rw [ENNReal.ofReal_mul
      (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (terminalSuccess_pos hn).le _)),
    ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_pow (terminalSuccess_pos hn).le,
    ENNReal.ofReal_pow (sub_nonneg.mpr (terminalSuccess_le_one hn))]

private abbrev SuccessfulContourCode
    (n : ℕ) (delta : ℝ) (m : Profile n) :=
  Σ b : {b : ℕ // b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)},
    GapChain (1 :: (profileList m ++ [b.1]))

private noncomputable def successfulContourCodeWord
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (code : SuccessfulContourCode n delta m) :
    {word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) //
      IsFixedProfileRadialWord n delta m word} :=
  ⟨successfulContourWord hn hdelta hm code.1.1
      (Finset.mem_Icc.mp code.1.2).2 code.2,
    successfulContourWord_isFixed hn hdelta hm code.1.1 code.1.2 code.2⟩

private theorem successfulContourCodeWord_injective
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    Function.Injective (successfulContourCodeWord hn hdelta hm) := by
  rintro ⟨leftB, leftChain⟩ ⟨rightB, rightChain⟩ heq
  have hword := congrArg Subtype.val heq
  have hpaths := congrArg
    (fun word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) ↦
      word.2.toList.map Fin.val) hword
  dsimp only [successfulContourCodeWord] at hpaths
  rw [successfulContourWord_toList_vals,
    successfulContourWord_toList_vals] at hpaths
  have hcount := congrArg (natStepCount n (n + 1)) hpaths
  have hleftCount := contourWord_upcrossingCount
    (profileList m ++ [leftB.1]) leftChain (n - 1)
  have hrightCount := contourWord_upcrossingCount
    (profileList m ++ [rightB.1]) rightChain (n - 1)
  have hleftCount' : natStepCount n (n + 1)
      (contourWord (1 :: (profileList m ++ [leftB.1])) leftChain) =
        leftB.1 := by
    simpa only [show 1 + (n - 1) = n by omega,
      show 1 + (n - 1) + 1 = n + 1 by omega,
      show n - 1 + 1 = n by omega,
      terminal_drop_headD hn] using hleftCount
  have hrightCount' : natStepCount n (n + 1)
      (contourWord (1 :: (profileList m ++ [rightB.1])) rightChain) =
        rightB.1 := by
    simpa only [show 1 + (n - 1) = n by omega,
      show 1 + (n - 1) + 1 = n + 1 by omega,
      show n - 1 + 1 = n by omega,
      terminal_drop_headD hn] using hrightCount
  rw [hleftCount', hrightCount'] at hcount
  have hb : leftB = rightB := Subtype.ext hcount
  subst rightB
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (contourWord_injective (profileList m ++ [leftB.1]) hpaths)

/-- Exact successful-contour enumeration, inserted as a subfamily of all
fixed-profile chronological radial words. -/
theorem ofReal_profile_terminal_mass_le_fixedProfileRadialWord_reference_sum
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    ENNReal.ofReal
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) ≤
      ∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
        radialChainReference (annularIdealEdge n)
          (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail := by
  classical
  let codeWord := successfulContourCodeWord hn hdelta hm
  let referenceMass := fun word : {word : BoundedRadialLabelWord n
      (profileRadialWordMaxTransitions n) //
      IsFixedProfileRadialWord n delta m word} ↦
    radialChainReference (annularIdealEdge n)
      (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail
  have hinjective : Function.Injective codeWord :=
    successfulContourCodeWord_injective hn hdelta hm
  have hinitialPos : ∀ a ∈ (1 :: profileList m), 0 < a := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have htwo := constrainedProfile_all_entries_two_le hdelta hm a ha
      omega
  have hinner (b : {b : ℕ //
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)}) :
      ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
          referenceMass (codeWord ⟨b, chain⟩) =
        ENNReal.ofReal
          (contourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
    calc
      (∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
          referenceMass (codeWord ⟨b, chain⟩)) =
          ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
            ENNReal.ofReal
              (contourGapChainMass n 1
                (1 :: (profileList m ++ [b.1])) chain) := by
        apply Finset.sum_congr rfl
        intro chain _
        simpa [referenceMass, codeWord, successfulContourCodeWord] using
          successfulContourWord_reference_eq_mass hn hdelta hm b.1
            (Finset.mem_Icc.mp b.2).2 chain
      _ = ENNReal.ofReal
          (contourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
        apply sum_ofReal_contourGapChainMass_eq hn
        exact contourSourcesPositive_append_singleton b.1
          (1 :: profileList m) hinitialPos
  have hcodeSum :
      (∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code)) =
        ENNReal.ofReal
          (firstProfileTransitionMass hn m * profileWeight m *
            terminalWindowMass n delta (terminalProfileCount hn m)) := by
    rw [Fintype.sum_sigma]
    calc
      (∑ b : {b : ℕ //
          b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)},
          ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
            referenceMass (codeWord ⟨b, chain⟩)) =
          ∑ b : {b : ℕ //
            b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)},
            ENNReal.ofReal
              (contourTransitionProduct n 1
                (1 :: (profileList m ++ [b.1]))) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hinner b
      _ = ∑ b : {b : ℕ //
            b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)},
            ENNReal.ofReal
              (firstProfileTransitionMass hn m * profileWeight m *
                NegativeBinomial.mass (terminalSuccess n)
                  (terminalProfileCount hn m) b.1) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [contourTransitionProduct_profile_terminal hn hdelta hm]
      _ = ENNReal.ofReal
          (firstProfileTransitionMass hn m * profileWeight m *
            terminalWindowMass n delta (terminalProfileCount hn m)) := by
        let factor := firstProfileTransitionMass hn m * profileWeight m
        have hfactor : 0 ≤ factor := mul_nonneg
          (AppendixFirstMoment.transitionMass_nonneg 1
            (m ⟨0, by omega⟩))
          (profileWeight_nonneg m)
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          rw [← Finset.sum_subtype
            (Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3))
            (fun x ↦ by simp) (fun j ↦ factor *
              NegativeBinomial.mass (terminalSuccess n)
                (terminalProfileCount hn m) j)]
          rw [← Finset.mul_sum]
          rfl
        · intro b _
          exact mul_nonneg hfactor
            (NegativeBinomial.mass_nonneg (terminalSuccess_pos hn).le
              (terminalSuccess_le_one hn) _ _)
  have hsubfamily :
      (∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code)) ≤
        ∑ word : {word : BoundedRadialLabelWord n
            (profileRadialWordMaxTransitions n) //
            IsFixedProfileRadialWord n delta m word},
          referenceMass word := by
    calc
      (∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code)) =
          ∑ word ∈ Finset.univ.image codeWord, referenceMass word := by
        symm
        apply Finset.sum_image
        intro left _ right _ heq
        exact hinjective heq
      _ ≤ ∑ word : {word : BoundedRadialLabelWord n
            (profileRadialWordMaxTransitions n) //
            IsFixedProfileRadialWord n delta m word},
          referenceMass word :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hcodeSum] at hsubfamily
  change ENNReal.ofReal
      (firstProfileTransitionMass hn m *
        terminalWindowMass n delta (terminalProfileCount hn m) *
        profileWeight m) ≤ _
  rw [show firstProfileTransitionMass hn m *
      terminalWindowMass n delta (terminalProfileCount hn m) *
      profileWeight m =
      firstProfileTransitionMass hn m * profileWeight m *
        terminalWindowMass n delta (terminalProfileCount hn m) by ring]
  simpa [referenceMass] using hsubfamily

end

end Erdos1165.AnnularRadialContourMass
