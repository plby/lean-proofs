/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialContourSurjection
import ErdosProblems.Erdos1165.ProfileGapChain

/-!
# Exact upper contour mass for chronological radial words

This module combines the converse contour classification with the finite
variable-parameter gap-chain sum.  It gives the missing upper endpoint for the
ideal reference mass of all fixed-profile chronological radial words.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialContourSurjection

open AppendixFirstMoment PathInsertion ProfileGapChain ProfileSmallBall
  AnnularIntegratedProfileKernel AnnularRadialLabelWord
  AnnularRadialProfileWords AnnularRadialChainLower
  AnnularRadialReferenceEdge AnnularRadialContourEnumeration
  AnnularRadialContourMass AnnularIdealReferenceCounts
  TerminalNegativeBinomialWindow ExcursionTransition NegativeBinomial ThickPoint

noncomputable section

private theorem upper_contourForest_one_eq_singleton
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

private theorem upper_contourWord_length
    (tail : List ℕ) (chain : GapChain (1 :: tail)) :
    (contourWord (1 :: tail) chain).length - 1 =
      2 * (1 :: tail).sum - 1 := by
  have h := contourForest_transitionLength 1 (by omega) (1 :: tail) chain
  rw [upper_contourForest_one_eq_singleton] at h
  simpa using h

private theorem upper_contourWord_upcrossingCount
    (tail : List ℕ) (chain : GapChain (1 :: tail)) (offset : ℕ) :
    natStepCount (1 + offset) (1 + offset + 1)
        (contourWord (1 :: tail) chain) =
      ((1 :: tail).drop (offset + 1)).headD 0 := by
  have h := contourForest_upcrossingCount 1 (by omega)
    (1 :: tail) chain offset
  rw [upper_contourForest_one_eq_singleton] at h
  simpa using h

private theorem upper_contourWord_downcrossingCount
    (tail : List ℕ) (chain : GapChain (1 :: tail)) (offset : ℕ) :
    natStepCount (1 + offset) (1 + offset - 1)
        (contourWord (1 :: tail) chain) =
      ((1 :: tail).drop offset).headD 0 := by
  have h := contourForest_downcrossingCount 1 (by omega)
    (1 :: tail) chain offset
  rw [upper_contourForest_one_eq_singleton] at h
  simpa using h

private theorem upper_radialLabelWord_sourcesNonzero
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

private theorem upper_radialLabelWord_toList_isChain
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

private theorem upper_profile_drop_headD
    {n : ℕ} (m : Profile n) (i : Fin (n - 1)) (b : ℕ) :
    ((1 :: (profileList m ++ [b])).drop (i.val + 1)).headD 0 = m i := by
  rw [List.drop_cons (by omega), Nat.add_sub_cancel]
  have hi : i.val < (profileList m).length := by simp [profileList]
  rw [show (profileList m ++ [b]).drop i.val =
      (profileList m ++ [b])[i.val]'(by
        simp only [List.length_append, List.length_singleton]
        omega) ::
        (profileList m ++ [b]).drop (i.val + 1) by
      exact List.drop_eq_getElem_cons (by simp [profileList])]
  simp only [List.headD_cons]
  rw [List.getElem_append_left hi]
  simp [profileList]

private theorem upper_terminal_drop_headD
    {n : ℕ} (hn : 2 ≤ n) (m : Profile n) (b : ℕ) :
    ((1 :: (profileList m ++ [b])).drop n).headD 0 = b := by
  rw [List.drop_cons (by omega)]
  have hlength : (profileList m).length = n - 1 := by simp [profileList]
  rw [show n - 1 = (profileList m).length by exact hlength.symm]
  simp

private def upperContourSuccess (n level : ℕ) : ℝ :=
  if level < n then 1 / 2 else terminalSuccess n

private def upperContourGapChainMass (n : ℕ) :
    (level : ℕ) → (values : List ℕ) → GapChain values → ℝ
  | _, [], _ => 1
  | _, [_], _ => 1
  | level, _a :: b :: rest, chain =>
      (∏ i, geometricOffspringMass (upperContourSuccess n level)
        (gapMultiplicity chain.1 i)) *
        upperContourGapChainMass n (level + 1) (b :: rest) chain.2

/-- The variable-parameter offspring transition, with the same absorbing
zero convention as `transitionMass`. -/
private def upperContourTransitionMass (p : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 then if b = 0 then 1 else 0
  else NegativeBinomial.mass p a b

private def upperContourTransitionProduct (n : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | _, [_] => 1
  | level, a :: b :: rest =>
      upperContourTransitionMass (upperContourSuccess n level) a b *
        upperContourTransitionProduct n (level + 1) (b :: rest)

private def upperContourDecisionProduct (n : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | _, [_] => 1
  | level, a :: b :: rest =>
      upperContourSuccess n level ^ a *
        (1 - upperContourSuccess n level) ^ b *
        upperContourDecisionProduct n (level + 1) (b :: rest)

private def UpperContourSourcesPositive : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => 0 < a ∧ UpperContourSourcesPositive (b :: rest)

private theorem upperContourGapChainMass_eq_decisionProduct
    (n level : ℕ) : ∀ (values : List ℕ) (chain : GapChain values),
    upperContourGapChainMass n level values chain =
      upperContourDecisionProduct n level values
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, chain => by
      simp only [upperContourGapChainMass, upperContourDecisionProduct]
      rw [show (∏ i, geometricOffspringMass (upperContourSuccess n level)
          (gapMultiplicity chain.1 i)) =
          upperContourSuccess n level ^ a *
            (1 - upperContourSuccess n level) ^ b by
        simpa [gapMultiplicity, offspringMultiplicity] using
          prod_geometricOffspringMass (upperContourSuccess n level) chain.1]
      rw [upperContourGapChainMass_eq_decisionProduct n (level + 1)
        (b :: rest) chain.2]

private theorem sum_upperContourOffspringMass
    (p : ℝ) (a b : ℕ) :
    (∑ pattern : GapPattern a b,
        ∏ i, geometricOffspringMass p
          (gapMultiplicity pattern i)) =
      upperContourTransitionMass p a b := by
  by_cases ha : a = 0
  · subst a
    have hterm : ∀ pattern : GapPattern 0 b,
        (∏ i, geometricOffspringMass p
          (gapMultiplicity pattern i)) = 1 := by
      intro pattern
      simp
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, card_gapPattern]
    simp only [nsmul_eq_mul, mul_one, upperContourTransitionMass, if_pos]
    by_cases hb : b = 0
    · subst b
      norm_num
    · rw [if_neg hb]
      norm_cast
      exact Nat.choose_eq_zero_of_lt (by omega)
  · simpa [upperContourTransitionMass, ha, gapMultiplicity,
      offspringMultiplicity] using
      sum_offspringPattern_weight (Nat.pos_of_ne_zero ha) b p

private theorem sum_upperContourGapChainMass_eq_transitionProduct
    (n level : ℕ) : ∀ values : List ℕ,
      ∑ chain : GapChain values, upperContourGapChainMass n level values chain =
        upperContourTransitionProduct n level values
  | [] => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | [_a] => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | a :: b :: rest => by
      change (∑ chain : GapPattern a b × GapChain (b :: rest),
        (∏ i, geometricOffspringMass (upperContourSuccess n level)
          (gapMultiplicity chain.1 i)) *
          upperContourGapChainMass n (level + 1) (b :: rest) chain.2) = _
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [sum_upperContourGapChainMass_eq_transitionProduct n (level + 1)
        (b :: rest)]
      rw [sum_upperContourOffspringMass]
      rfl

private theorem upperContourSuccess_nonneg {n level : ℕ} (hn : 2 ≤ n) :
    0 ≤ upperContourSuccess n level := by
  unfold upperContourSuccess
  split_ifs
  · norm_num
  · exact (terminalSuccess_pos hn).le

private theorem upperContourSuccess_le_one {n level : ℕ} (hn : 2 ≤ n) :
    upperContourSuccess n level ≤ 1 := by
  unfold upperContourSuccess
  split_ifs
  · norm_num
  · exact terminalSuccess_le_one hn

private theorem upperContourGapChainMass_nonneg
    {n level : ℕ} (hn : 2 ≤ n) :
    ∀ {values : List ℕ} (chain : GapChain values),
      0 ≤ upperContourGapChainMass n level values chain
  | [], _ => by simp [upperContourGapChainMass]
  | [_], _ => by simp [upperContourGapChainMass]
  | _a :: b :: rest, chain => by
      apply mul_nonneg
      · apply Finset.prod_nonneg
        intro i _
        unfold geometricOffspringMass
        exact mul_nonneg (upperContourSuccess_nonneg hn)
          (pow_nonneg (sub_nonneg.mpr (upperContourSuccess_le_one hn)) _)
      · exact upperContourGapChainMass_nonneg hn chain.2

private theorem sum_ofReal_upperContourGapChainMass_eq
    {n level : ℕ} (hn : 2 ≤ n) (values : List ℕ) :
    ∑ chain : GapChain values,
        ENNReal.ofReal (upperContourGapChainMass n level values chain) =
      ENNReal.ofReal (upperContourTransitionProduct n level values) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun chain _ ↦ upperContourGapChainMass_nonneg hn chain),
    sum_upperContourGapChainMass_eq_transitionProduct n level values]

private theorem upperContourSourcesPositive_append_singleton (b : ℕ) :
    ∀ (values : List ℕ), (∀ a ∈ values, 0 < a) →
      UpperContourSourcesPositive (values ++ [b])
  | [], _ => by simp [UpperContourSourcesPositive]
  | [a], hpos => by
      exact ⟨hpos a (by simp), by simp [UpperContourSourcesPositive]⟩
  | a :: c :: rest, hpos => by
      refine ⟨hpos a (by simp), ?_⟩
      exact upperContourSourcesPositive_append_singleton b (c :: rest)
        (fun x hx ↦ hpos x (by simp [hx]))

private theorem upperContourTransitionProduct_append_singleton
    (n b : ℕ) : ∀ (values : List ℕ) (level : ℕ)
    (hne : values ≠ [])
    (_hpos : ∀ a ∈ values, 0 < a)
    (_hlastLevel : level + values.length - 1 = n),
    upperContourTransitionProduct n level (values ++ [b]) =
      transitionProduct values *
        NegativeBinomial.mass (terminalSuccess n) (values.getLast hne) b
  | [], _, hne, _, _ => (hne rfl).elim
  | [a], level, _, hpos, hlastLevel => by
      have hlevel : level = n := by simp at hlastLevel; omega
      subst level
      have ha : a ≠ 0 := (hpos a (by simp)).ne'
      simp [upperContourTransitionProduct, upperContourTransitionMass,
        upperContourSuccess, ha]
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
      have ih := upperContourTransitionProduct_append_singleton n b (c :: rest)
        (level + 1) (by simp) htailPos htailLevel
      simp only [List.cons_append, upperContourTransitionProduct]
      rw [upperContourSuccess, if_pos hlevel]
      rw [show upperContourTransitionMass (1 / 2) a c =
          AppendixFirstMoment.transitionMass a c by
        simp [upperContourTransitionMass,
          AppendixFirstMoment.transitionMass, ha.ne']]
      rw [show c :: (rest ++ [b]) = (c :: rest) ++ [b] by rfl]
      rw [ih]
      rw [transitionProduct_cons_cons]
      have hlastEq : (a :: c :: rest).getLast hne =
          (c :: rest).getLast (by simp) := List.getLast_cons (by simp)
      rw [hlastEq]
      ring

private theorem upperContourDecisionProduct_append_singleton
    (n b : ℕ) : ∀ (values : List ℕ) (level : ℕ)
    (hne : values ≠ [])
    (_hlastLevel : level + values.length - 1 = n),
    upperContourDecisionProduct n level (values ++ [b]) =
      (1 / 2 : ℝ) ^ radialWordLength values *
        terminalSuccess n ^ values.getLast hne *
        (1 - terminalSuccess n) ^ b
  | [], _, hne, _ => (hne rfl).elim
  | [a], level, _, hlastLevel => by
      have hlevel : level = n := by simp at hlastLevel; omega
      subst level
      simp [upperContourDecisionProduct, upperContourSuccess, radialWordLength]
  | a :: c :: rest, level, hne, hlastLevel => by
      have hlevel : level < n := by
        simp only [List.length_cons] at hlastLevel
        omega
      have htailLevel : level + 1 + (c :: rest).length - 1 = n := by
        simp only [List.length_cons] at hlastLevel ⊢
        omega
      have ih := upperContourDecisionProduct_append_singleton n b (c :: rest)
        (level + 1) (by simp) htailLevel
      simp only [List.cons_append, upperContourDecisionProduct]
      rw [upperContourSuccess, if_pos hlevel]
      rw [show c :: (rest ++ [b]) = (c :: rest) ++ [b] by rfl, ih]
      have hlastEq : (a :: c :: rest).getLast hne =
          (c :: rest).getLast (by simp) := List.getLast_cons (by simp)
      rw [hlastEq]
      simp only [radialWordLength, pow_add]
      norm_num only [one_div]
      ring

private theorem upper_radialWordLength_add_head_add_last_eq_two_mul_sum :
    ∀ (values : List ℕ) (hne : values ≠ []),
      radialWordLength values + values.head hne + values.getLast hne =
        2 * values.sum
  | [], hne => (hne rfl).elim
  | [a], _ => by simp [radialWordLength]; omega
  | a :: b :: rest, hne => by
      have ih := upper_radialWordLength_add_head_add_last_eq_two_mul_sum
        (b :: rest) (by simp)
      rw [radialWordLength]
      rw [List.getLast_cons (by simp)]
      simp only [List.head_cons, List.sum_cons]
      simp only [List.head_cons, List.sum_cons] at ih
      omega

private theorem upperContourTransitionProduct_profile_terminal_of_pos
    {n : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (hmpos : ∀ a ∈ profileList m, 0 < a) (b : ℕ) :
    upperContourTransitionProduct n 1 (1 :: (profileList m ++ [b])) =
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
    · exact hmpos a ha
  have hlength : values.length = n := by
    simp [values, profileList]
    omega
  have hlastLevel : 1 + values.length - 1 = n := by omega
  have hmain := upperContourTransitionProduct_append_singleton n b values 1
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

private theorem upperContourTransitionProduct_profile_terminal
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) (b : ℕ) :
    upperContourTransitionProduct n 1 (1 :: (profileList m ++ [b])) =
      firstProfileTransitionMass hn m * profileWeight m *
        NegativeBinomial.mass (terminalSuccess n)
          (terminalProfileCount hn m) b := by
  apply upperContourTransitionProduct_profile_terminal_of_pos hn
  intro a ha
  have htwo := constrainedProfile_all_entries_two_le hdelta hm a ha
  omega

private theorem boundedRadialLabelWord_reference_eq_upperMass
    {n cutoff : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (b : ℕ) (chain : GapChain (1 :: (profileList m ++ [b])))
    (word : BoundedRadialLabelWord n cutoff)
    (hword : word.2.toList.map Fin.val =
      contourWord (1 :: (profileList m ++ [b])) chain) :
    radialChainReference (annularIdealEdge n)
        (word.2.level ⟨0, by omega⟩) word.2.toList.tail =
      ENNReal.ofReal
        (upperContourGapChainMass n 1
          (1 :: (profileList m ++ [b])) chain) := by
  let values : List ℕ := 1 :: (profileList m ++ [b])
  let path : List ℕ := contourWord values chain
  have hcons : word.2.level ⟨0, by omega⟩ :: word.2.toList.tail =
      word.2.toList := by
    simp [RadialLabelWord.toList, List.ofFn_succ]
  have hchain : (word.2.level ⟨0, by omega⟩ :: word.2.toList.tail).IsChain
      (fun (left right : Fin (n + 2)) ↦
        Nat.dist (left : ℕ) (right : ℕ) = 1) := by
    rw [hcons]
    exact upper_radialLabelWord_toList_isChain word.2
  have hsources : SourcesNonzero (word.2.level ⟨0, by omega⟩)
      word.2.toList.tail := upper_radialLabelWord_sourcesNonzero word.2
  have hmapped :
      ((word.2.level ⟨0, by omega⟩ :: word.2.toList.tail).map Fin.val) =
        path := by
    rw [hcons]
    simpa [values, path] using hword
  have hdown : directedLabelStepCount n (n - 1)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail =
        terminalProfileCount hn m := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := upper_contourWord_downcrossingCount
      (profileList m ++ [b]) chain (n - 1)
    dsimp only [path, values]
    have h' : natStepCount n (n - 1)
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop (n - 1)).headD 0 := by
      simpa only [show 1 + (n - 1) = n by omega,
        show 1 + (n - 1) - 1 = n - 1 by omega] using h
    rw [h']
    have hp := upper_profile_drop_headD m
      (⟨n - 2, by omega⟩ : Fin (n - 1)) b
    rw [show (n - 2) + 1 = n - 1 by omega] at hp
    simpa [terminalProfileCount] using hp
  have hup : directedLabelStepCount n (n + 1)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = b := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := upper_contourWord_upcrossingCount
      (profileList m ++ [b]) chain (n - 1)
    dsimp only [path, values]
    have h' : natStepCount n (n + 1)
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop n).headD 0 := by
      simpa only [show 1 + (n - 1) = n by omega,
        show 1 + (n - 1) + 1 = n + 1 by omega,
        show n - 1 + 1 = n by omega] using h
    rw [h', upper_terminal_drop_headD hn]
  have hreturn : directedLabelStepCount (n + 1) n
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = b := by
    rw [directedLabelStepCount_eq_natStepCount, hmapped]
    have h := upper_contourWord_downcrossingCount
      (profileList m ++ [b]) chain n
    dsimp only [path, values]
    have h' : natStepCount (n + 1) n
        (contourWord (1 :: (profileList m ++ [b])) chain) =
        ((1 :: (profileList m ++ [b])).drop n).headD 0 := by
      simpa only [show 1 + n = n + 1 by omega,
        show 1 + n - 1 = n by omega,
        show n + 1 - 1 = n by omega] using h
    rw [h', upper_terminal_drop_headD hn]
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
      upper_contourWord_length (profileList m ++ [b]) chain
  have hvaluesSum : values.sum = initialValues.sum + b := by
    simp [values, initialValues]
    omega
  have hradial := upper_radialWordLength_add_head_add_last_eq_two_mul_sum
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
  have hdecision := upperContourDecisionProduct_append_singleton n b
    initialValues 1 hinitialNe hlastLevel
  have hdecision' : upperContourDecisionProduct n 1 values =
      (1 / 2 : ℝ) ^ radialWordLength initialValues *
        terminalSuccess n ^ terminalProfileCount hn m *
        (1 - terminalSuccess n) ^ b := by
    simpa [values, initialValues, hinitialLast] using hdecision
  have hmass := upperContourGapChainMass_eq_decisionProduct
    n 1 values chain
  have href := annularIdealReference_eq_countProduct hn
    (word.2.level ⟨0, by omega⟩) word.2.toList.tail hchain hsources
  change radialChainReference (annularIdealEdge n)
      (word.2.level ⟨0, by omega⟩) word.2.toList.tail = _
  rw [href, hregular, hdown, hup]
  rw [show upperContourGapChainMass n 1
      (1 :: (profileList m ++ [b])) chain =
        upperContourDecisionProduct n 1 values by
      simpa [values] using hmass]
  rw [hdecision']
  rw [ENNReal.ofReal_mul
      (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (terminalSuccess_pos hn).le _)),
    ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_pow (terminalSuccess_pos hn).le,
    ENNReal.ofReal_pow (sub_nonneg.mpr (terminalSuccess_le_one hn))]

private theorem successfulContourWord_reference_eq_upperMass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    radialChainReference (annularIdealEdge n)
        ((successfulContourWord hn hdelta hm b hb chain).2.level
          ⟨0, by omega⟩)
        (successfulContourWord hn hdelta hm b hb chain).2.toList.tail =
      ENNReal.ofReal
        (upperContourGapChainMass n 1
          (1 :: (profileList m ++ [b])) chain) := by
  apply boundedRadialLabelWord_reference_eq_upperMass hn b chain
  exact successfulContourWord_toList_vals hn hdelta hm b hb chain

private theorem exactSuccessfulContourWord_reference_eq_upperMass
    {n : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (b : ℕ) (hb : b ≤ n ^ 3)
    (chain : GapChain (1 :: (profileList m ++ [b]))) :
    radialChainReference (annularIdealEdge n)
        ((exactSuccessfulContourWord hn b hb chain).2.level
          ⟨0, by omega⟩)
        (exactSuccessfulContourWord hn b hb chain).2.toList.tail =
      ENNReal.ofReal
        (upperContourGapChainMass n 1
          (1 :: (profileList m ++ [b])) chain) := by
  apply boundedRadialLabelWord_reference_eq_upperMass hn b chain
  exact exactSuccessfulContourWord_toList_vals hn b hb chain

/-- The ideal reference sum over all fixed-profile chronological radial words
is at most the exact profile transition mass times the terminal-window mass.
Together with the contour subfamily lower bound, this identifies the sum
exactly. -/
theorem fixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    (∑ word : {word : BoundedRadialLabelWord n
        (profileRadialWordMaxTransitions n) //
        IsFixedProfileRadialWord n delta m word},
      radialChainReference (annularIdealEdge n)
        (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) ≤
      ENNReal.ofReal
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) := by
  classical
  let codeWord := successfulContourCodeWord hn hdelta hm
  let wordCode := fixedProfileRadialWordContourCode hn hdelta hm
  let referenceMass := fun word : {word : BoundedRadialLabelWord n
      (profileRadialWordMaxTransitions n) //
      IsFixedProfileRadialWord n delta m word} ↦
    radialChainReference (annularIdealEdge n)
      (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail
  have hright : ∀ word, codeWord (wordCode word) = word := by
    intro word
    exact successfulContourCodeWord_fixedProfileRadialWordContourCode
      hn hdelta hm word
  have hinjective : Function.Injective wordCode :=
    fixedProfileRadialWordContourCode_injective hn hdelta hm
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
          (upperContourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
    calc
      (∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
          referenceMass (codeWord ⟨b, chain⟩)) =
          ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
            ENNReal.ofReal
              (upperContourGapChainMass n 1
                (1 :: (profileList m ++ [b.1])) chain) := by
        apply Finset.sum_congr rfl
        intro chain _
        simpa [referenceMass, codeWord, successfulContourCodeWord] using
          successfulContourWord_reference_eq_upperMass hn hdelta hm b.1
            (Finset.mem_Icc.mp b.2).2 chain
      _ = ENNReal.ofReal
          (upperContourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
        exact sum_ofReal_upperContourGapChainMass_eq hn _
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
              (upperContourTransitionProduct n 1
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
        rw [upperContourTransitionProduct_profile_terminal hn hdelta hm]
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
  have hwordSum :
      (∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
          referenceMass word) ≤
        ∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code) := by
    calc
      (∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
          referenceMass word) =
          ∑ word : {word : BoundedRadialLabelWord n
            (profileRadialWordMaxTransitions n) //
            IsFixedProfileRadialWord n delta m word},
            referenceMass (codeWord (wordCode word)) := by
        apply Finset.sum_congr rfl
        intro word _
        rw [hright]
      _ = ∑ code ∈ Finset.univ.image wordCode,
            referenceMass (codeWord code) := by
        symm
        apply Finset.sum_image
        intro left _ right _ heq
        exact hinjective heq
      _ ≤ ∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hcodeSum] at hwordSum
  change _ ≤ ENNReal.ofReal
      (firstProfileTransitionMass hn m *
        terminalWindowMass n delta (terminalProfileCount hn m) *
        profileWeight m)
  rw [show firstProfileTransitionMass hn m *
      terminalWindowMass n delta (terminalProfileCount hn m) *
      profileWeight m =
      firstProfileTransitionMass hn m * profileWeight m *
        terminalWindowMass n delta (terminalProfileCount hn m) by ring]
  simpa [referenceMass] using hwordSum

/-- The ideal reference sum for an arbitrary positive exact profile, in its
profile-dependent finite cutoff, is at most the corresponding transition
mass times the terminal-window mass. -/
theorem exactFixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {m : Profile n}
    (hmpos : ∀ a ∈ profileList m, 0 < a) :
    (∑ word : {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
        IsFixedProfileRadialWordWithCutoff n
          (exactProfileRadialWordMaxTransitions m) delta m word},
      radialChainReference (annularIdealEdge n)
        (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) ≤
      ENNReal.ofReal
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) := by
  classical
  let codeWord := exactSuccessfulContourCodeWord hn
    (delta := delta) (m := m)
  let wordCode := exactFixedProfileRadialWordContourCode hn
    (delta := delta) (m := m)
  let referenceMass := fun word : {word : BoundedRadialLabelWord n
      (exactProfileRadialWordMaxTransitions m) //
      IsFixedProfileRadialWordWithCutoff n
        (exactProfileRadialWordMaxTransitions m) delta m word} ↦
    radialChainReference (annularIdealEdge n)
      (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail
  have hright : ∀ word, codeWord (wordCode word) = word := by
    intro word
    exact exactSuccessfulContourCodeWord_exactFixedProfileRadialWordContourCode
      hn word
  have hinjective : Function.Injective wordCode :=
    exactFixedProfileRadialWordContourCode_injective hn
  have hinitialPos : ∀ a ∈ (1 :: profileList m), 0 < a := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · exact hmpos a ha
  have hinner (b : {b : ℕ //
      b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3)}) :
      ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
          referenceMass (codeWord ⟨b, chain⟩) =
        ENNReal.ofReal
          (upperContourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
    calc
      (∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
          referenceMass (codeWord ⟨b, chain⟩)) =
          ∑ chain : GapChain (1 :: (profileList m ++ [b.1])),
            ENNReal.ofReal
              (upperContourGapChainMass n 1
                (1 :: (profileList m ++ [b.1])) chain) := by
        apply Finset.sum_congr rfl
        intro chain _
        simpa [referenceMass, codeWord, exactSuccessfulContourCodeWord] using
          exactSuccessfulContourWord_reference_eq_upperMass hn b.1
            (Finset.mem_Icc.mp b.2).2 chain
      _ = ENNReal.ofReal
          (upperContourTransitionProduct n 1
            (1 :: (profileList m ++ [b.1]))) := by
        exact sum_ofReal_upperContourGapChainMass_eq hn _
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
              (upperContourTransitionProduct n 1
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
        rw [upperContourTransitionProduct_profile_terminal_of_pos hn hmpos]
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
  have hwordSum :
      (∑ word : {word : BoundedRadialLabelWord n
          (exactProfileRadialWordMaxTransitions m) //
          IsFixedProfileRadialWordWithCutoff n
            (exactProfileRadialWordMaxTransitions m) delta m word},
          referenceMass word) ≤
        ∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code) := by
    calc
      (∑ word : {word : BoundedRadialLabelWord n
          (exactProfileRadialWordMaxTransitions m) //
          IsFixedProfileRadialWordWithCutoff n
            (exactProfileRadialWordMaxTransitions m) delta m word},
          referenceMass word) =
          ∑ word : {word : BoundedRadialLabelWord n
            (exactProfileRadialWordMaxTransitions m) //
            IsFixedProfileRadialWordWithCutoff n
              (exactProfileRadialWordMaxTransitions m) delta m word},
            referenceMass (codeWord (wordCode word)) := by
        apply Finset.sum_congr rfl
        intro word _
        rw [hright]
      _ = ∑ code ∈ Finset.univ.image wordCode,
            referenceMass (codeWord code) := by
        symm
        apply Finset.sum_image
        intro left _ right _ heq
        exact hinjective heq
      _ ≤ ∑ code : SuccessfulContourCode n delta m,
          referenceMass (codeWord code) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hcodeSum] at hwordSum
  change _ ≤ ENNReal.ofReal
      (firstProfileTransitionMass hn m *
        terminalWindowMass n delta (terminalProfileCount hn m) *
        profileWeight m)
  rw [show firstProfileTransitionMass hn m *
      terminalWindowMass n delta (terminalProfileCount hn m) *
      profileWeight m =
      firstProfileTransitionMass hn m * profileWeight m *
        terminalWindowMass n delta (terminalProfileCount hn m) by ring]
  simpa [referenceMass] using hwordSum

/-- The same exact-profile upper bound without a positivity hypothesis.
When the terminal window is strictly positive, any chronological contour
reaching that window forces every preceding profile count to be positive;
otherwise the fixed-profile word family is empty. -/
theorem exactFixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass_of_terminalLower_pos
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hlower : 0 < terminalLower n delta)
    {m : Profile n} :
    (∑ word : {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
        IsFixedProfileRadialWordWithCutoff n
          (exactProfileRadialWordMaxTransitions m) delta m word},
      radialChainReference (annularIdealEdge n)
        (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) ≤
      ENNReal.ofReal
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) := by
  classical
  by_cases hmpos : ∀ a ∈ profileList m, 0 < a
  · exact
      exactFixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass
        hn hmpos
  · have hempty : ∀ word : {word : BoundedRadialLabelWord n
        (exactProfileRadialWordMaxTransitions m) //
        IsFixedProfileRadialWordWithCutoff n
          (exactProfileRadialWordMaxTransitions m) delta m word}, False := by
      intro word
      let code := exactFixedProfileRadialWordContourCode hn word
      have hbLower := (Finset.mem_Icc.mp code.1.2).1
      have hceil : 0 < ⌈terminalLower n delta⌉₊ := Nat.ceil_pos.mpr hlower
      have hb : 0 < code.1.1 := by omega
      have hlast : 0 <
          (1 :: (profileList m ++ [code.1.1])).getLast (by simp) := by
        simpa using hb
      have hall := gapChain_all_positive_of_last_positive
        1 (profileList m ++ [code.1.1]) code.2 hlast
      apply hmpos
      intro a ha
      exact hall a (by simp [ha])
    calc
      (∑ word : {word : BoundedRadialLabelWord n
          (exactProfileRadialWordMaxTransitions m) //
          IsFixedProfileRadialWordWithCutoff n
            (exactProfileRadialWordMaxTransitions m) delta m word},
        radialChainReference (annularIdealEdge n)
          (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) = 0 := by
        apply Finset.sum_eq_zero
        intro word _
        exact (hempty word).elim
      _ ≤ ENNReal.ofReal
          (firstProfileTransitionMass hn m *
            terminalWindowMass n delta (terminalProfileCount hn m) *
            profileWeight m) := bot_le

/-- Exact finite ideal-reference enumeration of all fixed-profile radial
words. -/
theorem fixedProfileRadialWord_reference_sum_eq_ofReal_profile_terminal_mass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    (∑ word : {word : BoundedRadialLabelWord n
        (profileRadialWordMaxTransitions n) //
        IsFixedProfileRadialWord n delta m word},
      radialChainReference (annularIdealEdge n)
        (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) =
      ENNReal.ofReal
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) := by
  apply le_antisymm
  · exact fixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass
      hn hdelta hm
  · exact
      ofReal_profile_terminal_mass_le_fixedProfileRadialWord_reference_sum
        hn hdelta hm

end

end Erdos1165.AnnularRadialContourSurjection
