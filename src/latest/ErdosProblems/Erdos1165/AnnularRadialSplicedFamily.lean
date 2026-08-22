/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialReferenceEdge
import ErdosProblems.Erdos1165.AnnularRadialSplicedPathwise
import ErdosProblems.Erdos1165.AnnularSpatialSpliceKernel
import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms

/-!
# Fixed-profile families of spatially spliced radial words

This module performs the finite disjoint union over all chronological radial
words carrying one fixed profile.  It retains the literal initial and final
spatial pieces, so the resulting mass estimate can be inserted directly into
the stopped successful-point event.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialSplicedFamily

open AnnularRadialChainLower AnnularRadialLabelWord
  AnnularRadialBoundaryEnumeration
  AppendixFirstMoment
  AnnularRadialProfileWords AnnularRadialReferenceEdge
  AnnularRadialSplicedChain AnnularRadialSplicedPathwise
  AnnularProfileLiteralAtoms
  AnnularSpatialSpliceKernel AnnularSpatialSpliceKernelDefs
  MarkedBoundaryVisitKernel MarkedBridgeFactorization PlanarPotential
  Proposition13Assembly ThickPoint
  TerminalSequentialVisitLaw

noncomputable section

/-- The complete initial/radial/final event, unioned over all bounded words
with the prescribed internal profile and terminal count window. -/
def fixedProfileSplicedRadialFamilyAtom
    (n : ℕ) (delta : ℝ) (x : Point) (m : Profile n) : Set StepPath :=
  ⋃ word : {word : BoundedRadialLabelWord n
      (profileRadialWordMaxTransitions n) //
      IsFixedProfileRadialWord n delta m word},
    spatiallySplicedRadialWordAtom x word.1.2

theorem measurableSet_spatiallySplicedRadialWordAtom
    {n L : ℕ} (x : Point) (word : RadialLabelWord n L) :
    MeasurableSet (spatiallySplicedRadialWordAtom x word) := by
  rw [spatiallySplicedRadialWordAtom, spatiallySplicedRadialChainAtom]
  apply MeasurableSet.iUnion
  intro endpoint
  exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
    ((measurableSet_radialChainFinalAtom n 0
      (fun z ↦ measurableSet_boundaryExitMarkedSteps _ _ z)
      ⟨1, by omega⟩ word.toList.tail endpoint.1).preimage
        (measurable_postWithTopStoppingSteps
          (isStoppingTime_boundaryExitTime (initialSpliceBoundary n) (-x))))

theorem measurableSet_fixedProfileSplicedRadialFamilyAtom
    (n : ℕ) (delta : ℝ) (x : Point) (m : Profile n) :
    MeasurableSet (fixedProfileSplicedRadialFamilyAtom n delta x m) := by
  apply MeasurableSet.iUnion
  intro word
  exact measurableSet_spatiallySplicedRadialWordAtom x word.1.2

/-- Different bounded chronological words remain disjoint after adjoining
the common initial hit and endpoint-dependent final escape. -/
theorem pairwise_disjoint_spatiallySplicedRadialWordAtom
    {n maxTransitions : ℕ} (hn : 2 ≤ n) (x : Point) :
    Pairwise fun left right : BoundedRadialLabelWord n maxTransitions ↦
      Disjoint (spatiallySplicedRadialWordAtom x left.2)
        (spatiallySplicedRadialWordAtom x right.2) := by
  rintro ⟨leftLength, left⟩ ⟨rightLength, right⟩ hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  obtain ⟨leftInitial, leftRadial, _leftFinal, leftEntrance, _leftZero,
      hleftInitial, hleftEntrance, _hleftBoundary, hleftRadial,
      _hleftZero, hleftTrace, _hleftFinal⟩ :=
    spatiallySplicedRadialWordAtom_pathwise hn x left hleft
  obtain ⟨rightInitial, rightRadial, _rightFinal, rightEntrance, _rightZero,
      hrightInitial, hrightEntrance, _hrightBoundary, hrightRadial,
      _hrightZero, hrightTrace, _hrightFinal⟩ :=
    spatiallySplicedRadialWordAtom_pathwise hn x right hright
  have hinitial : leftInitial = rightInitial :=
    absoluteBoundaryFirstAt_unique hleftInitial hrightInitial
  subst rightInitial
  have hentrance : leftEntrance = rightEntrance := by
    rw [← hleftEntrance, ← hrightEntrance]
  have hradial : leftRadial = rightRadial :=
    absoluteBoundaryFirstAt_unique hleftRadial (by simpa [← hentrance] using hrightRadial)
  subst rightRadial
  have hlist : left.toList = right.toList := by
    rw [← hleftTrace, ← hrightTrace, hentrance]
  have hlengthNat : (leftLength : ℕ) = (rightLength : ℕ) := by
    have h := congrArg List.length hlist
    simp only [RadialLabelWord.length_toList] at h
    omega
  have hlength : leftLength = rightLength := Fin.ext hlengthNat
  subst rightLength
  have hword : left = right := by
    apply RadialLabelWord.ext
    apply List.ofFn_injective
    exact hlist
  subst right
  exact hne rfl

/-- Exact finite disjoint-sum formula for the complete fixed-profile family. -/
theorem fairSteps_fixedProfileSplicedRadialFamilyAtom
    {n : ℕ} (hn : 2 ≤ n) (delta : ℝ) (x : Point) (m : Profile n) :
    fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m) =
      ∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
        fairSteps (spatiallySplicedRadialWordAtom x word.1.2) := by
  rw [fixedProfileSplicedRadialFamilyAtom, measure_iUnion]
  · exact tsum_fintype _
  · intro left right hne
    exact pairwise_disjoint_spatiallySplicedRadialWordAtom hn x
      (fun heq ↦ hne (Subtype.ext heq))
  · intro word
    exact measurableSet_spatiallySplicedRadialWordAtom x word.1.2

private theorem word_tail_getLast?_eq_zero
    {n L : ℕ} (word : RadialLabelWord n L) :
    word.toList.tail.getLast? = some ⟨0, by omega⟩ := by
  have hL : 0 < L := by
    by_contra hnot
    have hzero : L = 0 := by omega
    subst L
    have hindex : (⟨0, by omega⟩ : Fin (0 + 1)) = Fin.last 0 := by ext <;> rfl
    have hbad := word.startsAtOne.symm.trans
      ((congrArg word.level hindex).trans word.endsAtZero)
    have := congrArg Fin.val hbad
    norm_num at this
  rw [List.getLast?_tail, if_neg]
  · have hwordNe : word.toList ≠ [] := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp only [RadialLabelWord.length_toList, List.length_nil] at hlength
      omega
    have hfnNe : List.ofFn word.level ≠ [] := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp only [List.length_ofFn, List.length_nil] at hlength
      omega
    have hlast : word.toList.getLast hwordNe = ⟨0, by omega⟩ := by
      calc
        word.toList.getLast hwordNe =
            (List.ofFn word.level).getLast hfnNe :=
          List.getLast_congr hwordNe hfnNe rfl
        _ = ⟨0, by omega⟩ := by
          rw [List.getLast_ofFn]
          exact word.endsAtZero
    rw [List.getLast?_eq_some_getLast hwordNe, hlast]
  · simp only [RadialLabelWord.length_toList]
    omega

/-- Per-word lower bound for the literal three-piece splice. -/
theorem spatiallySplicedRadialWordAtom_lower
    {n : ℕ} (hn : 5 ≤ n) {x : Point}
    (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n))
    (hinitial : (1 / 128 : ℝ≥0∞) ≤
      ∑ z : RadialBoundaryPoint n 0 ⟨1, by omega⟩,
        skeletonExitKernel (initialSpliceBoundary n) (-x) z.1)
    (hrow : ∀ left right : Fin (n + 2), ∀ start : Point,
      start ∈ radialBoundary n 0 left →
        annularLowerEdge n left right ≤
          ∑ endpoint : RadialBoundaryPoint n 0 right,
            skeletonExitKernel (otherRadialBoundaries n 0 left)
              start endpoint.1)
    (hfinal : ∀ z : Point, z ∈ radialBoundary n 0 ⟨0, by omega⟩ →
      (1 / 128 : ℝ≥0∞) ≤ fairSteps (finalSpliceEvent n z)) :
    (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
          radialChainReference (annularIdealEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail *
        (1 / 128 : ℝ≥0∞) ≤
      fairSteps (spatiallySplicedRadialWordAtom x word.2) := by
  have hcompare := ofReal_half_mul_idealReference_le_lowerReference hn
    word
  have hsplice := initial_mul_reference_mul_final_le_splicedMass
    (n := n) 0 (-x) (initialSpliceBoundary n) ⟨1, by omega⟩
      word.2.toList.tail (fun z ↦ measurableSet_boundaryExitMarkedSteps _ _ z)
      (annularLowerEdge n) (1 / 128) (1 / 128) hinitial hrow hfinal
      (word_tail_getLast?_eq_zero word.2)
  have hcompare' : (1 / 2 : ℝ≥0∞) *
        radialChainReference (annularIdealEdge n)
          (word.2.level ⟨0, by omega⟩) word.2.toList.tail ≤
      radialChainReference (annularLowerEdge n)
        (word.2.level ⟨0, by omega⟩) word.2.toList.tail := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rwa [hhalf] at hcompare
  change _ ≤ fairSteps
    (spatiallySplicedRadialChainAtom n 0 (-x) (initialSpliceBoundary n)
      ⟨1, by omega⟩ word.2.toList.tail
        (fun z ↦ boundaryExitMarkedSteps (finalSpliceBoundary n)
          (discBoundary 0 (32 * scaleRadius n 0)) z))
  calc
    (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
          radialChainReference (annularIdealEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail *
        (1 / 128 : ℝ≥0∞) ≤
      (1 / 128 : ℝ≥0∞) *
          radialChainReference (annularLowerEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail *
        (1 / 128 : ℝ≥0∞) := by
      calc
        _ = (1 / 128 : ℝ≥0∞) *
              ((1 / 2 : ℝ≥0∞) *
                radialChainReference (annularIdealEdge n)
                  (word.2.level ⟨0, by omega⟩) word.2.toList.tail) *
              (1 / 128 : ℝ≥0∞) := by ac_rfl
        _ ≤ _ := mul_le_mul
          (mul_le_mul le_rfl hcompare' bot_le bot_le) le_rfl bot_le bot_le
    _ ≤ _ := by
      simpa only [word.2.startsAtOne] using hsplice

/-- Uniform eventual lower bound for the complete fixed-profile family,
still expressed as the ideal finite word-reference sum. -/
theorem eventually_fixedProfile_reference_sum_le_spliced_family :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 5 ≤ n) (delta : ℝ)
      (x : Point), x ∈ candidateBox n → ∀ m : Profile n,
      (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
          (∑ word : {word : BoundedRadialLabelWord n
              (profileRadialWordMaxTransitions n) //
              IsFixedProfileRadialWord n delta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) *
          (1 / 128 : ℝ≥0∞) ≤
        fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m) := by
  filter_upwards [eventually_one_div_128_le_initial_endpoint_sum,
    eventually_one_div_128_le_finalSpliceEvent,
    eventually_annularLowerEdge_le_endpoint_sum] with n hinitial hfinal hrow
  intro hn delta x hx m
  have hinitial' : (1 / 128 : ℝ≥0∞) ≤
      ∑ z : RadialBoundaryPoint n 0 ⟨1, by omega⟩,
        skeletonExitKernel (initialSpliceBoundary n) (-x) z.1 := by
    rw [AnnularRadialBoundaryEnumeration.sum_radialBoundaryPoint_eq_marked]
    simpa only [radialBoundary] using hinitial x hx
  rw [fairSteps_fixedProfileSplicedRadialFamilyAtom (by omega) delta x m]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun word _ ↦
    spatiallySplicedRadialWordAtom_lower hn word.1
      hinitial' (hrow (by omega) 0) (hfinal x hx)

/-! ## Finite union over constrained internal profiles -/

/-- The selected three-piece event unioned over every constrained internal
profile. -/
def constrainedProfileSplicedRadialFamilyAtom
    (n : ℕ) (delta : ℝ) (x : Point) : Set StepPath :=
  ⋃ m : {m : Profile n // m ∈ constrainedProfiles n delta},
    fixedProfileSplicedRadialFamilyAtom n delta x m.1

theorem measurableSet_constrainedProfileSplicedRadialFamilyAtom
    (n : ℕ) (delta : ℝ) (x : Point) :
    MeasurableSet (constrainedProfileSplicedRadialFamilyAtom n delta x) := by
  apply MeasurableSet.iUnion
  intro m
  exact measurableSet_fixedProfileSplicedRadialFamilyAtom n delta x m.1

/-- Fixed-profile containment makes the selected profile families disjoint,
because the literal stopped fixed-profile atoms are disjoint. -/
theorem fairSteps_constrainedProfileSplicedRadialFamilyAtom
    {n : ℕ} (delta : ℝ) (x : Point)
    (hsubset : ∀ m : {m : Profile n // m ∈ constrainedProfiles n delta},
      fixedProfileSplicedRadialFamilyAtom n delta x m.1 ⊆
        stoppedFixedProfileEvent 0 n delta x m.1) :
    fairSteps (constrainedProfileSplicedRadialFamilyAtom n delta x) =
      ∑ m : {m : Profile n // m ∈ constrainedProfiles n delta},
        fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m.1) := by
  rw [constrainedProfileSplicedRadialFamilyAtom, measure_iUnion]
  · exact tsum_fintype _
  · intro left right hne
    exact (stoppedFixedProfileEvent_disjoint
      (fun heq ↦ hne (Subtype.ext heq))).mono
        (hsubset left) (hsubset right)
  · intro m
    exact measurableSet_fixedProfileSplicedRadialFamilyAtom n delta x m.1

theorem constrainedProfileSplicedRadialFamilyAtom_subset_success
    {n : ℕ} {delta : ℝ} {x : Point}
    (hsubset : ∀ m : {m : Profile n // m ∈ constrainedProfiles n delta},
      fixedProfileSplicedRadialFamilyAtom n delta x m.1 ⊆
        stoppedFixedProfileEvent 0 n delta x m.1) :
    constrainedProfileSplicedRadialFamilyAtom n delta x ⊆
      stoppedSuccessfulPointEvent 0 n delta x := by
  intro omega homega
  obtain ⟨m, homega⟩ := Set.mem_iUnion.mp homega
  exact stoppedFixedProfileEvent_subset
    (mem_constrainedProfiles.mp m.2) (hsubset m homega)

/-- The literal pathwise splice theorem supplies the fixed-profile
containment required by the finite profile union. -/
theorem fixedProfileSplicedRadialFamilyAtom_subset_stoppedFixedProfileEvent
    {n : ℕ} (hn : 3 ≤ n) {delta : ℝ} {x : Point}
    (hx : x ∈ candidateBox n) (m : Profile n) :
    fixedProfileSplicedRadialFamilyAtom n delta x m ⊆
      stoppedFixedProfileEvent 0 n delta x m := by
  intro omega homega
  obtain ⟨word, homega⟩ := Set.mem_iUnion.mp homega
  exact spatiallySplicedRadialWordAtom_subset_stoppedFixedProfileEvent
    hn hx word.1 word.2 homega

theorem constrainedProfileSplicedRadialFamilyAtom_subset_stoppedSuccess
    {n : ℕ} (hn : 3 ≤ n) {delta : ℝ} {x : Point}
    (hx : x ∈ candidateBox n) :
    constrainedProfileSplicedRadialFamilyAtom n delta x ⊆
      stoppedSuccessfulPointEvent 0 n delta x := by
  apply constrainedProfileSplicedRadialFamilyAtom_subset_success
  intro m
  exact fixedProfileSplicedRadialFamilyAtom_subset_stoppedFixedProfileEvent
    hn hx m.1

theorem fairSteps_constrainedProfileSplicedRadialFamilyAtom_eq_sum
    {n : ℕ} (hn : 3 ≤ n) (delta : ℝ) {x : Point}
    (hx : x ∈ candidateBox n) :
    fairSteps (constrainedProfileSplicedRadialFamilyAtom n delta x) =
      ∑ m : {m : Profile n // m ∈ constrainedProfiles n delta},
        fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m.1) := by
  apply fairSteps_constrainedProfileSplicedRadialFamilyAtom delta x
  intro m
  exact fixedProfileSplicedRadialFamilyAtom_subset_stoppedFixedProfileEvent
    hn hx m.1

end

end Erdos1165.AnnularRadialSplicedFamily
