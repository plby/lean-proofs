/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialUpperClassifier
import ErdosProblems.Erdos1165.AnnularFirstLevelProfileRestriction
import ErdosProblems.Erdos1165.AnnularRadialContourUpperMass
import ErdosProblems.Erdos1165.AnnularProfileSequentialUpper
import ErdosProblems.Erdos1165.AnnularShiftedStoppedEvent
import ErdosProblems.Erdos1165.AppendixPairCrossingTail

/-!
# A sequential upper family from the linear radial cover

The upper cover restarts at the actual first entrance of the level-one
boundary.  The entire approach is retained and hence costs at most one; the
fresh segment is one chronological radial-label word, ending at its first
level-zero hit.  In particular, this construction does not use the nested
product of overlapping profile intervals.

This file also packages a literal fixed-profile event as a zero-stage
`SequentialProfileUpperAtom`.  The nontrivial stopping-time disintegration is
performed before that packaging, by the first-level restart theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularRadialSequentialUpperFamily

open AppendixFirstMoment AppendixPairCrossingTail
open AnnularProfileClocks AnnularProfileLiteralAtoms
open AnnularProfileSequentialUpper
open AnnularFirstLevelProfileRestriction
open AnnularRadialChainLower AnnularRadialLabelWord
open AnnularRadialContourSurjection
open AnnularRadialLinearUpper AnnularRadialProfileWords
open AnnularRadialReferenceEdge
open AnnularRadialUpperClassifier AnnularRadialUpperCover
open AnnularShiftedStoppedEvent Proposition13Assembly
open ExcursionTransition NegativeBinomial ProfileSmallBall
open SequentialStoppedAtoms TerminalNegativeBinomialWindow ThickPoint

noncomputable section

theorem stoppedFixedProfileEvent_eq_shiftSteps_preimage
    (start scale : ℕ) (delta : ℝ) (x : Point) (m : Profile scale) :
    stoppedFixedProfileEvent start scale delta x m =
      shiftSteps start ⁻¹'
        stoppedFixedProfileEvent 0 scale delta x m := by
  ext omega
  simp only [stoppedFixedProfileEvent, mem_iUnion, fixedProfileAtEvent,
    mem_ofPred_eq, mem_preimage]
  change (∃ horizon,
      ThickPoint.IsOuterExitTime (trajectory (shiftSteps start omega))
          scale horizon ∧
        x ∈ ThickPoint.candidateBox scale ∧
        FixedSuccessfulProfile scale delta m
          (ThickPoint.excursionProfile
            (trajectory (shiftSteps start omega)) scale horizon x)) ↔
    ∃ horizon,
      ThickPoint.IsOuterExitTime
          (trajectory (shiftSteps 0 (shiftSteps start omega))) scale horizon ∧
        x ∈ ThickPoint.candidateBox scale ∧
        FixedSuccessfulProfile scale delta m
          (ThickPoint.excursionProfile
            (trajectory (shiftSteps 0 (shiftSteps start omega)))
              scale horizon x)
  have hshift : shiftSteps 0 (shiftSteps start omega) =
      shiftSteps start omega := by
    funext q
    simp only [shiftSteps, Nat.zero_add]
  rw [hshift]

theorem fairSteps_stoppedFixedProfileEvent_eq_zero
    (start scale : ℕ) (delta : ℝ) (x : Point) (m : Profile scale) :
    fairSteps (stoppedFixedProfileEvent start scale delta x m) =
      fairSteps (stoppedFixedProfileEvent 0 scale delta x m) := by
  rw [stoppedFixedProfileEvent_eq_shiftSteps_preimage]
  rw [← Measure.map_apply (measurable_shiftSteps start)
    (measurableSet_stoppedFixedProfileEvent 0 scale delta x m),
    fairSteps_map_shiftSteps]

private theorem terminalWindowMass_le_one
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    terminalWindowMass n delta (terminalProfileCount hn m) ≤ 1 := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hi : 0 < terminalProfileCount hn m := by
    have htwo := constrainedProfile_entry_two_le hdelta hm i
    simpa [terminalProfileCount, i] using (show 0 < m i by omega)
  have hsummable := summable_mass (terminalSuccess_pos hn)
    (terminalSuccess_le_one hn) hi
  unfold terminalWindowMass
  calc
    (∑ j ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3),
        mass (terminalSuccess n) (terminalProfileCount hn m) j) ≤
        ∑' j, mass (terminalSuccess n) (terminalProfileCount hn m) j :=
      hsummable.sum_le_tsum _ (fun j _ ↦ mass_nonneg
        (terminalSuccess_pos hn).le (terminalSuccess_le_one hn) _ j)
    _ = 1 := tsum_mass (terminalSuccess_pos hn)
      (terminalSuccess_le_one hn) hi

private theorem exp_one_mul_profile_terminal_mass_le_profileWeight
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    Real.exp 1 *
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) ≤
      profileWeight m := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  have htwo : 2 ≤ m i := constrainedProfile_entry_two_le hdelta hm i
  have hfirst : firstProfileTransitionMass hn m ≤ 1 / 8 := by
    rw [firstProfileTransitionMass, transitionMass_formula (by omega)]
    have hi : m ⟨0, by omega⟩ = m i := rfl
    rw [hi, show 1 + m i - 1 = m i by omega, Nat.choose_self]
    norm_num only [Nat.cast_one, one_mul]
    have hpow : (8 : ℝ) ≤ 2 ^ (m i + 1) := by
      calc
        (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
        _ ≤ 2 ^ (m i + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
    have hden : (0 : ℝ) < 2 ^ (m i + 1) := by positivity
    rw [show 1 + m i = m i + 1 by omega]
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hfirst0 : 0 ≤ firstProfileTransitionMass hn m := by
    unfold firstProfileTransitionMass
    exact transitionMass_nonneg _ _
  have hexpFirst : Real.exp 1 * firstProfileTransitionMass hn m ≤ 1 := by
    calc
      Real.exp 1 * firstProfileTransitionMass hn m ≤
          3 * (1 / 8 : ℝ) :=
        mul_le_mul hexp hfirst hfirst0 (by norm_num)
      _ ≤ 1 := by norm_num
  have hterminal0 : 0 ≤
      terminalWindowMass n delta (terminalProfileCount hn m) :=
    terminalWindowMass_nonneg n delta _
      (terminalSuccess_pos hn).le (terminalSuccess_le_one hn)
  have hterminal1 := terminalWindowMass_le_one hn hdelta hm
  have hweight0 := profileWeight_nonneg m
  calc
    Real.exp 1 *
        (firstProfileTransitionMass hn m *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m) =
        (Real.exp 1 * firstProfileTransitionMass hn m) *
          terminalWindowMass n delta (terminalProfileCount hn m) *
          profileWeight m := by ring
    _ ≤ 1 * 1 * profileWeight m := by
      gcongr
    _ = profileWeight m := by ring

/-- Every literal stopped fixed-profile path is covered after its actual
first level-one entrance by the unrestricted chronological radial-word row.
The arbitrary prefix is retained; only the fresh first-return segment is
classified. -/
theorem stoppedFixedProfileEvent_subset_firstLevelOneRestartEvent
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {x : Point} {m : Profile n} (hm : IsConstrainedProfile delta m) :
    stoppedFixedProfileEvent 0 n delta x m ⊆
      firstLevelOneRestartEvent n x
        (fun z ↦ fixedProfileRadialWordFamilyAtom n delta x z m) := by
  intro omega homega
  obtain ⟨horizon, hexit, hx, hfixed⟩ := mem_iUnion.mp homega
  change IsOuterExitTime (trajectory (shiftSteps 0 omega)) n horizon at hexit
  change FixedSuccessfulProfile n delta m
    (excursionProfile (trajectory (shiftSteps 0 omega)) n horizon x) at hfixed
  have hshiftZero : shiftSteps 0 omega = omega := by
    funext q
    simp [shiftSteps]
  rw [hshiftZero] at hexit hfixed
  have hclock : firstLevelOneEntranceTime n x omega =
      profileInnerHitTime (trajectory omega) n horizon x 1 0 :=
    firstLevelOneEntranceTime_eq_profileInnerHitTime (by omega)
      hexit hx hfixed
  have hfinite : firstLevelOneEntranceTime n x omega < ⊤ := by
    rw [hclock]
    exact WithTop.coe_lt_top _
  refine ⟨hfinite, ?_⟩
  have hstart := stoppedPosition_firstLevelOneEntrance_mem
    (by omega : 1 ≤ n) hexit hx hfixed
  have hfirst := firstLevelOne_fresh_firstLevelZero_profileGapLength
    (by omega : 1 ≤ n) hexit hx hfixed
  have hcoordinates := firstLevelOne_fresh_fixed_coordinates
    hn hexit hx hfixed
  exact mem_fixedProfileRadialWordFamilyAtom_of_firstLevelZero_profileCoordinates
    hn hdelta hm hstart hfirst hcoordinates.1 hcoordinates.2.1
      hcoordinates.2.2

/-- The same first-level restart cover with the exact profile-dependent
cutoff.  No parabolic-window hypothesis is needed for this pathwise
classification. -/
theorem stoppedFixedProfileEvent_subset_exactFirstLevelOneRestartEvent
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ}
    {x : Point} {m : Profile n} :
    stoppedFixedProfileEvent 0 n delta x m ⊆
      firstLevelOneRestartEvent n x
        (fun z ↦ exactFixedProfileRadialWordFamilyAtom
          n delta x z m) := by
  intro omega homega
  obtain ⟨horizon, hexit, hx, hfixed⟩ := mem_iUnion.mp homega
  change IsOuterExitTime (trajectory (shiftSteps 0 omega)) n horizon at hexit
  change FixedSuccessfulProfile n delta m
    (excursionProfile (trajectory (shiftSteps 0 omega)) n horizon x) at hfixed
  have hshiftZero : shiftSteps 0 omega = omega := by
    funext q
    simp [shiftSteps]
  rw [hshiftZero] at hexit hfixed
  have hclock : firstLevelOneEntranceTime n x omega =
      profileInnerHitTime (trajectory omega) n horizon x 1 0 :=
    firstLevelOneEntranceTime_eq_profileInnerHitTime (by omega)
      hexit hx hfixed
  have hfinite : firstLevelOneEntranceTime n x omega < ⊤ := by
    rw [hclock]
    exact WithTop.coe_lt_top _
  refine ⟨hfinite, ?_⟩
  have hstart := stoppedPosition_firstLevelOneEntrance_mem
    (by omega : 1 ≤ n) hexit hx hfixed
  have hfirst := firstLevelOne_fresh_firstLevelZero_profileGapLength
    (by omega : 1 ≤ n) hexit hx hfixed
  have hcoordinates := firstLevelOne_fresh_fixed_coordinates
    hn hexit hx hfixed
  exact
    mem_exactFixedProfileRadialWordFamilyAtom_of_firstLevelZero_profileCoordinates
      hn hstart hfirst hcoordinates.1 hcoordinates.2.1 hcoordinates.2.2

private theorem fixedProfile_measure_le_profileWeight_of_linear_cover
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {x : Point} {m : Profile n} (hm : IsConstrainedProfile delta m)
    (hcover : stoppedFixedProfileEvent 0 n delta x m ⊆
      firstLevelOneRestartEvent n x
        (fun z ↦ fixedProfileRadialWordFamilyAtom n delta x z m))
    (hrow : ∀ z ∈ levelOneInnerBoundary n x,
      fairSteps (fixedProfileRadialWordFamilyAtom n delta x z m) ≤
        ENNReal.ofReal (Real.exp 1) *
          ∑ word : {word : BoundedRadialLabelWord n
              (profileRadialWordMaxTransitions n) //
              IsFixedProfileRadialWord n delta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail)
    (hreference :
      (∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
        radialChainReference (annularIdealEdge n)
          (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) ≤
        ENNReal.ofReal
          (firstProfileTransitionMass hn m *
            terminalWindowMass n delta (terminalProfileCount hn m) *
            profileWeight m)) :
    fairSteps (stoppedFixedProfileEvent 0 n delta x m) ≤
      ENNReal.ofReal (profileWeight m) := by
  let radialMass := firstProfileTransitionMass hn m *
    terminalWindowMass n delta (terminalProfileCount hn m) * profileWeight m
  have hrow' : ∀ z ∈ levelOneInnerBoundary n x,
      fairSteps (fixedProfileRadialWordFamilyAtom n delta x z m) ≤
        ENNReal.ofReal (profileWeight m) := by
    intro z hz
    calc
      fairSteps (fixedProfileRadialWordFamilyAtom n delta x z m) ≤
          ENNReal.ofReal (Real.exp 1) *
            ∑ word : {word : BoundedRadialLabelWord n
                (profileRadialWordMaxTransitions n) //
                IsFixedProfileRadialWord n delta m word},
              radialChainReference (annularIdealEdge n)
                (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail := hrow z hz
      _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal radialMass :=
        by gcongr
      _ = ENNReal.ofReal (Real.exp 1 * radialMass) := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg 1)]
      _ ≤ ENNReal.ofReal (profileWeight m) :=
        ENNReal.ofReal_le_ofReal
          (exp_one_mul_profile_terminal_mass_le_profileWeight
            hn hdelta hm)
  exact (measure_mono hcover).trans
    (fairSteps_firstLevelOneRestartEvent_le
      (fun z ↦ measurableSet_fixedProfileRadialWordFamilyAtom
        n delta x z m)
      hrow')

private def fixedProfileZeroStageUpperAtom
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ}
    {x : Point} {m : Profile scale}
    (hm : IsConstrainedProfile profileDelta m)
    (hhistory : 0 ≤ historyGain)
    (hupper : fairSteps
        (stoppedFixedProfileEvent blockStart scale profileDelta x m) ≤
      ENNReal.ofReal (historyGain * profileWeight m)) :
    SequentialProfileUpperAtom
      blockStart scale profileDelta historyGain x m where
  initial := stoppedFixedProfileEvent blockStart scale profileDelta x m
  tau := fun _ _ ↦ ⊤
  fresh := fun _ _ ↦ ∅
  stages := 0
  valid := fun _ ↦ ∅
  lower := fun _ ↦ 0
  upper := fun _ ↦ 0
  stopping := by intro j hj; omega
  history_measurable := by intro j hj; omega
  finite := by intro j hj; omega
  support := by intro j hj; omega
  fresh_measurable := by intro j hj; omega
  fresh_probability := by intro j hj; omega
  historyGain_nonneg := hhistory
  numerical_upper := by simpa using hupper
  atom_measurable := by
    simpa using measurableSet_stoppedFixedProfileEvent
      blockStart scale profileDelta x m
  atom_subset := by
    simpa using stoppedFixedProfileEvent_subset hm

private def emptyZeroStageUpperAtom
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ}
    {x : Point} {m : Profile scale}
    (hhistory : 0 ≤ historyGain) :
    SequentialProfileUpperAtom
      blockStart scale profileDelta historyGain x m where
  initial := ∅
  tau := fun _ _ ↦ ⊤
  fresh := fun _ _ ↦ ∅
  stages := 0
  valid := fun _ ↦ ∅
  lower := fun _ ↦ 0
  upper := fun _ ↦ 0
  stopping := by intro j hj; omega
  history_measurable := by intro j hj; omega
  finite := by intro j hj; omega
  support := by intro j hj; omega
  fresh_measurable := by intro j hj; omega
  fresh_probability := by intro j hj; omega
  historyGain_nonneg := hhistory
  numerical_upper := by simp
  atom_measurable := MeasurableSet.empty
  atom_subset := empty_subset _

private def zeroStageUpperFamily
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    (hhistory : 0 ≤ historyGain)
    (hupper : ∀ m : Profile scale, IsConstrainedProfile profileDelta m →
      fairSteps (stoppedFixedProfileEvent
          blockStart scale profileDelta x m) ≤
        ENNReal.ofReal (historyGain * profileWeight m)) :
    SequentialProfileUpperFamily
      blockStart scale profileDelta historyGain x := by
  classical
  exact {
    atom := fun m ↦ if hm : IsConstrainedProfile profileDelta m then
        fixedProfileZeroStageUpperAtom hm hhistory (hupper m hm)
      else emptyZeroStageUpperAtom hhistory
    disjoint := by
      intro m hm m' hm' hne
      have hmC := mem_constrainedProfiles.mp hm
      have hm'C := mem_constrainedProfiles.mp hm'
      simp only [dif_pos hmC, dif_pos hm'C,
        SequentialProfileUpperAtom.event, atomEvent_zero,
        fixedProfileZeroStageUpperAtom]
      exact stoppedFixedProfileEvent_disjoint hne
    cover := by
      rw [stoppedSuccessfulPointEvent_eq_iUnion_fixedProfiles]
      congr 1
      funext m
      congr 1
      funext hm
      have hmC := mem_constrainedProfiles.mp hm
      simp only [dif_pos hmC, SequentialProfileUpperAtom.event,
        atomEvent_zero, fixedProfileZeroStageUpperAtom]
  }

/-- Uniform eventual upper bound for one exact stopped profile at time zero.
It is obtained from the actual first-level restart, the linear word row, and
the converse contour enumeration. -/
theorem eventually_fairSteps_stoppedFixedProfileEvent_le_profileWeight :
    ∀ᶠ n : ℕ in atTop, ∀ (delta : ℝ), delta ≤ 1 →
      ∀ (x : Point) (m : Profile n), IsConstrainedProfile delta m →
        fairSteps (stoppedFixedProfileEvent 0 n delta x m) ≤
          ENNReal.ofReal (profileWeight m) := by
  filter_upwards
      [eventually_fairSteps_fixedProfileRadialWordFamilyAtom_le_ideal_sum,
        eventually_ge_atTop 2]
      with n hrow hn
  intro delta hdelta x m hm
  apply fixedProfile_measure_le_profileWeight_of_linear_cover
    hn hdelta hm
  · exact stoppedFixedProfileEvent_subset_firstLevelOneRestartEvent
      hn hdelta hm
  · intro z hz
    exact hrow hn delta x z m (by
      simpa [levelOneInnerBoundary] using hz)
  · exact fixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass
      hn hdelta hm

/-- Exact-profile stopped-event upper bound with the accumulated linear row
cost exposed.  This is the form used when a bounded set of profile
coordinates is deliberately left unrestricted. -/
theorem eventually_fairSteps_stoppedFixedProfileEvent_le_exact_profile_cost :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n)
      (delta : ℝ) (x : Point) (m : Profile n),
      0 < terminalLower n delta →
        fairSteps (stoppedFixedProfileEvent 0 n delta x m) ≤
          ENNReal.ofReal
            ((1 + 1 / (n : ℝ) ^ 4) ^
                exactProfileRadialWordMaxTransitions m *
              (firstProfileTransitionMass hn m *
                terminalWindowMass n delta
                  (terminalProfileCount hn m) *
                profileWeight m)) := by
  filter_upwards
      [eventually_fairSteps_exactFixedProfileRadialWordFamilyAtom_le_ideal_sum,
        eventually_ge_atTop 2]
      with n hrow hn
  intro _ delta x m hlower
  let radialMass := firstProfileTransitionMass hn m *
    terminalWindowMass n delta (terminalProfileCount hn m) * profileWeight m
  let common : ℝ := 1 + 1 / (n : ℝ) ^ 4
  have hreference :
      (∑ word : {word : BoundedRadialLabelWord n
          (exactProfileRadialWordMaxTransitions m) //
          IsFixedProfileRadialWordWithCutoff n
            (exactProfileRadialWordMaxTransitions m) delta m word},
        radialChainReference (annularIdealEdge n)
          (word.1.2.level ⟨0, by omega⟩)
          word.1.2.toList.tail) ≤ ENNReal.ofReal radialMass := by
    exact
      exactFixedProfileRadialWord_reference_sum_le_ofReal_profile_terminal_mass_of_terminalLower_pos
        hn hlower
  have hrow' : ∀ z ∈ levelOneInnerBoundary n x,
      fairSteps (exactFixedProfileRadialWordFamilyAtom n delta x z m) ≤
        ENNReal.ofReal (common ^ exactProfileRadialWordMaxTransitions m *
          radialMass) := by
    intro z hz
    calc
      fairSteps (exactFixedProfileRadialWordFamilyAtom n delta x z m) ≤
          ENNReal.ofReal common ^ exactProfileRadialWordMaxTransitions m *
            ∑ word : {word : BoundedRadialLabelWord n
                (exactProfileRadialWordMaxTransitions m) //
                IsFixedProfileRadialWordWithCutoff n
                  (exactProfileRadialWordMaxTransitions m) delta m word},
              radialChainReference (annularIdealEdge n)
                (word.1.2.level ⟨0, by omega⟩)
                word.1.2.toList.tail :=
        hrow hn delta x z m (by
          simpa [levelOneInnerBoundary] using hz)
      _ ≤ ENNReal.ofReal common ^ exactProfileRadialWordMaxTransitions m *
          ENNReal.ofReal radialMass := by gcongr
      _ = ENNReal.ofReal
          (common ^ exactProfileRadialWordMaxTransitions m * radialMass) := by
        rw [← ENNReal.ofReal_pow (by dsimp only [common]; positivity),
          ENNReal.ofReal_mul (pow_nonneg (by dsimp only [common]; positivity) _)]
  have hcover :=
    stoppedFixedProfileEvent_subset_exactFirstLevelOneRestartEvent
      hn (delta := delta) (x := x) (m := m)
  have hmeasure := (measure_mono hcover).trans
    (fairSteps_firstLevelOneRestartEvent_le
      (fun z ↦ measurableSet_exactFixedProfileRadialWordFamilyAtom
        n delta x z m) hrow')
  simpa [common, radialMass] using hmeasure

/-- The complete disjoint stopped-profile partition as a zero-stage
sequential upper family.  The history factor is exactly the reserve already
budgeted in the pair envelope. -/
theorem eventually_nonempty_sequentialProfileUpperFamily :
    ∀ᶠ n : ℕ in atTop, ∀ (blockStart : ℕ) (profileDelta : ℝ),
      profileDelta ≤ 1 → ∀ x : Point,
        Nonempty (SequentialProfileUpperFamily blockStart n profileDelta
          (Real.exp prefixProfileCostDeficit) x) := by
  filter_upwards
      [eventually_fairSteps_stoppedFixedProfileEvent_le_profileWeight]
      with n hprofile
  intro blockStart profileDelta hdelta x
  refine ⟨zeroStageUpperFamily (Real.exp_nonneg _) ?_⟩
  intro m hm
  have hzero := hprofile profileDelta hdelta x m hm
  have hweight0 := profileWeight_nonneg m
  have hgain : profileWeight m ≤
      Real.exp prefixProfileCostDeficit * profileWeight m := by
    calc
      profileWeight m = 1 * profileWeight m := (one_mul _).symm
      _ ≤ Real.exp prefixProfileCostDeficit * profileWeight m :=
        mul_le_mul_of_nonneg_right
          (Real.one_le_exp prefixProfileCostDeficit_nonneg) hweight0
  calc
    fairSteps (stoppedFixedProfileEvent
        blockStart n profileDelta x m) =
        fairSteps (stoppedFixedProfileEvent 0 n profileDelta x m) :=
      fairSteps_stoppedFixedProfileEvent_eq_zero
        blockStart n profileDelta x m
    _ ≤ ENNReal.ofReal (profileWeight m) := hzero
    _ ≤ ENNReal.ofReal
        (Real.exp prefixProfileCostDeficit * profileWeight m) :=
      ENNReal.ofReal_le_ofReal hgain

/-- Scale-index specialization used by the literal far-pair source package.
The result is uniform in the block number, deterministic block start, and
candidate centre. -/
theorem eventually_nonempty_chosenSequentialProfileUpperFamily
    (delta : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (i : ℕ) (x : Point),
      Nonempty (SequentialProfileUpperFamily
        (i * Proposition13Scales.chosenBlockLength delta N)
        (Proposition13Scales.scaleIndex delta N)
        Proposition13Scales.chosenProfileDelta
        (Real.exp prefixProfileCostDeficit) x) := by
  have hscaleNat : Tendsto
      (Proposition13Scales.scaleIndex delta) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hb := (Proposition13Scales.tendsto_scaleIndex_atTop delta).eventually
      (eventually_ge_atTop (b : ℝ))
    filter_upwards [hb] with N hN
    exact_mod_cast hN
  have hscale := hscaleNat.eventually
    eventually_nonempty_sequentialProfileUpperFamily
  filter_upwards [hscale] with N hN
  intro i x
  exact hN (i * Proposition13Scales.chosenBlockLength delta N)
    Proposition13Scales.chosenProfileDelta (by
    norm_num [Proposition13Scales.chosenProfileDelta]) x

end

end Erdos1165.AnnularRadialSequentialUpperFamily
