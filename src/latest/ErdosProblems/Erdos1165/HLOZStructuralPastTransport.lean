/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceStructuralPastInvariant
import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeProp49Family
import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift

/-!
# Transport of structural pasts

The low-gap-only rank pasts commute with the column reflection.  Checker
recentering is handled separately under its exact origin-safety condition.
-/

open Set

namespace Erdos1165.HLOZStructuralPastTransport

open HLOZNoLazyFilteredTransitions HLOZPathEvents
open HLOZCheckerOriginSafeProp49Family
open HLOZSpatialAdapter VariableStoppedTracePartition
open HLOZSourceStructuralPastInvariant HLOZThetaOneSourceShift

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

theorem latticeDistance_horizontalReflectPoint (x y : Point) :
    latticeDistance (horizontalReflectPoint x) (horizontalReflectPoint y) =
      latticeDistance x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [latticeDistance, horizontalReflectPoint]
  congr 1
  norm_num
  ring

theorem gapScaleOf_horizontalReflectPoint (m : ℕ) (x y : Point) :
    gapScaleOf m (horizontalReflectPoint x) (horizontalReflectPoint y) =
      gapScaleOf m x y := by
  have heq : HasProperGapScale m (horizontalReflectPoint x)
      (horizontalReflectPoint y) = HasProperGapScale m x y := by
    apply propext
    simp only [HasProperGapScale, latticeDistance_horizontalReflectPoint]
  unfold gapScaleOf
  split <;> split
  · rename_i hreflect hplain
    have hfind : Nat.find hreflect = Nat.find hplain := by
      apply Nat.find_congr'
      intro i
      simp only [HasProperGapScale] at hreflect hplain ⊢
      rw [latticeDistance_horizontalReflectPoint]
    apply Fin.ext
    exact hfind
  · rename_i hreflect hplain
    exfalso
    exact hplain (heq.mp hreflect)
  · rename_i hreflect hplain
    exfalso
    exact hreflect (heq.mpr hplain)
  · rfl

theorem latticeDistance_sub_right (x y z : Point) :
    latticeDistance (x - z) (y - z) = latticeDistance x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp only [latticeDistance, Prod.fst_sub, Prod.snd_sub]
  congr 1 <;> ring_nf

theorem gapScaleOf_sub_right (m : ℕ) (x y z : Point) :
    gapScaleOf m (x - z) (y - z) = gapScaleOf m x y := by
  have heq : HasProperGapScale m (x - z) (y - z) =
      HasProperGapScale m x y := by
    apply propext
    simp only [HasProperGapScale, latticeDistance_sub_right]
  unfold gapScaleOf
  split <;> split
  · rename_i hshift hplain
    have hfind : Nat.find hshift = Nat.find hplain := by
      apply Nat.find_congr'
      intro i
      simp only [HasProperGapScale] at hshift hplain ⊢
      rw [latticeDistance_sub_right]
    apply Fin.ext
    exact hfind
  · rename_i hshift hplain
    exact (hplain (heq.mp hshift)).elim
  · rename_i hshift hplain
    exact (hshift (heq.mpr hplain)).elim
  · rfl

theorem oneStepRecenter_point_eq_sub (omega : StepPath) (n : ℕ) :
    oneStepRecenter (trajectory omega) n =
      trajectory omega (n + 1) - trajectory omega 1 := by
  exact (eq_sub_iff_add_eq).2 (oneStepRecenter_add_first omega n)

theorem lowGapDeficitFailure_oneStepRecenter_iff
    (omega : StepPath) (m qOld qNew : ℕ)
    (hnew : trajectory omega (qNew + 1) ≠ 0) :
    lowGapDeficitFailure (oneStepRecenter (trajectory omega)) m qOld qNew ↔
      lowGapDeficitFailure (trajectory omega) m (qOld + 1) (qNew + 1) := by
  simp only [lowGapDeficitFailure, oneStepRecenter_point_eq_sub,
    gapScaleOf_sub_right]
  rw [localTime_oneStepRecenter_eq_of_ne_origin omega qOld
    (trajectory omega (qNew + 1)) hnew]

private theorem position_ne_zero_of_creation_of_origin_lt
    (omega : StepPath) {m k n N : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hnN : n ≤ N) (horigin : localTime (trajectory omega) N 0 < m) :
    trajectory omega n ≠ 0 := by
  intro hzero
  have hsite := position_mem_thresholdSites_of_creation hk hcreation
  have hlocal : m ≤ localTime (trajectory omega) n (trajectory omega n) :=
    (mem_thresholdSites_iff _ _ _ _ hm).mp hsite
  rw [hzero] at hlocal
  exact (not_lt_of_ge
    (hlocal.trans (localTime_mono_time (trajectory omega) 0 hnN))) horigin

theorem pairConfiguration_oneStepRecenter_of_origin_lt
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (a : GapScale) (n₁ n₂ : ℕ)
    (horigin : localTime (trajectory omega) n₂ 0 < m)
    (hpair : trajectory omega ∈ pairConfiguration (.checker d) m a n₁ n₂) :
    ∃ q₁ q₂, n₁ = q₁ + 1 ∧ n₂ = q₂ + 1 ∧
      oneStepRecenter (trajectory omega) ∈
        pairConfiguration (shiftedCheckerTiling d) m a q₁ q₂ := by
  rcases hpair with ⟨h₁, h₂, hnext, hdomino, hscale⟩
  have hn₁pos := thresholdCreation_time_pos_of_two_le omega hm (by omega) h₁
  have hn₂pos := thresholdCreation_time_pos_of_two_le omega hm (by omega) h₂
  obtain ⟨q₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₁pos.ne'
  obtain ⟨q₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₂pos.ne'
  have htime : q₁ + 1 ≤ q₂ + 1 :=
    (creation_time_lt (by omega) (by omega) (by omega) h₁ h₂).le
  have horigin₁ : localTime (trajectory omega) (q₁ + 1) 0 < m :=
    (localTime_mono_time (trajectory omega) 0 htime).trans_lt horigin
  have hpoint₁ := oneStepRecenter_point_eq_sub omega q₁
  have hpoint₂ := oneStepRecenter_point_eq_sub omega q₂
  refine ⟨q₁, q₂, by omega, by omega, ?_⟩
  refine ⟨thresholdCreation_oneStepRecenter omega q₁ m 1 (by omega) h₁
      horigin₁,
    thresholdCreation_oneStepRecenter omega q₂ m 2 (by omega) h₂
      horigin, ?_, ?_, ?_⟩
  · rw [thresholdCount_oneStepRecenter_eq omega q₂ (m + 1) (by omega)
      (horigin.trans (Nat.lt_succ_self m))]
    exact hnext
  · rw [hpoint₁, hpoint₂,
      sameDomino_shiftedChecker_sub_iff omega d]
    exact hdomino
  · rw [hpoint₁, hpoint₂, gapScaleOf_sub_right]
    exact hscale

theorem tripleConfiguration_oneStepRecenter_of_origin_lt
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (a₁ a₂ : GapScale)
    (n₁ n₂ n₃ : ℕ)
    (horigin : localTime (trajectory omega) n₃ 0 < m)
    (htriple : trajectory omega ∈
      tripleConfiguration (.checker d) m a₁ a₂ n₁ n₂ n₃) :
    ∃ q₁ q₂ q₃, n₁ = q₁ + 1 ∧ n₂ = q₂ + 1 ∧ n₃ = q₃ + 1 ∧
      oneStepRecenter (trajectory omega) ∈
        tripleConfiguration (shiftedCheckerTiling d) m a₁ a₂ q₁ q₂ q₃ := by
  rcases htriple with
    ⟨h₁, h₂, h₃, hnext, hdomino₁₂, hdomino₁₃, hdomino₂₃,
      hscale₁, hscale₂⟩
  have hn₁pos := thresholdCreation_time_pos_of_two_le omega hm (by omega) h₁
  have hn₂pos := thresholdCreation_time_pos_of_two_le omega hm (by omega) h₂
  have hn₃pos := thresholdCreation_time_pos_of_two_le omega hm (by omega) h₃
  obtain ⟨q₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₁pos.ne'
  obtain ⟨q₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₂pos.ne'
  obtain ⟨q₃, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₃pos.ne'
  have htime₁ : q₁ + 1 ≤ q₃ + 1 :=
    (creation_time_lt (by omega) (by omega) (by omega) h₁ h₃).le
  have htime₂ : q₂ + 1 ≤ q₃ + 1 :=
    (creation_time_lt (by omega) (by omega) (by omega) h₂ h₃).le
  have horigin₁ : localTime (trajectory omega) (q₁ + 1) 0 < m :=
    (localTime_mono_time (trajectory omega) 0 htime₁).trans_lt horigin
  have horigin₂ : localTime (trajectory omega) (q₂ + 1) 0 < m :=
    (localTime_mono_time (trajectory omega) 0 htime₂).trans_lt horigin
  have hp₁ := oneStepRecenter_point_eq_sub omega q₁
  have hp₂ := oneStepRecenter_point_eq_sub omega q₂
  have hp₃ := oneStepRecenter_point_eq_sub omega q₃
  refine ⟨q₁, q₂, q₃, by omega, by omega, by omega, ?_⟩
  refine ⟨thresholdCreation_oneStepRecenter omega q₁ m 1 (by omega) h₁
      horigin₁,
    thresholdCreation_oneStepRecenter omega q₂ m 2 (by omega) h₂
      horigin₂,
    thresholdCreation_oneStepRecenter omega q₃ m 3 (by omega) h₃
      horigin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [thresholdCount_oneStepRecenter_eq omega q₃ (m + 1) (by omega)
      (horigin.trans (Nat.lt_succ_self m))]
    exact hnext
  · rw [hp₁, hp₂, sameDomino_shiftedChecker_sub_iff omega d]
    exact hdomino₁₂
  · rw [hp₁, hp₃, sameDomino_shiftedChecker_sub_iff omega d]
    exact hdomino₁₃
  · rw [hp₂, hp₃, sameDomino_shiftedChecker_sub_iff omega d]
    exact hdomino₂₃
  · rw [hp₁, hp₂, gapScaleOf_sub_right]
    exact hscale₁
  · rw [hp₂, hp₃, gapScaleOf_sub_right]
    exact hscale₂

/-- Outside the discarded-origin obstruction, a physical checker first
structural past remains a first structural past after deleting the first
step and recentering. -/
theorem firstStructuralPast_oneStepRecenter_of_origin_lt
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (gaps : GapTriple)
    (horigin : localTime (trajectory omega)
      (creationTimeNat m 2 (trajectory omega)) 0 < m)
    (hs : trajectory omega ∈ firstStructuralPast (.checker d) m gaps) :
    oneStepRecenter (trajectory omega) ∈
      firstStructuralPast (shiftedCheckerTiling d) m gaps := by
  rcases hs with ⟨htransition, hnotBad⟩
  rcases Set.mem_iUnion.mp htransition with ⟨n₁, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨n₂, hpair⟩
  have hclock : creationTimeNat m 2 (trajectory omega) = n₂ :=
    creationTimeNat_eq_of_creation hpair.2.1
  have horigin₂ : localTime (trajectory omega) n₂ 0 < m := by
    simpa only [hclock] using horigin
  obtain ⟨q₁, q₂, rfl, rfl, hpairShift⟩ :=
    pairConfiguration_oneStepRecenter_of_origin_lt omega d m hm gaps.1.1
      n₁ n₂ horigin₂ hpair
  refine ⟨Set.mem_iUnion_of_mem q₁ <| Set.mem_iUnion_of_mem q₂
      hpairShift, ?_⟩
  intro hbadShift
  rcases Set.mem_iUnion.mp hbadShift with ⟨q₁', hbadShift⟩
  rcases Set.mem_iUnion.mp hbadShift with ⟨q₂', hpairBad, hgapBad⟩
  have hq₁ : q₁' = q₁ :=
    thresholdCreation_time_unique hpairBad.1 hpairShift.1
  have hq₂ : q₂' = q₂ :=
    thresholdCreation_time_unique hpairBad.2.1 hpairShift.2.1
  subst q₁'
  subst q₂'
  have hnew : trajectory omega (q₂ + 1) ≠ 0 :=
    position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
      hpair.2.1 le_rfl horigin₂
  apply hnotBad
  exact Set.mem_iUnion_of_mem (q₁ + 1) <|
    Set.mem_iUnion_of_mem (q₂ + 1) ⟨hpair,
      (lowGapDeficitFailure_oneStepRecenter_iff omega m q₁ q₂ hnew).mp
        hgapBad⟩

/-- Outside the discarded-origin obstruction, a physical checker second
structural past remains a second structural past after deleting the first
step and recentering. -/
theorem secondStructuralPast_oneStepRecenter_of_origin_lt
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (gaps : GapTriple)
    (horigin : localTime (trajectory omega)
      (creationTimeNat m 3 (trajectory omega)) 0 < m)
    (hs : trajectory omega ∈ secondStructuralPast (.checker d) m gaps) :
    oneStepRecenter (trajectory omega) ∈
      secondStructuralPast (shiftedCheckerTiling d) m gaps := by
  rcases hs with ⟨htransition, hnotBad⟩
  rcases Set.mem_iUnion.mp htransition with ⟨n₁, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨n₂, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨n₃, htriple⟩
  have hclock : creationTimeNat m 3 (trajectory omega) = n₃ :=
    creationTimeNat_eq_of_creation htriple.2.2.1
  have horigin₃ : localTime (trajectory omega) n₃ 0 < m := by
    simpa only [hclock] using horigin
  obtain ⟨q₁, q₂, q₃, rfl, rfl, rfl, htripleShift⟩ :=
    tripleConfiguration_oneStepRecenter_of_origin_lt omega d m hm gaps.1.1
      gaps.1.2 n₁ n₂ n₃ horigin₃ htriple
  refine ⟨Set.mem_iUnion_of_mem q₁ <| Set.mem_iUnion_of_mem q₂ <|
      Set.mem_iUnion_of_mem q₃ htripleShift, ?_⟩
  intro hbadShift
  rcases hbadShift with hfirstBad | hsecondBad
  · rcases Set.mem_iUnion.mp hfirstBad with ⟨q₁', hfirstBad⟩
    rcases Set.mem_iUnion.mp hfirstBad with
      ⟨q₂', hpairBad, hgapBad⟩
    have hq₁ : q₁' = q₁ :=
      thresholdCreation_time_unique hpairBad.1 htripleShift.1
    have hq₂ : q₂' = q₂ :=
      thresholdCreation_time_unique hpairBad.2.1 htripleShift.2.1
    subst q₁'
    subst q₂'
    have htime₂₃ : q₂ + 1 ≤ q₃ + 1 :=
      (creation_time_lt (by omega) (by omega) (by omega)
        htriple.2.1 htriple.2.2.1).le
    have hnew : trajectory omega (q₂ + 1) ≠ 0 :=
      position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
        htriple.2.1 htime₂₃ horigin₃
    have hnext₂ : thresholdCount (trajectory omega) (q₂ + 1) (m + 1) = 0 := by
      have hmono := thresholdCount_mono_time (trajectory omega) (m + 1)
        htime₂₃
      dsimp only at hmono
      rw [htriple.2.2.2.1] at hmono
      omega
    apply hnotBad
    exact Or.inl <| Set.mem_iUnion_of_mem (q₁ + 1) <|
      Set.mem_iUnion_of_mem (q₂ + 1) ⟨
        ⟨htriple.1, htriple.2.1, hnext₂, htriple.2.2.2.2.1,
          htriple.2.2.2.2.2.2.2.1⟩,
        (lowGapDeficitFailure_oneStepRecenter_iff omega m q₁ q₂ hnew).mp
          hgapBad⟩
  · rcases Set.mem_iUnion.mp hsecondBad with ⟨q₁', hsecondBad⟩
    rcases Set.mem_iUnion.mp hsecondBad with ⟨q₂', hsecondBad⟩
    rcases Set.mem_iUnion.mp hsecondBad with
      ⟨q₃', htripleBad, hgapBad⟩
    have hq₁ : q₁' = q₁ :=
      thresholdCreation_time_unique htripleBad.1 htripleShift.1
    have hq₂ : q₂' = q₂ :=
      thresholdCreation_time_unique htripleBad.2.1 htripleShift.2.1
    have hq₃ : q₃' = q₃ :=
      thresholdCreation_time_unique htripleBad.2.2.1 htripleShift.2.2.1
    subst q₁'
    subst q₂'
    subst q₃'
    have hnew : trajectory omega (q₃ + 1) ≠ 0 :=
      position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
        htriple.2.2.1 le_rfl horigin₃
    apply hnotBad
    exact Or.inr <| Set.mem_iUnion_of_mem (q₁ + 1) <|
      Set.mem_iUnion_of_mem (q₂ + 1) <|
        Set.mem_iUnion_of_mem (q₃ + 1) ⟨htriple,
          (lowGapDeficitFailure_oneStepRecenter_iff omega m q₂ q₃ hnew).mp
            hgapBad⟩

theorem pairConfiguration_of_oneStepRecenter_of_originSafe
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (a : GapScale) (q₁ q₂ : ℕ)
    (horigin : localTime (oneStepRecenter (trajectory omega)) q₂
      (0 - trajectory omega 1) + 1 < m)
    (hpair : oneStepRecenter (trajectory omega) ∈
      pairConfiguration (shiftedCheckerTiling d) m a q₁ q₂) :
    trajectory omega ∈
      pairConfiguration (.checker d) m a (q₁ + 1) (q₂ + 1) := by
  rcases hpair with ⟨h₁, h₂, hnext, hdomino, hscale⟩
  have horiginPhysical :
      localTime (trajectory omega) (q₂ + 1) 0 < m := by
    rw [← localTime_oneStepRecenter_origin_add_one omega q₂]
    exact horigin
  have htime : q₁ ≤ q₂ :=
    (creation_time_lt (by omega) (by omega) (by omega) h₁ h₂).le
  have horigin₁ : localTime (oneStepRecenter (trajectory omega)) q₁
      (0 - trajectory omega 1) + 1 < m := by
    have hmono := localTime_mono_time (oneStepRecenter (trajectory omega))
      (0 - trajectory omega 1) htime
    dsimp only at hmono
    omega
  have hp₁ := oneStepRecenter_point_eq_sub omega q₁
  have hp₂ := oneStepRecenter_point_eq_sub omega q₂
  refine ⟨thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      (by omega) h₁ horigin₁,
    thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      (by omega) h₂ horigin, ?_, ?_, ?_⟩
  · rw [← thresholdCount_oneStepRecenter_eq omega q₂ (m + 1)
      (by omega) (horiginPhysical.trans (Nat.lt_succ_self m))]
    exact hnext
  · rw [hp₁, hp₂, sameDomino_shiftedChecker_sub_iff] at hdomino
    exact hdomino
  · rw [hp₁, hp₂, gapScaleOf_sub_right] at hscale
    exact hscale

theorem tripleConfiguration_of_oneStepRecenter_of_originSafe
    (omega : StepPath) (d : Tilings.CheckerDirection)
    (m : ℕ) (hm : 2 ≤ m) (a₁ a₂ : GapScale) (q₁ q₂ q₃ : ℕ)
    (horigin : localTime (oneStepRecenter (trajectory omega)) q₃
      (0 - trajectory omega 1) + 1 < m)
    (htriple : oneStepRecenter (trajectory omega) ∈
      tripleConfiguration (shiftedCheckerTiling d) m a₁ a₂ q₁ q₂ q₃) :
    trajectory omega ∈
      tripleConfiguration (.checker d) m a₁ a₂
        (q₁ + 1) (q₂ + 1) (q₃ + 1) := by
  rcases htriple with
    ⟨h₁, h₂, h₃, hnext, hdomino₁₂, hdomino₁₃, hdomino₂₃,
      hscale₁, hscale₂⟩
  have horiginPhysical :
      localTime (trajectory omega) (q₃ + 1) 0 < m := by
    rw [← localTime_oneStepRecenter_origin_add_one omega q₃]
    exact horigin
  have htime₁ : q₁ ≤ q₃ :=
    (creation_time_lt (by omega) (by omega) (by omega) h₁ h₃).le
  have htime₂ : q₂ ≤ q₃ :=
    (creation_time_lt (by omega) (by omega) (by omega) h₂ h₃).le
  have horigin₁ : localTime (oneStepRecenter (trajectory omega)) q₁
      (0 - trajectory omega 1) + 1 < m := by
    have hmono := localTime_mono_time (oneStepRecenter (trajectory omega))
      (0 - trajectory omega 1) htime₁
    dsimp only at hmono
    omega
  have horigin₂ : localTime (oneStepRecenter (trajectory omega)) q₂
      (0 - trajectory omega 1) + 1 < m := by
    have hmono := localTime_mono_time (oneStepRecenter (trajectory omega))
      (0 - trajectory omega 1) htime₂
    dsimp only at hmono
    omega
  have hp₁ := oneStepRecenter_point_eq_sub omega q₁
  have hp₂ := oneStepRecenter_point_eq_sub omega q₂
  have hp₃ := oneStepRecenter_point_eq_sub omega q₃
  refine ⟨thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      (by omega) h₁ horigin₁,
    thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      (by omega) h₂ horigin₂,
    thresholdCreation_of_oneStepRecenter_of_originSafe omega hm
      (by omega) h₃ horigin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← thresholdCount_oneStepRecenter_eq omega q₃ (m + 1)
      (by omega) (horiginPhysical.trans (Nat.lt_succ_self m))]
    exact hnext
  · rw [hp₁, hp₂, sameDomino_shiftedChecker_sub_iff] at hdomino₁₂
    exact hdomino₁₂
  · rw [hp₁, hp₃, sameDomino_shiftedChecker_sub_iff] at hdomino₁₃
    exact hdomino₁₃
  · rw [hp₂, hp₃, sameDomino_shiftedChecker_sub_iff] at hdomino₂₃
    exact hdomino₂₃
  · rw [hp₁, hp₂, gapScaleOf_sub_right] at hscale₁
    exact hscale₁
  · rw [hp₂, hp₃, gapScaleOf_sub_right] at hscale₂
    exact hscale₂

/-- Target origin-safety makes the recentered first structural past lift
back to the physical checker past. -/
theorem firstStructuralPast_of_oneStepRecenter_of_originSafe
    (omega : StepPath) (d : Tilings.CheckerDirection) (e : Direction)
    (m : ℕ) (hm : 2 ≤ m) (gaps : GapTriple)
    (hfirst : trajectory omega 1 = directionVector e)
    (hsafe : oneStepRecenter (trajectory omega) ∈ targetOriginSafe m 2 e)
    (hs : oneStepRecenter (trajectory omega) ∈
      firstStructuralPast (shiftedCheckerTiling d) m gaps) :
    trajectory omega ∈ firstStructuralPast (.checker d) m gaps := by
  rcases hs with ⟨htransition, hnotBad⟩
  rcases Set.mem_iUnion.mp htransition with ⟨q₁, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨q₂, hpair⟩
  have hclock : creationTimeNat m 2 (oneStepRecenter (trajectory omega)) = q₂ :=
    creationTimeNat_eq_of_creation hpair.2.1
  have horigin : localTime (oneStepRecenter (trajectory omega)) q₂
      (0 - trajectory omega 1) + 1 < m := by
    change localTime (oneStepRecenter (trajectory omega))
      (creationTimeNat m 2 (oneStepRecenter (trajectory omega)))
      (0 - directionVector e) + 1 < m at hsafe
    simpa only [hclock, hfirst] using hsafe
  have hpairPhysical := pairConfiguration_of_oneStepRecenter_of_originSafe
    omega d m hm gaps.1.1 q₁ q₂ horigin hpair
  refine ⟨Set.mem_iUnion_of_mem (q₁ + 1) <|
    Set.mem_iUnion_of_mem (q₂ + 1) hpairPhysical, ?_⟩
  intro hbad
  rcases Set.mem_iUnion.mp hbad with ⟨n₁, hbad⟩
  rcases Set.mem_iUnion.mp hbad with ⟨n₂, hpairBad, hgapBad⟩
  have hn₁ : n₁ = q₁ + 1 :=
    thresholdCreation_time_unique hpairBad.1 hpairPhysical.1
  have hn₂ : n₂ = q₂ + 1 :=
    thresholdCreation_time_unique hpairBad.2.1 hpairPhysical.2.1
  subst n₁
  subst n₂
  have horiginPhysical : localTime (trajectory omega) (q₂ + 1) 0 < m := by
    rw [← localTime_oneStepRecenter_origin_add_one omega q₂]
    exact horigin
  have hnew : trajectory omega (q₂ + 1) ≠ 0 :=
    position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
      hpairPhysical.2.1 le_rfl horiginPhysical
  apply hnotBad
  exact Set.mem_iUnion_of_mem q₁ <| Set.mem_iUnion_of_mem q₂
    ⟨hpair,
      (lowGapDeficitFailure_oneStepRecenter_iff omega m q₁ q₂ hnew).mpr
        hgapBad⟩

/-- Target origin-safety makes the recentered second structural past lift
back to the physical checker past. -/
theorem secondStructuralPast_of_oneStepRecenter_of_originSafe
    (omega : StepPath) (d : Tilings.CheckerDirection) (e : Direction)
    (m : ℕ) (hm : 2 ≤ m) (gaps : GapTriple)
    (hfirst : trajectory omega 1 = directionVector e)
    (hsafe : oneStepRecenter (trajectory omega) ∈ targetOriginSafe m 3 e)
    (hs : oneStepRecenter (trajectory omega) ∈
      secondStructuralPast (shiftedCheckerTiling d) m gaps) :
    trajectory omega ∈ secondStructuralPast (.checker d) m gaps := by
  rcases hs with ⟨htransition, hnotBad⟩
  rcases Set.mem_iUnion.mp htransition with ⟨q₁, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨q₂, htransition⟩
  rcases Set.mem_iUnion.mp htransition with ⟨q₃, htriple⟩
  have hclock : creationTimeNat m 3 (oneStepRecenter (trajectory omega)) = q₃ :=
    creationTimeNat_eq_of_creation htriple.2.2.1
  have horigin : localTime (oneStepRecenter (trajectory omega)) q₃
      (0 - trajectory omega 1) + 1 < m := by
    change localTime (oneStepRecenter (trajectory omega))
      (creationTimeNat m 3 (oneStepRecenter (trajectory omega)))
      (0 - directionVector e) + 1 < m at hsafe
    simpa only [hclock, hfirst] using hsafe
  have htriplePhysical := tripleConfiguration_of_oneStepRecenter_of_originSafe
    omega d m hm gaps.1.1 gaps.1.2 q₁ q₂ q₃ horigin htriple
  refine ⟨Set.mem_iUnion_of_mem (q₁ + 1) <|
    Set.mem_iUnion_of_mem (q₂ + 1) <|
      Set.mem_iUnion_of_mem (q₃ + 1) htriplePhysical, ?_⟩
  intro hbad
  rcases hbad with hfirstBad | hsecondBad
  · rcases Set.mem_iUnion.mp hfirstBad with ⟨n₁, hfirstBad⟩
    rcases Set.mem_iUnion.mp hfirstBad with ⟨n₂, hpairBad, hgapBad⟩
    have hn₁ : n₁ = q₁ + 1 :=
      thresholdCreation_time_unique hpairBad.1 htriplePhysical.1
    have hn₂ : n₂ = q₂ + 1 :=
      thresholdCreation_time_unique hpairBad.2.1 htriplePhysical.2.1
    subst n₁
    subst n₂
    have horiginPhysical : localTime (trajectory omega) (q₃ + 1) 0 < m := by
      rw [← localTime_oneStepRecenter_origin_add_one omega q₃]
      exact horigin
    have htime : q₂ + 1 ≤ q₃ + 1 :=
      (creation_time_lt (by omega) (by omega) (by omega)
        htriplePhysical.2.1 htriplePhysical.2.2.1).le
    have hnew : trajectory omega (q₂ + 1) ≠ 0 :=
      position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
        htriplePhysical.2.1 htime horiginPhysical
    apply hnotBad
    exact Or.inl <| Set.mem_iUnion_of_mem q₁ <| Set.mem_iUnion_of_mem q₂
      ⟨⟨htriple.1, htriple.2.1, by
          have hmono := thresholdCount_mono_time
            (oneStepRecenter (trajectory omega)) (m + 1)
            ((creation_time_lt (by omega) (by omega) (by omega)
              htriple.2.1 htriple.2.2.1).le)
          dsimp only at hmono
          rw [htriple.2.2.2.1] at hmono
          omega,
        htriple.2.2.2.2.1, htriple.2.2.2.2.2.2.2.1⟩,
       (lowGapDeficitFailure_oneStepRecenter_iff omega m q₁ q₂ hnew).mpr
         hgapBad⟩
  · rcases Set.mem_iUnion.mp hsecondBad with ⟨n₁, hsecondBad⟩
    rcases Set.mem_iUnion.mp hsecondBad with ⟨n₂, hsecondBad⟩
    rcases Set.mem_iUnion.mp hsecondBad with ⟨n₃, htripleBad, hgapBad⟩
    have hn₁ : n₁ = q₁ + 1 :=
      thresholdCreation_time_unique htripleBad.1 htriplePhysical.1
    have hn₂ : n₂ = q₂ + 1 :=
      thresholdCreation_time_unique htripleBad.2.1 htriplePhysical.2.1
    have hn₃ : n₃ = q₃ + 1 :=
      thresholdCreation_time_unique htripleBad.2.2.1 htriplePhysical.2.2.1
    subst n₁
    subst n₂
    subst n₃
    have horiginPhysical : localTime (trajectory omega) (q₃ + 1) 0 < m := by
      rw [← localTime_oneStepRecenter_origin_add_one omega q₃]
      exact horigin
    have hnew : trajectory omega (q₃ + 1) ≠ 0 :=
      position_ne_zero_of_creation_of_origin_lt omega (by omega) (by omega)
        htriplePhysical.2.2.1 le_rfl horiginPhysical
    apply hnotBad
    exact Or.inr <| Set.mem_iUnion_of_mem q₁ <|
      Set.mem_iUnion_of_mem q₂ <| Set.mem_iUnion_of_mem q₃
        ⟨htriple,
          (lowGapDeficitFailure_oneStepRecenter_iff omega m q₂ q₃ hnew).mpr
            hgapBad⟩

theorem lowGapDeficitFailure_horizontalReflectPath
    (s : WalkPath) (m nOld nNew : ℕ) :
    lowGapDeficitFailure (horizontalReflectPath s) m nOld nNew ↔
      lowGapDeficitFailure s m nOld nNew := by
  simp only [lowGapDeficitFailure, horizontalReflectPath,
    gapScaleOf_horizontalReflectPoint, localTime_horizontalReflectPath]

theorem pairConfiguration_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (a : GapScale) (n₁ n₂ : ℕ) :
    horizontalReflectPath s ∈
        pairConfiguration (reflectedColumnTiling t) m a n₁ n₂ ↔
      s ∈ pairConfiguration t m a n₁ n₂ := by
  simp only [pairConfiguration, Set.mem_ofPred_eq, horizontalReflectPath,
    thresholdCreation_horizontalReflectPath s m 1 n₁ hm,
    thresholdCreation_horizontalReflectPath s m 2 n₂ hm,
    thresholdCount_horizontalReflectPath s n₂ (m + 1) (by omega),
    sameDomino_reflectedColumn_iff ht,
    gapScaleOf_horizontalReflectPoint]

theorem tripleConfiguration_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (a₁ a₂ : GapScale)
    (n₁ n₂ n₃ : ℕ) :
    horizontalReflectPath s ∈
        tripleConfiguration (reflectedColumnTiling t) m a₁ a₂ n₁ n₂ n₃ ↔
      s ∈ tripleConfiguration t m a₁ a₂ n₁ n₂ n₃ := by
  simp only [tripleConfiguration, Set.mem_ofPred_eq, horizontalReflectPath,
    thresholdCreation_horizontalReflectPath s m 1 n₁ hm,
    thresholdCreation_horizontalReflectPath s m 2 n₂ hm,
    thresholdCreation_horizontalReflectPath s m 3 n₃ hm,
    thresholdCount_horizontalReflectPath s n₃ (m + 1) (by omega),
    sameDomino_reflectedColumn_iff ht,
    gapScaleOf_horizontalReflectPoint]

theorem firstTransitionEvent_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        firstTransitionEvent (reflectedColumnTiling t) m gaps ↔
      s ∈ firstTransitionEvent t m gaps := by
  simp only [firstTransitionEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨n₁, n₂, hs⟩
    exact ⟨n₁, n₂,
      (pairConfiguration_horizontalReflectPath ht s m hm gaps.1.1 n₁ n₂).mp hs⟩
  · rintro ⟨n₁, n₂, hs⟩
    exact ⟨n₁, n₂,
      (pairConfiguration_horizontalReflectPath ht s m hm gaps.1.1 n₁ n₂).mpr hs⟩

theorem secondTransitionEvent_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        secondTransitionEvent (reflectedColumnTiling t) m gaps ↔
      s ∈ secondTransitionEvent t m gaps := by
  simp only [secondTransitionEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨n₁, n₂, n₃, hs⟩
    exact ⟨n₁, n₂, n₃,
      (tripleConfiguration_horizontalReflectPath ht s m hm gaps.1.1 gaps.1.2
        n₁ n₂ n₃).mp hs⟩
  · rintro ⟨n₁, n₂, n₃, hs⟩
    exact ⟨n₁, n₂, n₃,
      (tripleConfiguration_horizontalReflectPath ht s m hm gaps.1.1 gaps.1.2
        n₁ n₂ n₃).mpr hs⟩

theorem firstLowGapFailureEvent_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        firstLowGapFailureEvent (reflectedColumnTiling t) m gaps ↔
      s ∈ firstLowGapFailureEvent t m gaps := by
  simp only [firstLowGapFailureEvent, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n₁, n₂, hpair, hgap⟩
    exact ⟨n₁, n₂,
      (pairConfiguration_horizontalReflectPath ht s m hm gaps.1.1 n₁ n₂).mp
        hpair,
      (lowGapDeficitFailure_horizontalReflectPath s m n₁ n₂).mp hgap⟩
  · rintro ⟨n₁, n₂, hpair, hgap⟩
    exact ⟨n₁, n₂,
      (pairConfiguration_horizontalReflectPath ht s m hm gaps.1.1 n₁ n₂).mpr
        hpair,
      (lowGapDeficitFailure_horizontalReflectPath s m n₁ n₂).mpr hgap⟩

theorem secondLowGapFailureEvent_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        secondLowGapFailureEvent (reflectedColumnTiling t) m gaps ↔
      s ∈ secondLowGapFailureEvent t m gaps := by
  simp only [secondLowGapFailureEvent, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n₁, n₂, n₃, htriple, hgap⟩
    exact ⟨n₁, n₂, n₃,
      (tripleConfiguration_horizontalReflectPath ht s m hm gaps.1.1 gaps.1.2
        n₁ n₂ n₃).mp htriple,
      (lowGapDeficitFailure_horizontalReflectPath s m n₂ n₃).mp hgap⟩
  · rintro ⟨n₁, n₂, n₃, htriple, hgap⟩
    exact ⟨n₁, n₂, n₃,
      (tripleConfiguration_horizontalReflectPath ht s m hm gaps.1.1 gaps.1.2
        n₁ n₂ n₃).mpr htriple,
      (lowGapDeficitFailure_horizontalReflectPath s m n₂ n₃).mpr hgap⟩

theorem firstStructuralPast_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        firstStructuralPast (reflectedColumnTiling t) m gaps ↔
      s ∈ firstStructuralPast t m gaps := by
  change
    (horizontalReflectPath s ∈
        firstTransitionEvent (reflectedColumnTiling t) m gaps ∧
      horizontalReflectPath s ∉
        firstLowGapFailureEvent (reflectedColumnTiling t) m gaps) ↔
      (s ∈ firstTransitionEvent t m gaps ∧
        s ∉ firstLowGapFailureEvent t m gaps)
  rw [firstTransitionEvent_horizontalReflectPath ht s m hm,
    firstLowGapFailureEvent_horizontalReflectPath ht s m hm]

theorem secondStructuralPast_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (m : ℕ) (hm : 0 < m) (gaps : GapTriple) :
    horizontalReflectPath s ∈
        secondStructuralPast (reflectedColumnTiling t) m gaps ↔
      s ∈ secondStructuralPast t m gaps := by
  change
    (horizontalReflectPath s ∈
        secondTransitionEvent (reflectedColumnTiling t) m gaps ∧
      horizontalReflectPath s ∉
        firstLowGapFailureEvent (reflectedColumnTiling t) m gaps ∪
          secondLowGapFailureEvent (reflectedColumnTiling t) m gaps) ↔
      (s ∈ secondTransitionEvent t m gaps ∧
        s ∉ firstLowGapFailureEvent t m gaps ∪
          secondLowGapFailureEvent t m gaps)
  simp only [Set.mem_union,
    secondTransitionEvent_horizontalReflectPath ht s m hm,
    firstLowGapFailureEvent_horizontalReflectPath ht s m hm,
    secondLowGapFailureEvent_horizontalReflectPath ht s m hm]

end

end Erdos1165.HLOZStructuralPastTransport
