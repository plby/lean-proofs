/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.RestartBridge

/-!
# Completion of the HLOZ lower-bound assembly

This module combines the fresh-walk estimate, the two deterministic restart
bridges, strong Markov at the two level clocks, recurrence, and conditional
Borel--Cantelli.  Its final theorem leaves precisely HLOZ Proposition 1.3 as
an input and concludes that three favorite sites occur infinitely often.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.LowerConclusion

open Lower LowerAssembly RestartBridge

theorem fairBlock_freshCreationBlock_toReal_eq
    (delta : ℝ) (m : ℕ) (x : Point) :
    (fairBlock (levelCutoffTime delta m) (freshCreationBlock delta m x)).toReal =
      fairSteps.real (freshCreationSteps delta m x) := by
  rw [measureReal_def, ← fairSteps_map_stepBlock 0 (levelCutoffTime delta m)]
  rw [Measure.map_apply (measurable_stepBlock 0 (levelCutoffTime delta m))
    (measurableSet_freshCreationBlock delta m x)]
  have heq : stepBlock 0 (levelCutoffTime delta m) =
      stepPrefix (levelCutoffTime delta m) := by
    funext omega j
    simp [stepBlock, stepPrefix]
  rw [heq]
  congr 2
  ext omega
  change stepPrefix (levelCutoffTime delta m) omega ∈ freshCreationBlock delta m x ↔ _
  exact mem_freshCreationBlock_stepPrefix_iff delta m x omega

theorem ae_mem_levelEventSteps_one (m : ℕ) (hm : 0 < m) :
    ∀ᵐ omega ∂fairSteps, omega ∈ levelEventSteps m 1 := by
  have hdivSteps : ∀ᵐ omega ∂fairSteps,
      MaxLocalTimeDiverges (trajectory omega) := by
    change ∀ᵐ omega ∂fairSteps,
      Tendsto (maxLocalTime (trajectory omega)) atTop atTop
    rw [← ae_map_iff measurable_trajectory.aemeasurable
      measurableSet_tendsto_maxLocalTime, ← simpleRandomWalk]
    exact ae_maxLocalTime_tendsto_atTop
  filter_upwards [hdivSteps] with omega hdiv
  rw [levelEventSteps_eq_preimage m 1 (by omega)]
  exact levelFavorite_one_of_maxLocalTimeDiverges (trajectory omega) m hm hdiv

theorem firstStage_condExp_lower
    (delta : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    ∀ᵐ omega ∂fairSteps,
      fairSteps.real (freshCreationSteps delta m 0) ≤
        (fairSteps[(levelEventSteps m 2).indicator (1 : StepPath → ℝ) |
          (isStoppingTime_levelTimeSteps m 1).measurableSpace]) omega := by
  let B := levelEventSteps m 1
  let D := postWithTopStoppingBlock (levelTimeSteps m 1)
      (levelCutoffTime delta m) ⁻¹' freshCreationBlock delta m 0
  let E := B ∩ D
  have hB : MeasurableSet[(isStoppingTime_levelTimeSteps m 1).measurableSpace] B :=
    measurableSet_levelEventSteps_at_current m 1
  have hBfinite : B ⊆ {omega | levelTimeSteps m 1 omega < ⊤} := by
    intro omega homega
    change levelTimeSteps m 1 omega < levelTimeSteps (m + 1) 1 omega at homega
    exact homega.trans_le le_top
  have hEmeas : MeasurableSet E :=
    ((isStoppingTime_levelTimeSteps m 1).measurableSpace_le B hB).inter
      ((measurable_postWithTopStoppingBlock (isStoppingTime_levelTimeSteps m 1)
        (levelCutoffTime delta m)) (measurableSet_freshCreationBlock delta m 0))
  have hM2meas : MeasurableSet (levelEventSteps m 2) :=
    measurableSet_levelEventSteps m 2 (by omega)
  have hmono :
      fairSteps[E.indicator (1 : StepPath → ℝ) |
          (isStoppingTime_levelTimeSteps m 1).measurableSpace] ≤ᵐ[fairSteps]
        fairSteps[(levelEventSteps m 2).indicator (1 : StepPath → ℝ) |
          (isStoppingTime_levelTimeSteps m 1).measurableSpace] := by
    apply condExp_mono
    · exact (integrable_const 1).indicator hEmeas
    · exact (integrable_const 1).indicator hM2meas
    · exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases he : omega ∈ E
        · have hm2 : omega ∈ levelEventSteps m 2 :=
            firstStage_freshCreation_subset_levelEventTwo delta m hm he
          simp [Set.indicator, he, hm2]
        · by_cases hm2 : omega ∈ levelEventSteps m 2 <;>
            simp [Set.indicator, he, hm2]
  have hmarkov := condExp_indicator_inter_postWithTopStoppingBlock
    (isStoppingTime_levelTimeSteps m 1) hB hBfinite
    (levelCutoffTime delta m) (freshCreationBlock delta m 0)
  have hBae := ae_mem_levelEventSteps_one m (by omega)
  filter_upwards [hmono, hmarkov, hBae] with omega hmono_o hmarkov_o hB_o
  calc
    fairSteps.real (freshCreationSteps delta m 0) =
        (fairBlock (levelCutoffTime delta m)
          (freshCreationBlock delta m 0)).toReal :=
      (fairBlock_freshCreationBlock_toReal_eq delta m 0).symm
    _ = (fairBlock (levelCutoffTime delta m)
          (freshCreationBlock delta m 0)).toReal * B.indicator
            (1 : StepPath → ℝ) omega := by simp [B, hB_o]
    _ = (fairSteps[E.indicator (1 : StepPath → ℝ) |
          (isStoppingTime_levelTimeSteps m 1).measurableSpace]) omega := by
      exact hmarkov_o.symm
    _ ≤ _ := hmono_o

/-- For an extended natural-valued stopping time, atomwise measurability is
enough to give Mathlib stopped-sigma-algebra measurability for an event that
itself forces the clock to be finite. -/
theorem measurableSet_stopping_of_atomwise_of_finite
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    (hfinite : A ⊆ {omega | tau omega < ⊤}) :
    MeasurableSet[htau.measurableSpace] A := by
  rw [htau.measurableSet]
  constructor
  · have hdecomp : A = ⋃ n : ℕ, A ∩ {omega | tau omega = n} := by
      ext omega
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro homega
        have ht : tau omega < ⊤ := hfinite homega
        have htne : tau omega ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp ht
        lift tau omega to ℕ using htne with n hn
        exact ⟨n, homega, rfl⟩
      · rintro ⟨n, homega, _⟩
        exact homega
    rw [hdecomp]
    exact MeasurableSet.iUnion fun n ↦ le_iSup incrementFiltration n _ (hA n)
  · intro i
    have hdecomp : A ∩ {omega | tau omega ≤ i} =
        ⋃ n : Fin (i + 1), A ∩ {omega | tau omega = (n : ℕ)} := by
      ext omega
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨homega, ht⟩
        have htne : tau omega ≠ ⊤ :=
          WithTop.lt_top_iff_ne_top.mp (ht.trans_lt (WithTop.coe_lt_top i))
        lift tau omega to ℕ using htne with n hn
        have hni : n ≤ i := WithTop.coe_le_coe.mp ht
        exact ⟨⟨n, Nat.lt_succ_of_le hni⟩, homega, rfl⟩
      · rintro ⟨n, homega, hn⟩
        refine ⟨homega, ?_⟩
        rw [hn]
        exact_mod_cast Nat.le_of_lt_succ n.isLt
    change MeasurableSet[incrementFiltration i]
      (A ∩ {omega | tau omega ≤ (i : WithTop ℕ)})
    rw [hdecomp]
    exact MeasurableSet.iUnion fun n ↦
      incrementFiltration.mono (Nat.le_of_lt_succ n.isLt) _ (hA n)

theorem secondStage_condExp_lower
    (delta : ℝ) (m : ℕ) (hm : 2 ≤ m) (r : ℝ)
    (hr : ∀ x : Point, r ≤ fairSteps.real (freshCreationSteps delta m x)) :
    ∀ᵐ omega ∂fairSteps,
      r * (levelEventSteps m 2).indicator (1 : StepPath → ℝ) omega ≤
        (fairSteps[(levelEventSteps m 3).indicator (1 : StepPath → ℝ) |
          (isStoppingTime_levelTimeSteps m 2).measurableSpace]) omega := by
  let target := fairSteps[(levelEventSteps m 3).indicator (1 : StepPath → ℝ) |
    (isStoppingTime_levelTimeSteps m 2).measurableSpace]
  have hfiber (x : Point) : ∀ᵐ omega ∂fairSteps,
      r * (levelEventSteps m 2 ∩
          {omega | secondFavoriteDisplacement m omega = x}).indicator
            (1 : StepPath → ℝ) omega ≤ target omega := by
    let B := levelEventSteps m 2 ∩
      {omega | secondFavoriteDisplacement m omega = x}
    let D := postWithTopStoppingBlock (levelTimeSteps m 2)
      (levelCutoffTime delta m) ⁻¹' freshCreationBlock delta m x
    let E := B ∩ D
    have hBfinite : B ⊆ {omega | levelTimeSteps m 2 omega < ⊤} := by
      intro omega homega
      have hM : omega ∈ levelEventSteps m 2 := homega.1
      change levelTimeSteps m 2 omega < levelTimeSteps (m + 1) 1 omega at hM
      exact hM.trans_le le_top
    have hB : MeasurableSet[(isStoppingTime_levelTimeSteps m 2).measurableSpace] B :=
      measurableSet_stopping_of_atomwise_of_finite
        (isStoppingTime_levelTimeSteps m 2)
        (isMeasurableAtWithTopStopping_levelEventTwo_displacement_fiber m x)
        hBfinite
    have hEmeas : MeasurableSet E :=
      ((isStoppingTime_levelTimeSteps m 2).measurableSpace_le B hB).inter
        ((measurable_postWithTopStoppingBlock (isStoppingTime_levelTimeSteps m 2)
          (levelCutoffTime delta m)) (measurableSet_freshCreationBlock delta m x))
    have hM3meas : MeasurableSet (levelEventSteps m 3) :=
      measurableSet_levelEventSteps m 3 (by omega)
    have hmono :
        fairSteps[E.indicator (1 : StepPath → ℝ) |
            (isStoppingTime_levelTimeSteps m 2).measurableSpace] ≤ᵐ[fairSteps]
          target := by
      apply condExp_mono
      · exact (integrable_const 1).indicator hEmeas
      · exact (integrable_const 1).indicator hM3meas
      · exact Filter.Eventually.of_forall fun omega ↦ by
          by_cases he : omega ∈ E
          · have hm3 : omega ∈ levelEventSteps m 3 :=
              secondStage_freshCreation_fiber_subset_levelEventThree delta m hm x he
            simp [Set.indicator, he, hm3]
          · by_cases hm3 : omega ∈ levelEventSteps m 3 <;>
              simp [Set.indicator, he, hm3]
    have hmarkov := condExp_indicator_inter_postWithTopStoppingBlock
      (isStoppingTime_levelTimeSteps m 2) hB hBfinite
      (levelCutoffTime delta m) (freshCreationBlock delta m x)
    filter_upwards [hmono, hmarkov] with omega hmono_o hmarkov_o
    calc
      r * B.indicator (1 : StepPath → ℝ) omega ≤
          fairSteps.real (freshCreationSteps delta m x) *
              B.indicator (1 : StepPath → ℝ) omega := by
        exact mul_le_mul_of_nonneg_right (hr x) (by
          by_cases h : omega ∈ B <;> simp [Set.indicator, h])
      _ = (fairBlock (levelCutoffTime delta m)
            (freshCreationBlock delta m x)).toReal *
              B.indicator (1 : StepPath → ℝ) omega := by
        rw [fairBlock_freshCreationBlock_toReal_eq]
      _ = (fairSteps[E.indicator (1 : StepPath → ℝ) |
            (isStoppingTime_levelTimeSteps m 2).measurableSpace]) omega := hmarkov_o.symm
      _ ≤ target omega := hmono_o
  have hall : ∀ᵐ omega ∂fairSteps, ∀ x : Point,
      r * (levelEventSteps m 2 ∩
          {omega | secondFavoriteDisplacement m omega = x}).indicator
            (1 : StepPath → ℝ) omega ≤ target omega := by
    rw [ae_all_iff]
    exact hfiber
  filter_upwards [hall] with omega homega
  let x := secondFavoriteDisplacement m omega
  have hx := homega x
  by_cases hM : omega ∈ levelEventSteps m 2
  · simpa [target, x, Set.indicator, hM] using hx
  · simpa [target, x, Set.indicator, hM] using hx

/-- The canonical HLOZ lower theorem.  All restart, two-point-avoidance,
stopping-time, recurrence, and conditional Borel--Cantelli inputs have been
discharged; its sole hypothesis is the planar maximal-local-time lower-tail
estimate (HLOZ Proposition 1.3). -/
theorem ae_frequently_favoriteCount_ge_three_of_lowerDeviation
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk) :
    ∀ᵐ s ∂simpleRandomWalk, ∃ᶠ n in atTop, 3 ≤ favoriteCount s n := by
  let delta : ℝ := 1 / 10
  let q : ℕ → ℝ := fun m ↦ 1 / (600 * Real.sqrt ((m + 1 : ℕ) : ℝ))
  have hdeltaPos : 0 < delta := by norm_num [delta]
  have hdeltaLt : delta < 2 / 5 := by norm_num [delta]
  have hfresh0 := eventually_freshCreationSteps_lower_inv_sqrt
    hProp13 delta hdeltaPos hdeltaLt
  have hfresh : ∀ᶠ m : ℕ in atTop, ∀ x : Point,
      q m ≤ fairSteps.real (freshCreationSteps delta (m + 1) x) := by
    have hshift := (tendsto_add_atTop_nat 1).eventually hfresh0
    simpa [q, Nat.add_comm] using hshift
  have hsecond : ∀ᶠ m in atTop, ∀ᵐ omega ∂fairSteps,
      q m ≤
        (fairSteps[(levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) | levelFiltration m]) omega := by
    filter_upwards [hfresh, eventually_ge_atTop 1] with m hfresh_m hm
    have hstage := firstStage_condExp_lower delta (m + 1) (by omega)
    rw [levelFiltration_apply]
    filter_upwards [hstage] with omega hstage_o
    exact (hfresh_m 0).trans hstage_o
  have hthird : ∀ᶠ m in atTop, ∀ᵐ omega ∂fairSteps,
      q m * (levelEventSteps (m + 1) 2).indicator
          (1 : StepPath → ℝ) omega ≤
        (fairSteps[(levelEventSteps (m + 1) 3).indicator
          (1 : StepPath → ℝ) |
            (isStoppingTime_levelTimeSteps (m + 1) 2).measurableSpace]) omega := by
    filter_upwards [hfresh, eventually_ge_atTop 1] with m hfresh_m hm
    exact secondStage_condExp_lower delta (m + 1) (by omega) (q m) hfresh_m
  apply ae_frequently_favoriteCount_ge_three_of_eventually_two_stage_bounds
    q q (fun m ↦ by positivity) (c := 1 / 360000) (by norm_num)
    (fun m ↦ ?_) hsecond hthird
  have hsqrt : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = (m + 1 : ℕ) := by
    rw [Real.sq_sqrt]
    positivity
  dsimp only [q]
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

end Erdos1165.LowerConclusion
