import Wikipedia.HopfProblem.DegreeCollapseThreeBeltHomologicalReduction
import Wikipedia.HopfProblem.DegreeCollapseUnitConsecutiveLevelCancellation
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementTransverseSheets

/-!
# An actual unit three-handle coordinate cancels the consecutive four-handle

The entire backward basin is represented by the original embedded attaching
three-sphere. Its native collapse coordinate supplies the unit signed count.
Construct transverse preparation, the complete finite Whitney sequence, the
unique whole-level crossing, the realized flow, and transverse ambient basin
tubes. Relative native cancellation removes exactly the original pair while
fixing the full upper germ and literal strict sublevel. No intersection or
Whitney data, and no exclusion of other lower endpoints, are assumed.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.cancel_three_four_pair_of_unit_coordinate
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ s : criticalPoints E f, ¬ (f p < f s ∧ f s < f q))
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3)
    (hqindex : nativeMorseIndex E f q = 4) {b : ℝ} (hqb : f q < b)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (α : C(Hemisphere.Sphere 3, (S.data p).UpperLevel))
    (hfull : ∀ y : (S.data p).UpperLevel, y ∈ range α ↔
      Tendsto (fun t => S.flow t y.val) atBot (𝓝 q.val))
    (hunit : (MiddleBasis.collapseCoordinate (S.data p) 1 hf.continuous hindex
      (threeSectionClass α)).natAbs = 1) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ α → Injective α →
    (∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α x)) →
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ w, w ∈ criticalPoints E g ↔ w ∈ criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
      (∀ w ∈ criticalPoints E g, nativeMorseIndex E g w = nativeMorseIndex E f w) ∧
      (∀ w, b ≤ f w → g =ᶠ[𝓝 w] f) ∧ ∀ w, g w < b ↔ f w < b := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hs := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hα hinj hi
  obtain ⟨D, δ, x, hD, hplace, hgood, hpoints, _⟩ :=
    exists_single_three_belt_intersection_of_unit_coordinate (S.data p) hf hdim
      hindex hnull α hunit hα hinj hi
  have hplacement (y : (S.data p).UpperLevel) :
      Tendsto (fun t => S.flow t y.val) atBot (𝓝 q.val) ↔ D y ∈ range δ := by
    rw [← hfull]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hplace z⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, D.injective ((hplace z).symm.trans hz)⟩
  have hsingle (z : Hemisphere.Sphere 3) :
      Tendsto (fun t => S.flow t (δ z).val) atTop (𝓝 p.val) ↔ z = x := by
    rw [S.belt_basin_iff hf p]
    change z ∈ (S.data p).beltIntersectionPoints 3 δ ↔ z = x
    rw [hpoints]
    rfl
  have hcount := unit_level_count_of_circle_placement S.flow D.toEquiv δ x hplacement hsingle
  have hx : x ∈ (S.data p).beltIntersectionPoints 3 δ := by rw [hpoints]; exact mem_singleton x
  obtain ⟨v, hv⟩ := hx
  obtain ⟨β, hβ, hcross, htrans, hDβ⟩ := exists_transverse_sheet_of_circle_placement D
    (hα.mdifferentiableAt (by simp))
    (((S.data p).belt_smooth hf 3).mdifferentiableAt (by simp))
    (fun z => (hplace z).symm) hv (hgood.2.2.2 x v)
  have hαbasin : ∀ᶠ u in 𝓝 x,
      Tendsto (fun t => S.flow t (α u).val) atBot (𝓝 q.val) :=
    Filter.Eventually.of_forall (fun u => (hfull (α u)).mp (mem_range_self u))
  have hβbasin : ∀ᶠ u in 𝓝 v,
      Tendsto (fun t => S.flow t (D (β u)).val) atTop (𝓝 p.val) := by
    apply Filter.Eventually.of_forall
    intro u
    apply (S.belt_basin_iff hf p (D (β u))).mpr
    exact ⟨u, (hDβ u).symm⟩
  have hidx : nativeMorseIndex E f q = nativeMorseIndex E f p + 1 := by
    rw [hqindex, nativeMorseIndex_eq_chart (S.data p).chart, hindex]
  have haq : S.toSurgeryWindows.upper p < f q :=
    (S.toSurgeryWindows.upper_lt_lower p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  exact S.cancel_unit_consecutive_level_isotopy_below_cut hf hm (m := 6) hdim p q
    (S.toSurgeryWindows.value_lt_upper p) haq hqb hconsecutive hidx (S.data p).upper_regular
    D hD hcount α β x v (hα.mdifferentiableAt (by simp)) hβ hcross htrans hαbasin hβbasin

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
