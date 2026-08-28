import Wikipedia.HopfProblem.DegreeCollapseRelativeLevelIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelBasinTransport
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization

/-!
# A relative level move gives an actual adapted surgery system

Construct the modified field and complete flow, then rebuild arbitrarily
small separated surgery windows with the exact prescribed flow and the
original signed critical charts. Backward labels are unchanged at the
original cut; forward labels transform by the prescribed level map. Every
protected level point retains its complete original orbit set.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_relative_level_surgery_system
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) {c : ℝ} (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (z : {y : M // f y = c}) (ε : criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := RegularLevel.chartedSpace hf hc
    ∀ (D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = c} {y : M // f y = c} ∞)
      (K P : Set {y : M // f y = c}), IsCompact K → SupportedRelativeIsotopy D K P →
      ∃ T : AdaptedSurgeryWindows E f,
        (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
        (∀ p ∈ criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
        (∀ x : {y : M // f y = c}, ∀ p : M,
          Tendsto (fun t => T.flow t x.val) atBot (𝓝 p) ↔
            Tendsto (fun t => S.flow t x.val) atBot (𝓝 p)) ∧
        (∀ x : {y : M // f y = c}, ∀ p : M,
          Tendsto (fun t => T.flow t x.val) atTop (𝓝 p) ↔
            Tendsto (fun t => S.flow t (D x).val) atTop (𝓝 p)) ∧
        ∀ x ∈ P, range (fun t => T.flow t x.val) = range (fun t => S.flow t x.val) := by
  let _ := RegularLevel.chartedSpace hf hc
  dsimp only
  intro D K P hK I
  obtain ⟨a, b, ha, hb, hband⟩ := S.regular_interval_around_level hc
  obtain ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry,
      hV, hG, hzero, hdesc, hgerms, -, hend, -, hleft, hright, hprotected⟩ :=
    FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral ha hb hband hc z D K P hK I
  have hmodel (p : criticalPoints E f) :
      ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ := exists_adapted_windows_with_prescribed_flow_lt
    hf hm S.distinct hV G hG (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc
      (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy
    S.flow H G Subtype.val D (fun x p => (hgeometry x).2.1 p)
      (fun x p => (hgeometry x).2.2 p) hend hleft hright
  refine ⟨T, hcharts, hradii, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x p
    rw [hflow]
    exact hback x p
  · intro x p
    rw [hflow]
    exact hforward x p
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = (fun t => H t x.val) :=
      funext (fun t => hprotected x hx t)
    rw [heq]
    exact (hgeometry x.val).1

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
