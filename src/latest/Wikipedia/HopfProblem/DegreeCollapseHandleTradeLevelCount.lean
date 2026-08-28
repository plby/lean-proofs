import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount
import Wikipedia.HopfProblem.DegreeCollapseBeltCircleForwardSection

/-!
# Constructing a unit middle-level count for the one/two handle trade

The target circle is constructed from the selected one-handle's actual belt
and minimum branches. The new two-handle's entire backward-basin section is
placed on it by the proved circle isotopy, using the old middle-level cut.
Thus the actual whole-level intersection count is one, without a prescribed
target circle, attaching-disk identification, or connecting orbit.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem exists_handle_trade_unit_level_count
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (u : sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) atTop (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : criticalPoints E g, g z < g r → g z < a)
    (hnewlow : ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    let _ := RegularLevel.chartedSpace hg hgr
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // g y = a} {y : M // g y = a} ∞,
      IsotopicToIdentity P ∧
      {x : {y : M // g y = a} | Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ∧
        Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, hsingle⟩ := T.exists_middle_circle_single_forward_basin
    hg hdim m q hm hq 4 u hbranches hqa hgr hnewlow
  obtain ⟨Γ, -, -, -, -, P, hP, -, hplacement⟩ := exists_new_attaching_circle_placement
    S T hf hg e hdim hfr hgr heq hhigh hlow r har hgap δ hδ hδi hδd
  exact ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
