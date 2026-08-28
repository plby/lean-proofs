import Wikipedia.HopfProblem.DegreeCollapseTransverseMiddleBeltLoop
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementTransverseSheets
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount

/-!
# Constructed transverse level data for the one/two handle trade

The actual belt loop, its forward-basin sheet, the new attaching section,
and their native ambient isotopy jointly supply a unit whole-level count
and transverse local basin sheets. No transverse sheet or circle placement
is an input. The original middle cut is used only to construct disk fillings.
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
theorem exists_handle_trade_transverse_level_data
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
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
        Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 ∧
      ∃ (α : C(Hemisphere.Sphere 1, {y : M // g y = a})) (z₀ : Hemisphere.Sphere 1)
        (β : sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → {y : M // g y = a})
        (v : sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ α ∧
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧ β v = α z₀ ∧
        NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) α β z₀ v ∧
        (∀ z, Tendsto (fun t => T.flow t (α z).val) atBot (𝓝 r.val)) ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => T.flow t (P (β w)).val) atTop (𝓝 q.val)) ∧
        ∀ x : {y : M // g y = a}, Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) →
          Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 m.val) ∨
          Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop hg hdim m q hm hq u hbranches hqa hgr hnewlow
  obtain ⟨α, hα, -, -, hrange, P, hP, hplace, hplacement⟩ :=
    exists_new_attaching_circle_placement S T hf hg e hdim hfr hgr heq hhigh hlow
      r har hgap δ hδ hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hPβ⟩ := exists_transverse_sheet_of_circle_placement P
    (hα.mdifferentiableAt (by simp)) hβ₀ hplace hcross₀ htrans₀
  refine ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle,
    α, z₀, β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hPβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
