import Wikipedia.HopfProblem.DegreeCollapseMiddleAttachingPassage
import Wikipedia.HopfProblem.DegreeCollapsePuncturedPassageTrace
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelBasinTransport

/-!
# The entire original belt complement flows to the actual lower level

Every upper-level point outside the full belt has a forward endpoint
strictly below the lower surgery level. Separation excludes every other
critical point in the window; convergence to its central point would put
the original point on the belt. The actual common-flow cylinder therefore
constructs a continuous lower-level map on the entire belt complement.
Its orbit characterization determines its values uniquely.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.belt_complement_reaches_lower_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (y : (S.data p).UpperLevel)
    (hy : y ∉ range (S.data p).surgery.beltSphere) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct y.val
  have hyreg : y.val ∉ criticalPoints E f := (S.data p).upper_regular y.val y.property
  have hbelow : f b < S.toSurgeryWindows.lower p := by
    rcases lt_trichotomy (f b) (f p) with h | h | h
    · exact (S.toSurgeryWindows.value_lt_upper ⟨b, hb⟩).trans (S.separated ⟨b, hb⟩ p h)
    · have heq : b = p.val := S.distinct hb p.property h
      subst b
      exact (hy ((S.belt_basin_iff hf p y).mp hforward)).elim
    · have hup : f y.val < f b := by
        rw [y.property]
        exact (S.separated p ⟨b, hb⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨b, hb⟩)
      exact (not_lt_of_ge hup.le (hheights hyreg).1).elim
  have hlow : S.toSurgeryWindows.lower p < f y.val := by
    rw [y.property]
    exact (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward (hlow.trans (hheights hyreg).2) hbelow

theorem AdaptedSurgeryWindows.exists_belt_complement_lower_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
      ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf
    (S.data p).upper_regular (S.data p).lower_regular
    ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hsrc (x : ((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) :
      x.val ∈ P.source :=
    hsource.symm ▸ S.belt_complement_reaches_lower_level hf p x.val x.property
  let D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel) := ⟨fun x => P x.val,
    P.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc⟩
  refine ⟨D, fun x => horbit x.val (hsrc x), ?_⟩
  intro x y t hty
  obtain ⟨s, hs⟩ := horbit x.val (hsrc x)
  have hshared : S.flow 0 (D x).val = S.flow (s - t) y.val := by
    rw [S.flow.map_zero_apply]
    change (P x.val).val = S.flow (s - t) y.val
    rw [← hs, ← hty, ← S.flow.map_add, sub_add_cancel]
  apply Subtype.ext
  exact native_same_level_orbit_points hf S.smooth S.flow S.integral
    (fun z hz => S.descent z ((S.data p).lower_regular z hz)) (D x).property y.property hshared

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
