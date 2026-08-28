import Wikipedia.HopfProblem.DegreeCollapseDenseRegularLevelBasins
import Wikipedia.HopfProblem.DegreeCollapseDensePointIsotopies
import Wikipedia.HopfProblem.DegreeCollapseOneHandleBasinUniqueness

/-!
# Place an actual component-merging one-handle into two distinct minimum basins

The native regular-level density and supported point motions construct an
ambient isotopy taking both attaching points into minimum basins. The isotopy
preserves their old sublevel components, so the two actual minimum endpoints
are distinct. No flow endpoint, isotopy or transversality is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.forward_limit_below_regular_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ x, f x = a → x ∉ criticalPoints E f)
    (x : {y : M // f y = a}) {p : M}
    (hlim : Tendsto (fun t => S.flow t x) atTop (𝓝 p)) : f p < a := by
  obtain ⟨r, hr, q, hq, -, hqLim, hheight⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct (x : M)
  have hqp : q = p := tendsto_nhds_unique hqLim hlim
  have hh := (hheight (hreg x x.property)).1
  simpa only [hqp, x.property] using hh

open Classical in
theorem AdaptedSurgeryWindows.place_one_handle_in_distinct_minimum_basins
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      IsotopicToIdentity d ∧ ∃ p r : criticalPoints E f,
        nativeMorseIndex E f p = 0 ∧ nativeMorseIndex E f r = 0 ∧ p ≠ r ∧
        f p < S.toSurgeryWindows.lower q ∧ f r < S.toSurgeryWindows.lower q ∧
        Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere u)).val)
          atTop (𝓝 p.val) ∧
        Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere v)).val)
          atTop (𝓝 r.val) ∧
        ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
          Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
            atTop (𝓝 p.val) ∨
          Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
            atTop (𝓝 r.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  let ι : C((S.data q).LowerLevel, {z : M // f z ≤ S.toSurgeryWindows.lower q}) :=
    ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := by
    intro h
    have hh : (S.data q).coreBoundaryMap u = (S.data q).coreBoundaryMap v := congrArg ι h
    exact hnot (hh ▸ Joined.refl _)
  obtain ⟨d, hd, ⟨p, hp, hpu⟩, ⟨r, hr, hrv⟩⟩ :=
    exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu
  have hrq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α v)) hrv
  have hpr : p ≠ r := by
    intro h
    subst r
    let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
    have hnew : Joined (ι (d (α u))) (ι (d (α v))) :=
      joined_sublevel_of_common_forward_limit S.flow hf.continuous
        (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
        (ι (d (α u))) (ι (d (α v))) hpq hpu hrv
    exact hnot (((isotopicToIdentity_joined hd (α u)).map ι.continuous).trans
      (hnew.trans ((isotopicToIdentity_joined hd (α v)).map ι.continuous).symm))
  refine ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, ?_⟩
  intro w
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := fun h => hxy (congrArg α h)
  rcases unitSphere_eq_two_points_of_finrank_one hindex u v huv w with h | h
  · subst w
    exact Or.inl hpu
  · subst w
    exact Or.inr hrv

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
