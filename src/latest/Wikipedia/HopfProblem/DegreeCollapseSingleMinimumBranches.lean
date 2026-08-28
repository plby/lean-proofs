import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchPlacement

/-!
# Placing both one-handle branches in the unique minimum basin

The actual zero-sphere has exactly two distinct points. Density of the
minimum basins and supported point isotopies place both attaching points
in minimum basins. When the minimum is unique, both endpoints are that
same original critical point. No connectivity of the attaching level is
needed for this placement.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_distinct_unitSphere_points_of_finrank_one
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) :
    ∃ u v : sphere (0 : V) 1, u ≠ v := by
  obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := UnitSphereEquiv.homeomorph L
  let u : sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  let v : sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  refine ⟨e.symm u, e.symm v, ?_⟩
  intro heq
  have hh : u = v := e.symm.injective heq
  have hval : (1 : ℝ) = -1 := congrArg Subtype.val hh
  norm_num at hval

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.place_one_handle_in_unique_minimum_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hunique : ∀ r : criticalPoints E f, nativeMorseIndex E f r = 0 → r = p) :
    let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      IsotopicToIdentity d ∧ f p < S.toSurgeryWindows.lower q ∧
      ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
          atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hi
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := fun h => huv ((S.data q).attaching_isClosedEmbedding.injective h)
  obtain ⟨d, hd, ⟨r, hr, hru⟩, ⟨s, hs, hsv⟩⟩ :=
    exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpu : Tendsto (fun t => S.flow t (d (α u)).val) atTop (𝓝 p.val) :=
    hunique r hr ▸ hru
  have hpv : Tendsto (fun t => S.flow t (d (α v)).val) atTop (𝓝 p.val) :=
    hunique s hs ▸ hsv
  refine ⟨d, hd, S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu, ?_⟩
  intro w
  rcases unitSphere_eq_two_points_of_finrank_one hi u v huv w with rfl | rfl
  · exact hpu
  · exact hpv

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
