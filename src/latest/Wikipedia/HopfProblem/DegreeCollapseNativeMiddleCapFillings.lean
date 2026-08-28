import Wikipedia.HopfProblem.DegreeCollapseOrbitCapFilling

/-!
# Controlled fillings of the actual middle attaching and belt spheres

The native signed hitting time is continuous on the whole sphere because
every point reaches the cap level. The controlled cone construction gives
an actual disk filling, with its exact original boundary and its entire
image confined to the original orbits plus the appropriate extremal disk.
Both directions use the same constructed flow and original atlas.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Nonempty (sphere (0 : V) 1)]

theorem exists_native_orbit_cap_filling {f : M → ℝ} (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ x, f x = a → x ∉ criticalPoints E f)
    (γ : C(sphere (0 : V) 1, M))
    (hreach : ∀ z, γ z ∈ FlowCancellation.levelBasin S.flow f a)
    (C : Set M) [ContractibleSpace C] (hlevel : ∀ x, f x = a → x ∈ C) :
    ∃ K : C(closedBall (0 : V) 1, M),
      (∀ z : sphere (0 : V) 1, K ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z) ∧
      ∀ z, K z ∈ orbitSaturation S.flow γ ∪ C := by
  obtain ⟨-, htime, -⟩ := FlowCancellation.smooth_signed_level_time hf S.smooth
    S.flow S.integral (fun x hx => S.descent x (ha x hx))
  let τ : C(sphere (0 : V) 1, ℝ) :=
    ⟨fun z => FlowCancellation.signedLevelTime S.flow f a (γ z),
      htime.continuousOn.comp_continuous γ.continuous hreach⟩
  apply exists_orbit_cap_filling S.flow γ τ C
  intro z
  exact hlevel _ (FlowCancellation.signedLevelTime_hits S.flow f a (hreach z))

namespace SeparatedSystem

variable [Nonempty M] (D : SeparatedSystem E M)

def attachingMap (p : criticalPoints E D.function) :
    C(sphere (0 : (D.windows.data p).chart.NegativeCoordinates) 1, M) :=
  ⟨fun u => ((D.windows.data p).surgery.attachingSphere u).val,
    continuous_subtype_val.comp (D.windows.data p).surgery.attachingSphere.continuous⟩

def beltMap (p : criticalPoints E D.function) :
    C(sphere (0 : (D.windows.data p).chart.PositiveCoordinates) 1, M) :=
  ⟨fun u => ((D.windows.data p).surgery.beltSphere u).val,
    continuous_subtype_val.comp (D.windows.data p).surgery.beltSphere.continuous⟩

theorem exists_attaching_cap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    ∃ K : C(closedBall (0 : (D.windows.data p).chart.NegativeCoordinates) 1, M),
      (∀ z : sphere (0 : (D.windows.data p).chart.NegativeCoordinates) 1,
        K ⟨z.val, sphere_subset_closedBall z.property⟩ = D.attachingMap p z) ∧
      ∀ z, K z ∈ orbitSaturation D.windows.flow (D.attachingMap p) ∪
        {x | D.function x ≤ D.lowerCut} := by
  let _ : Fact (Module.finrank ℝ (D.windows.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (D.windows.data p).chart).symm.trans hp⟩
  let _ : Nonempty (sphere (0 : (D.windows.data p).chart.NegativeCoordinates) 1) :=
    ⟨SphereCoordinates.standardParametrization (D.windows.data p).chart.NegativeCoordinates 2
      (Hemisphere.point true ⟨0, by simp⟩)⟩
  let _ : ContractibleSpace {x : M | D.function x ≤ D.lowerCut} :=
    D.lowerDisk.contractibleSpace
  exact exists_native_orbit_cap_filling D.windows D.smooth D.lowerCut_regular (D.attachingMap p)
    (D.attaching_reaches_lower_cap p hp) {x | D.function x ≤ D.lowerCut}
      (fun x hx => hx.le)

theorem exists_belt_cap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    ∃ K : C(closedBall (0 : (D.windows.data p).chart.PositiveCoordinates) 1, M),
      (∀ z : sphere (0 : (D.windows.data p).chart.PositiveCoordinates) 1,
        K ⟨z.val, sphere_subset_closedBall z.property⟩ = D.beltMap p z) ∧
      ∀ z, K z ∈ orbitSaturation D.windows.flow (D.beltMap p) ∪
        {x | D.upperCut ≤ D.function x} := by
  have hneg := (nativeMorseIndex_eq_chart (D.windows.data p).chart).symm.trans hp
  have hsplit := (D.windows.data p).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (D.windows.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hd := D.dimension; omega⟩
  let _ : Nonempty (sphere (0 : (D.windows.data p).chart.PositiveCoordinates) 1) :=
    ⟨SphereCoordinates.standardParametrization (D.windows.data p).chart.PositiveCoordinates 2
      (Hemisphere.point true ⟨0, by simp⟩)⟩
  let _ : ContractibleSpace {x : M | -D.function x ≤ -D.upperCut} :=
    D.upperDisk.contractibleSpace
  obtain ⟨K, hK, himage⟩ := exists_native_orbit_cap_filling D.windows D.smooth
    D.upperCut_regular (D.beltMap p) (D.belt_reaches_upper_cap p hp)
      {x | -D.function x ≤ -D.upperCut} (fun x hx => by
        change -D.function x ≤ -D.upperCut
        exact neg_le_neg hx.ge)
  refine ⟨K, hK, ?_⟩
  intro z
  rcases himage z with h | h
  · exact Or.inl h
  · right
    change D.upperCut ≤ D.function (K z)
    change -D.function (K z) ≤ -D.upperCut at h
    exact neg_le_neg_iff.mp h

end SeparatedSystem
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
