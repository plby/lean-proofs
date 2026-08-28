import Wikipedia.HopfProblem.DegreeCollapseHigherMiddleFamily
import Wikipedia.HopfProblem.DegreeCollapseIndexFourBasinFamily

/-!
# Lift the original four-handle basin family with exact parameters

Every common-cut point with a higher backward endpoint crosses the selected
upper level. Compactness and fullness of each old basin section force all
native attaching directions to reach the old cut; hence the lifted family
still covers every labelled basin on the new level. The exact old sphere
parameters are retained, along with smoothness, immersion and disjointness.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.four_backward_basin_reaches_compact_section
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (α : C(S₃, {y : M // f y = a}))
    (hfull : ∀ y, y ∈ range α ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val))
    {x : M} (hx : x ∉ criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)) :
    x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 3 ha α
    (Hemisphere.point true ⟨0, by simp⟩) hfull
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p hx hback
  let y : (S.data p).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Tendsto (fun s => S.flow s y.val) atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff S.flow t x p.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p y).mp hyback
  apply (FlowCancellation.levelBasin_flow_iff S.flow f a t x).mp
  change y.val ∈ FlowCancellation.levelBasin S.flow f a
  rw [← hu]
  exact hreach u

theorem AdaptedSurgeryWindows.exists_higher_four_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f) (j₀ : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4) (hpb : ∀ j, b < f (p j))
    (α : Fin n → C(S₃, {y : M // f y = a}))
    (hα : IsNativeFourBasinFamily S hf ha p (fun j => α j)) :
    ∃ β : Fin n → C(S₃, {y : M // f y = b}),
      IsNativeFourBasinFamily S hf hb p (fun j => β j) ∧
      ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have hreach (j : Fin n) (x : S₃) :
      (α j x).val ∈ FlowCancellation.levelBasin S.flow f b := by
    apply S.backward_basin_reaches_intermediate_cut hf
      ((hfull j (α j x)).mp (mem_range_self x))
    · simpa only [(α j x).property] using hab
    · exact hpb j
  let x₀ : S₃ := Hemisphere.point true ⟨0, by simp⟩
  obtain ⟨t₀, ht₀⟩ := hreach j₀ x₀
  obtain ⟨β, hβs, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb (α j₀ x₀)
      ⟨S.flow t₀ (α j₀ x₀).val, ht₀⟩ (fun j => α j) hs
      (fun j => (he j).injective) hi hpair hreach
  refine ⟨fun j => ⟨β j, (hβs j).continuous⟩,
    ⟨hβs, hβe, hβi, hβpair, ?_⟩, horbit⟩
  intro j
  apply S.transported_basin_image_of_reaching hf hb (p j).val (α j) (β j)
    (hfull j) (horbit j)
  intro y hy
  exact S.four_backward_basin_reaches_compact_section hf (p j) (hp j) ha (α j) (hfull j)
    (hb y.val y.property) hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

