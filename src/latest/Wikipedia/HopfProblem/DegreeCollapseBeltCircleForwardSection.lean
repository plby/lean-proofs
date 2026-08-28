import Wikipedia.HopfProblem.DegreeCollapseEmbeddedLevelTransport
import Wikipedia.HopfProblem.DegreeCollapseCircleStandardParametrization

/-!
# The transported belt loop meets the whole forward basin exactly once

The circle and every crossing orbit are constructed in the original flow.
The actual belt-basin identity and invariance of endpoints along an orbit
turn the unique geometric belt crossing into a whole-basin statement in
the middle level. No upper index bound or disk filling is used here.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_middle_circle_single_forward_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ δ : C(Hemisphere.Sphere 1, {y : M // f y = a}),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ ∧ Injective δ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) ∧
      ∃ z₀ : Hemisphere.Sphere 1,
        ∀ z, Tendsto (fun t => S.flow t (δ z).val) atTop (𝓝 q.val) ↔ z = z₀ := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf ha
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
  have hpos : Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1 := Fact.out
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  have hn : 2 < n := by omega
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, -⟩ :=
    S.exists_transverse_belt_circle_reaching_level hf p q hp hq n u hbranches hqa ha hlow
      hn (by omega) (by omega)
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data q).upper_regular ha γ (1 : Circle)
      hγ hγi hγd hreach
  have hforward (z : Circle) :
      Tendsto (fun t => S.flow t (Γ z).val) atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := hflow z
    have hbasin : Tendsto (fun s => S.flow s (Γ z).val) atTop (𝓝 q.val) ↔
        γ z ∈ range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact (flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
        (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  let δ : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨Γ ∘ standardCircleParametrization, Γ.continuous.comp standardCircleParametrization.continuous⟩
  refine ⟨δ, contMDiff_comp_standardCircle hΓ, injective_comp_standardCircle hΓi,
    injective_derivative_comp_standardCircle hΓ hΓd, standardCircleParametrization.symm z₀, ?_⟩
  intro z
  change Tendsto (fun t => S.flow t (Γ (standardCircleParametrization z)).val)
    atTop (𝓝 q.val) ↔ _
  rw [hforward]
  constructor
  · intro hz
    exact standardCircleParametrization.injective
      (hz.trans (standardCircleParametrization.apply_symm_apply z₀).symm)
  · rintro rfl
    exact standardCircleParametrization.apply_symm_apply z₀

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
