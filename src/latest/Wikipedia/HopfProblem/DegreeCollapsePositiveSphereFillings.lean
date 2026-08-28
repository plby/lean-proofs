import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelDisks
import Wikipedia.SmoothSixDPoincare.SmoothHomotopyCollars
import Wikipedia.SmoothSixDPoincare.CollaredRadialExtension

/-!
# Actual higher-sphere fillings in the original positive regular level

A supplied nullhomotopy in the strict superlevel gives a smooth global
radial filling with its entire sphere fixed. Relative endpoint avoidance
keeps that boundary and places the whole disk in the actual level basin.
The original flow cylinder then gives a continuous disk in the original
regular level. No embedding or isotopy conclusion is inferred for this
projected disk. No index bound is imposed on the untouched lower half.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_smooth_sphere_filling_of_nullhomotopy
    {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
    {n : ℕ} (γ : C(Hemisphere.Sphere n, N))
    (hγ : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ γ)
    (hnull : ∃ c : N, γ.Homotopic (ContinuousMap.const _ c)) :
    ∃ g : C(Hemisphere.Ambient (n + 1), N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ g ∧
      ∀ z : Hemisphere.Sphere n, g z.val = γ z := by
  obtain ⟨c, ⟨H⟩⟩ := hnull
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  let b := SphereCube.point n
  have hs := RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  exact ⟨⟨RadialFilling.filling H' b, hs.continuous⟩, hs,
    RadialFilling.filling_on_sphere H' b hlo⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_sphere_filling_in_level_basin_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) (hU : ∀ x, x ∈ U ↔ b < f x)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d n : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hself : 2 * (n + 1) < Module.finrank ℝ E)
    (hobstacle : n + 1 + d < Module.finrank ℝ E)
    (γ : C(Hemisphere.Sphere n, U)) (hγ : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ γ)
    (hnull : ∃ c : U, γ.Homotopic (ContinuousMap.const _ c))
    (hlevel : ∀ z, f (γ z).val = a) :
    ∃ g : C(Hemisphere.Ambient (n + 1), U),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, E) ∞ g ∧
      (∀ z : Hemisphere.Sphere n, g z.val = γ z) ∧
      ∀ z : Hemisphere.Ball (n + 1),
        (g z.val).val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary⟩ :=
    exists_smooth_sphere_filling_of_nullhomotopy γ hγ hnull
  let L : Set (Hemisphere.Ambient (n + 1)) := closedBall 0 1
  let C : Set (Hemisphere.Ambient (n + 1)) := sphere 0 1
  have hfixed (z : Hemisphere.Ambient (n + 1)) (hz : z ∈ L ∩ C) :
      (g₀ z).val ∈ FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  obtain ⟨g, hg, hhom, _, _, _, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin_above_cut S hf U hU hreg hhigh hlow g₀ hg₀
      (by simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hself)
      (by simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hobstacle)
      (K := ∅) isCompact_empty (isCompact_closedBall _ _) isClosed_sphere
      (by simp) (by simp) hfixed
  refine ⟨g, hg, ?_, fun z => hbasin z.val (Or.inr z.property)⟩
  intro z
  exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)

theorem exists_actual_sphere_filling_at_level_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) (hU : ∀ x, x ∈ U ↔ b < f x)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d n : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hself : 2 * (n + 1) < Module.finrank ℝ E)
    (hobstacle : n + 1 + d < Module.finrank ℝ E)
    (γ : C(Hemisphere.Sphere n, U)) (hγ : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ γ)
    (hnull : ∃ c : U, γ.Homotopic (ContinuousMap.const _ c))
    (hlevel : ∀ z, f (γ z).val = a) :
    ∃ D : C(Hemisphere.Ball (n + 1), {y : M // f y = a}),
      ∀ z : Hemisphere.Sphere n,
        (D ⟨z.val, sphere_subset_closedBall z.property⟩).val = (γ z).val := by
  obtain ⟨g, _, hboundary, hbasin⟩ := exists_sphere_filling_in_level_basin_above_cut
    S hf U hU hreg hhigh hlow hself hobstacle γ hγ hnull hlevel
  let z₀ : {y : M // f y = a} := ⟨(γ (SphereCube.point n)).val, hlevel (SphereCube.point n)⟩
  let _ := RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Hemisphere.Ball (n + 1) => Φ.symm (g z.val).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp (g.continuous.comp continuous_subtype_val))
      (fun z => htarget.symm ▸ hbasin z)
  let D : C(Hemisphere.Ball (n + 1), {y : M // f y = a}) :=
    ⟨fun z => (Φ.symm (g z.val).val).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : {y : M // f y = a} := ⟨(γ z).val, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = (γ z).val := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val).val).1.val = (γ z).val
  rw [hboundary z]
  exact congrArg (fun q : {y : M // f y = a} × ℝ => q.1.val) hi

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
