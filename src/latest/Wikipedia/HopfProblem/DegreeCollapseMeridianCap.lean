import Wikipedia.HopfProblem.DegreeCollapseBeltComplementDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseCircleFillingAvoidance

/-!
# A cap for the actual meridian in the whole belt complement

Simple connectivity of the original lower level supplies a disk. Relative
avoidance removes the full attaching circle without changing its boundary.
The inverse native complement transport gives a cap in the original upper
level, avoiding the whole belt and with the exact parametrized meridian.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_native_belt_meridian_cap
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)]
    [SimplyConnectedSpace (S.data p).LowerLevel]
    (hdim : 6 ≤ Module.finrank ℝ E)
    (e : Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1)
      (sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ)) :
    ∃ K : C(Hemisphere.Ball 2, (S.data p).UpperLevel),
      (∀ z : Hemisphere.Sphere 1,
        K ⟨z.val, sphere_subset_closedBall z.property⟩ =
          nativeUpperMeridian S p v s (e z)) ∧
      ∀ z, K z ∉ range (S.data p).surgery.beltSphere := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ := RegularLevel.isManifold hf (S.data p).lower_regular
  let u := e (SphereCube.point 1)
  obtain ⟨D, hsource, htarget, _, _⟩ :=
    S.exists_native_surgery_complement_transport hf p u v
  let γ : C(Hemisphere.Sphere 1, (S.data p).UpperLevel) :=
    (nativeUpperMeridian S p v s).comp ⟨e, e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    (nativeUpperMeridian_smooth_immersive S hf p 1 v s hs).1.comp e.contMDiff
  have hγsource (z : Hemisphere.Sphere 1) : γ z ∈ D.source := by
    rw [hsource]
    exact nativeUpperMeridian_avoids_belt S p v s hs (e z)
  let γL : C(Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨fun z => D (γ z),
      D.contMDiffOn_toFun.continuousOn.comp_continuous γ.continuous hγsource⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γL :=
    D.contMDiffOn_toFun.comp_contMDiff hγ hγsource
  let β : C(Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    (S.data p).surgery.attachingSphere.comp ⟨e, e.continuous⟩
  have hβ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ β :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hrange : range β = range (S.data p).surgery.attachingSphere := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e z, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := e.surjective w
      exact ⟨z, rfl⟩
  have hdisj : Disjoint (range γL) (range β) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z, rfl⟩ hy
    have hz := D.map_source (hγsource z)
    rw [htarget] at hz
    exact hz (hrange ▸ hy)
  have hdimL : 4 < Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨g, hg, hboundary, havoid⟩ := exists_circle_filling_avoiding_sphere
    γL hγL β hβ hdisj hdimL (by omega)
  have hgtarget (z : Hemisphere.Ball 2) : g z.val ∈ D.target := by
    rw [htarget, ← hrange]
    exact havoid z
  let K : C(Hemisphere.Ball 2, (S.data p).UpperLevel) :=
    ⟨fun z => D.symm (g z.val),
      D.contMDiffOn_invFun.continuousOn.comp_continuous
        (g.continuous.comp continuous_subtype_val) hgtarget⟩
  refine ⟨K, ?_, ?_⟩
  · intro z
    change D.symm (g z.val) = γ z
    rw [hboundary]
    exact D.left_inv' (hγsource z)
  · intro z
    have hz := D.map_target (hgtarget z)
    rwa [hsource] at hz

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
