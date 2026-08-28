import Wikipedia.HopfProblem.DegreeCollapseTwoSpherePoleCap
import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianDisk

/-!
# The retained meridian is embedded and immersive on the protected cap

The zero set of the actual smooth pole cutoff lies strictly inside the
cap on which the original sphere has the meridian-disk formula. Tail
coordinates and the original native disk therefore control every protected
point, including the boundary of the cutoff's zero set.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] in
theorem retained_meridian_injective_on_protected_cap
    (S : AdaptedSurgeryWindows E f) (p : criticalPoints E f)
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (S.data p).chart.NegativeCoordinates)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ))
    (γ : Hemisphere.Sphere 2 → (S.data p).UpperLevel)
    (hformula : ∀ x ∈ fixedPoleCap,
      γ x = nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) :
    InjOn γ {x | poleCutoff x = 0} := by
  intro x hx y hy hxy
  have hxhead := (poleCutoff_zero_iff x).mp hx
  have hyhead := (poleCutoff_zero_iff y).mp hy
  have hxc : x ∈ fixedPoleCap := by change x.val 0 ≤ -(1 / 2 : ℝ); linarith
  have hyc : y ∈ fixedPoleCap := by change y.val 0 ≤ -(1 / 2 : ℝ); linarith
  have hxn : x ∈ negativeHemisphere := by change x.val 0 < 0; linarith
  have hyn : y ∈ negativeHemisphere := by change y.val 0 < 0; linarith
  rw [hformula x hxc, hformula y hyc] at hxy
  exact tail_injective_negative hxn hyn
    (L.injective (nativeBeltMeridianDisk_injective S p v s hs hs0 hxy))

theorem retained_meridian_immersive_on_protected_cap
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (S.data p).chart.NegativeCoordinates)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ))
    (γ : Hemisphere.Sphere 2 → (S.data p).UpperLevel)
    (hformula : ∀ x ∈ fixedPoleCap,
      γ x = nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ∀ x, poleCutoff x = 0 →
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro x hx
  have hxhead : x.val 0 ≠ 0 := by
    have hh := (poleCutoff_zero_iff x).mp hx
    linarith
  apply immersive_germ_of_tail L (nativeBeltMeridianDisk S p v s hs)
    (nativeBeltMeridianDisk_smooth S hf p v s hs)
    (nativeBeltMeridianDisk_immersive S hf p v s hs hs0) γ x hxhead
  filter_upwards [poleCutoff_zero_fixed_germ x hx] with y hy
  exact hformula y hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
