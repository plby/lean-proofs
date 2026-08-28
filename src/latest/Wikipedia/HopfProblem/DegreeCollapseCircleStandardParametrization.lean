import Wikipedia.HopfProblem.DegreeCollapseStandardBeltCircle

/-!
# Reusable native Euclidean parametrization of a complex unit circle

These small derivative lemmas retain arbitrary target maps and tangent
constraints, so the same parametrization can be used simultaneously before
and after actual flow transport.
-/

noncomputable section

open Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def standardCircleParametrization : Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1) Circle ∞ := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  exact SphereCoordinates.standardParametrization ℂ 1

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem contMDiff_comp_standardCircle {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) :
    ContMDiff (𝓡 1) J ∞ (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.contMDiff

theorem injective_comp_standardCircle {γ : Circle → N} (hγ : Injective γ) :
    Injective (γ ∘ standardCircleParametrization) := hγ.comp standardCircleParametrization.injective

theorem injective_derivative_comp_standardCircle {γ : Circle → N}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (hi : ∀ z, Injective (mfderiv (𝓡 1) J γ z))
    (z : Hemisphere.Sphere 1) :
    Injective (mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z) := by
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
    (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  exact (hi _).comp (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).injective

theorem transverse_comp_standardCircle {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) (B : D →L[ℝ] G)
    (z : Hemisphere.Sphere 1)
    (htrans : Surjective ((mfderiv (𝓡 1) J γ (standardCircleParametrization z) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B)) :
    Surjective ((mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] G :=
    mfderiv (𝓡 1) J γ (standardCircleParametrization z)
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) standardCircleParametrization z
  have hP : Surjective P :=
    (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).surjective
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
    (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  change Surjective ((L.comp P).coprod B)
  exact surjective_coprod_comp_left L B P hP htrans

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
