import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyFraming
import Wikipedia.SmoothSixDPoincare.CompatibleWhitneyChart

/-!
# Exact nonlinear Whitney coordinates for the original immersed branches

The native crossing signs construct the full compatible chart, including
exact recognition of both whole compact branch images. The source maps
remain the original immersion restricted to its selected patches.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

variable {G E M N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, G) N))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)
  {F : N → M} {U V : Set N} {α β : C(ℝ, N)}
  {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) (F '' U) (F '' V) (F ∘ α) k₀ k₁}
  {l : CleanStripPatch (E := E) (F '' V) (F '' U) (F ∘ β) l₀ l₁}
  (tube : TubularBigon (E := E) (F '' U) (F '' V) (F ∘ α) (F ∘ β) k.map l.map h)
  (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' U) k.map)
  (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' V) l.map)

include J d e

theorem nonempty_compatibleChart_of_opposite_native_signs
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hUc : IsCompact U) (hVc : IsCompact V)
    (hα : MapsTo α (Icc (0 : ℝ) 1) (interior U))
    (hβ : MapsTo β (Icc (0 : ℝ) 1) (interior V))
    (ht : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (β t)).coprod
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (α t))))
    (hsign : intersectionSign oN oM K F (α 0) (β 0) ≠
      intersectionSign oN oM K F (α 1) (β 1)) :
    Nonempty (TubularBigon.CompatibleChart tube) :=
  tube.nonempty_compatibleChart_of_opposite_corner_signs d e
    (hUc.image hF.continuous).isClosed (hVc.image hF.continuous).isClosed
    (opposite_native_signs_imply_opposite_corner_determinants oN oM J K tube d e
      hF hi hα hβ ht hsign)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
