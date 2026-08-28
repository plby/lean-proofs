import Wikipedia.SmoothSixDPoincare.GlobalAmbientTransversality
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Disjoint compact smooth images by an actual ambient isotopy

Pad the first source with a sphere on which its map is constant. The proved
complementary-dimensional ambient transversality theorem applies to this
product. At any intersection, its differential would factor through the
two original source tangent spaces, whose total dimension is too small.
Consequently the constructed ambient diffeomorphism removes every crossing.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeTransversality

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  [CompactSpace X] [T2Space X]

/-- The original compact smooth images can be separated by a constructed ambient isotopy. -/
theorem exists_ambient_avoiding_diffeomorph {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞, SupportedDiffeomorph.IsotopicToIdentity e ∧
      Disjoint (range (e ∘ f)) (range g) := by
  let m := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let F : X × Hemisphere.Sphere m → N := fun z => f z.1
  have hF : ContMDiff (I.prod (𝓡 m)) J ∞ F := hf.comp contMDiff_fst
  have hd : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin m)) + Module.finrank ℝ Z =
      Module.finrank ℝ G := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    dsimp [m]
    omega
  obtain ⟨e, hiso, ht⟩ := exists_ambient_transverse_diffeomorph hF hg hd
  refine ⟨e, hiso, disjoint_left.mpr ?_⟩
  rintro _ ⟨x, rfl⟩ ⟨y, hxy⟩
  let u : Hemisphere.Sphere m := Hemisphere.point true
    ⟨0, by simp [Metric.mem_closedBall]⟩
  let L : D →L[ℝ] G := mfderiv I J (e ∘ f) x
  let Q : Z →L[ℝ] G := mfderiv I' J g y
  let P : (D × EuclideanSpace ℝ (Fin m)) →L[ℝ] G :=
    mfderiv (I.prod (𝓡 m)) J (e ∘ F) (x, u)
  have hs : Surjective (P.coprod Q) := ht (x, u) y hxy
  have heF : MDifferentiableAt I J (e ∘ f) x :=
    (e.contMDiff.comp hf).mdifferentiable (by simp) x
  have hder : P = L.comp (ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin m))) := by
    change mfderiv (I.prod (𝓡 m)) J ((e ∘ f) ∘ Prod.fst) (x, u) = _
    rw [mfderiv_comp (x, u) heF mdifferentiableAt_fst, mfderiv_fst]
    rfl
  have hsmall : Surjective (L.coprod Q) := by
    intro v
    obtain ⟨⟨⟨a, b⟩, c⟩, hv⟩ := hs v
    refine ⟨(a, c), ?_⟩
    change L a + Q c = v
    change P (a, b) + Q c = v at hv
    rw [hder] at hv
    exact hv
  have hbound := LinearMap.finrank_le_finrank_of_surjective
    (f := (L.coprod Q).toLinearMap) hsmall
  rw [Module.finrank_prod] at hbound
  omega

end Wikipedia.SmoothSixDPoincare.NativeTransversality
