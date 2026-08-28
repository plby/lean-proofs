import Wikipedia.HopfProblem.DegreeCollapseNativeTransverseDimension
import Wikipedia.SmoothSixDPoincare.GlobalAmbientTransversality
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Ambient avoidance from complementary transversality and an ignored sphere

When two compact native sheets have total dimension smaller than the
target, enlarge the first source by a compact sphere of the missing
dimension and let the map ignore that factor. The existing complementary
transversality theorem gives an actual ambient isotopy. Removing the
ignored factor retains transversality, and the original strict dimension
inequality excludes every intersection.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_ambient_disjoint_diffeomorph_of_dimension {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞, SupportedDiffeomorph.IsotopicToIdentity e ∧
      Disjoint (range (e ∘ f)) (range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) +
      Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨e, he, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph hf' hg hdim'
  have htrans : ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Hemisphere.Sphere d := Hemisphere.point true ⟨0, by simp [DiskDouble.Disk]⟩
    apply native_transverse_of_ignored_factor (I'' := 𝓡 d) w
      ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, he, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
