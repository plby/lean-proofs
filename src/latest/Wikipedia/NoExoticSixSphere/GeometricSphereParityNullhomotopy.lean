import Wikipedia.NoExoticSixSphere.GeometricSphereParity
import Wikipedia.NoExoticSixSphere.ManifoldSmallFourDisk

/-!
# Geometric sphere parity vanishes on every nullhomotopic map

The original chart-contained four-disk supplies a zero-parity embedded
sphere and an actual contraction to its prescribed center. Thus the
homotopy-invariant geometric parity has value zero on constant maps,
without assigning a normalization constant.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricSphereParity_const (x : M) :
    e.geometricSphereParity a r (ContinuousMap.const (Sphere 3) x) = 0 := by
  obtain ⟨f, hf, hi, hd, hz, H⟩ := e.exists_zeroParitySphere_homotopic_const a x
  exact (e.geometricSphereParity_homotopic a r _ f H.symm).trans
    ((e.geometricSphereParity_eq_of_embedding a r f hf hi hd).trans hz)

theorem geometricSphereParity_zero_of_nullhomotopic (f : C(Sphere 3, M)) (x : M)
    (H : f.Homotopic (ContinuousMap.const _ x)) : e.geometricSphereParity a r f = 0 :=
  (e.geometricSphereParity_homotopic a r f _ H).trans (e.geometricSphereParity_const a r x)

end NoExoticSixSphere.EuclideanEmbedding
