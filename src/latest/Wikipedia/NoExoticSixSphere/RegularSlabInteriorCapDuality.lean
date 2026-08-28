import Wikipedia.NoExoticSixSphere.RegularSlabInteriorEquivalence
import Wikipedia.NoExoticSixSphere.SlabInteriorAtlas
import Wikipedia.NoExoticSixSphere.ManifoldCompactSupportDuality

/-!
# Actual interior cap duality with homology of the original slab

The strict-time interior carries the native regular-fiber charts.
Cap with its constructed compact-supported fundamental classes is
bijective. Composing with the actual interior inclusion gives a
bijective map to homology of the original slab, by the proved collar
homotopy equivalence. This is still a compact-support statement; the
comparison with cohomology relative to the actual boundary remains
a separate obligation.
-/

noncomputable section

open Function Module TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))

@[instance_reducible]
def interiorEuclideanAtlas : ChartedSpace (EuclideanSpace ℝ (Fin (n + 3)))
    (CylinderFiberSlab.interiorDomain d.map z s t) :=
  letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (n + 3) hd
  ModelAtlasTransport.atlas (H := EuclideanSpace ℝ (Fin (n + 3)))
    (CylinderFiberSlab.interiorHomeomorph d.map z s t)

theorem interiorEuclideanAtlas_isManifold : letI := d.interiorEuclideanAtlas n hd;
    IsManifold (𝓡 (n + 3)) ∞ (CylinderFiberSlab.interiorDomain d.map z s t) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (n + 3) hd
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map (n + 3) hd
  exact ModelAtlasTransport.isManifold
    (CylinderFiberSlab.interiorHomeomorph d.map z s t) (𝓡 (n + 3))

theorem interiorEuclideanAtlas_smooth_ambient : letI := d.interiorEuclideanAtlas n hd;
    ContMDiff (𝓡 (n + 3)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : CylinderFiberSlab.interiorDomain d.map z s t ↦ p.val.val.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (n + 3) hd
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map (n + 3) hd
  let := d.interiorEuclideanAtlas n hd
  have hi : ContMDiff (𝓡 (n + 3)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : CylinderFiberSlab.fiberInterior d.map z s t ↦ p.val.val) :=
    (regularFiber_contMDiff_subtype_val d.map d.smooth_map z d.regular_map
      (n + 3) hd).comp contMDiff_subtype_val
  exact hi.comp (ModelAtlasTransport.contMDiff
    (CylinderFiberSlab.interiorHomeomorph d.map z s t) (𝓡 (n + 3)))

variable [T2Space M]

def interiorCapMap (p q : ℕ) (h : p + q = n + 3) :
    CompactSupportCohomology.Cohomology (CylinderFiberSlab.interiorDomain d.map z s t) p →ₗ[ℤ]
      ModHomology 2 (CylinderFiberSlab.slab d.map z s t) q :=
  letI := d.interiorEuclideanAtlas n hd
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  (modHomologyMap 2 (CylinderFiberSlab.InteriorPush.inclusion d.map z s t) q).comp
    (CompactSupportCapMap.dualityMap (E := EuclideanSpace ℝ (Fin (n + 3))) n
      (CylinderFiberSlab.interiorDomain d.map z s t) p q h)

theorem interiorCapMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Bijective (d.interiorCapMap n hd p q h) := by
  let := d.interiorEuclideanAtlas n hd
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact (d.modHomologyMap_interior_bijective 2 q).comp
    (CompactSupportCapMap.manifold_bijective (E := EuclideanSpace ℝ (Fin (n + 3))) n
      (CylinderFiberSlab.interiorDomain d.map z s t) p q h)

def interiorCapEquiv (p q : ℕ) (h : p + q = n + 3) :
    CompactSupportCohomology.Cohomology (CylinderFiberSlab.interiorDomain d.map z s t) p ≃ₗ[ℤ]
      ModHomology 2 (CylinderFiberSlab.slab d.map z s t) q :=
  LinearEquiv.ofBijective (d.interiorCapMap n hd p q h) (d.interiorCapMap_bijective n hd p q h)

theorem interiorCapEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (d.interiorCapEquiv n hd p q h).toLinearMap = d.interiorCapMap n hd p q h := rfl

end NoExoticSixSphere.RegularCollaredCylinder
