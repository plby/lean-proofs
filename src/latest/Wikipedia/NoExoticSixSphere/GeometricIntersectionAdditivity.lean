import Wikipedia.NoExoticSixSphere.GeometricIntersectionPinchGenericity
import Wikipedia.NoExoticSixSphere.BasedSphereMapSmoothing

/-!
# Additivity of the geometric intersection number on actual sphere pinches

All three maps may be arbitrary continuous sphere maps. Based smoothing
and the constructed common transverse representative remove the auxiliary
smoothness, transversality, avoidance, and local-constancy hypotheses.
The only condition on the two pinched inputs is equality of their base values.

This is an identity for the actual hemisphere-pinch map. Identification
with native homotopy-group addition and descent to native homology are
separate steps and are not asserted here.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereFold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

theorem sphereIntersectionNumber_pinch_add (v : Sphere 3) (f g k : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v)) :
    sphereIntersectionNumber e r (pinch v f g hbase) k =
      sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k := by
  obtain ⟨F, hF, HF⟩ := exists_smooth_based_sphereMap (antipode v) f
  obtain ⟨G, hG, HG⟩ := exists_smooth_based_sphereMap (antipode v) g
  have hbase' : F (antipode v) = G (antipode v) :=
    (HF.fst_eq_snd (mem_singleton _)).symm.trans
      (hbase.trans (HG.fst_eq_snd (mem_singleton _)))
  have HP := pinch_homotopic v f g F G hbase hbase' HF HG
  calc
    sphereIntersectionNumber e r (pinch v f g hbase) k =
        sphereIntersectionNumber e r (pinch v F G hbase') k :=
      sphereIntersectionNumber_homotopic e r _ _ k k HP (.refl k)
    _ = sphereIntersectionNumber e r F k + sphereIntersectionNumber e r G k :=
      sphereIntersectionNumber_pinch_of_smooth e r v F G k hbase' hF hG
    _ = sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k :=
      congrArg₂ (· + ·)
        (sphereIntersectionNumber_homotopic e r f F k k HF.homotopic (.refl k)).symm
        (sphereIntersectionNumber_homotopic e r g G k k HG.homotopic (.refl k)).symm

theorem sphereIntersectionNumber_pinch_add_right (v : Sphere 3) (f g k : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v)) :
    sphereIntersectionNumber e r k (pinch v f g hbase) =
      sphereIntersectionNumber e r k f + sphereIntersectionNumber e r k g := by
  rw [sphereIntersectionNumber_comm e r k (pinch v f g hbase),
    sphereIntersectionNumber_pinch_add e r v f g k hbase,
    sphereIntersectionNumber_comm e r f k, sphereIntersectionNumber_comm e r g k]

end NoExoticSixSphere.EuclideanEmbedding
