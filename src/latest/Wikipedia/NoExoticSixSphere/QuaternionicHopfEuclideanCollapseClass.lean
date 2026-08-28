import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEuclideanTube

/-!
# The actual Euclidean framed tube represents the original sixth-stem class

Both compactifications here are the standard Euclidean compactifications.
The map is the collapse of the explicitly retained tube. Its equality with
the endpoint sphere map follows from the proved finite coordinate formulas.
No Arf value, nontriviality, or generation is asserted.
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition

def southPairEuclideanCollapse : C(OnePoint (V 16), OnePoint (V 10)) :=
  ⟨OpenFiberCollapse.collapseOnePoint southPairEuclideanTube,
    OpenFiberCollapse.continuous_collapseOnePoint southPairEuclideanTube
      southPairEuclideanTube_isOpenEmbedding⟩

def southPairEuclideanCollapseSphereMap : C(Sphere 16, Sphere 10) :=
  (euclideanOnePointSphere 10 : C(_, _)).comp
    (southPairEuclideanCollapse.comp ((euclideanOnePointSphere 16).symm : C(_, _)))

theorem southPairEuclideanCollapseSphereMap_apply (z : OnePoint (V 16)) :
    southPairEuclideanCollapseSphereMap (euclideanOnePointSphere 16 z) =
      euclideanOnePointSphere 10 (OpenFiberCollapse.collapseOnePoint southPairEuclideanTube z) := by
  change euclideanOnePointSphere 10 (southPairEuclideanCollapse
    ((euclideanOnePointSphere 16).symm (euclideanOnePointSphere 16 z))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem southPairEuclideanCollapseSphereMap_raw :
    southPairEuclideanCollapseSphereMap = southPairedRawSphereMap := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (StereographicEquator.stabilizedPairSphereHomeomorph 7).surjective y
  have he : southPairEuclideanCollapseSphereMap
      (StereographicEquator.stabilizedPairSphereHomeomorph 7 z) =
        southPairedTargetSphereHomeomorph
          (OpenFiberCollapse.collapseOnePoint (southPairedFrameTube 1) z) := by
    rw [southPairedSourceSphereHomeomorph_euclidean,
      southPairEuclideanCollapseSphereMap_apply, southPairEuclideanTube_collapse,
      southPairedTargetSphereHomeomorph_euclidean]
  exact he.trans (southPairedRawSphereMap_formula z).symm

def southPairEuclideanCollapseBasedMap : Based 16 10 := by
  refine ⟨southPairEuclideanCollapseSphereMap, ?_⟩
  rw [southPairEuclideanCollapseSphereMap_raw]
  exact southPairedRawSphereMap_pole

theorem southPairEuclideanCollapseBasedMap_raw :
    southPairEuclideanCollapseBasedMap = southPairedRawBasedMap :=
  Subtype.ext southPairEuclideanCollapseSphereMap_raw

theorem southPairEuclideanCollapse_nativeClass :
    sphereClass southPairEuclideanCollapseBasedMap = SixthStemSmashSquare.nativeClass := by
  rw [southPairEuclideanCollapseBasedMap_raw]
  exact southPairedRawBasedMap_nativeClass

end NoExoticSixSphere.QuaternionicHopf
