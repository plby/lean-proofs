import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductCollapse
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductFrameHomotopy
import Wikipedia.NoExoticSixSphere.StereographicStabilizedCoordinates
import Wikipedia.NoExoticSixSphere.CollapseAmbientEquiv
import Wikipedia.NoExoticSixSphere.CollapseBaseEquiv

/-!
# The original stabilized Hopf tube in the computed ambient coordinates

The certified tube itself is retained. Only its base parametrization and
the specified ambient coordinates are changed. Its center is twice the
original quaternion-axis inclusion, and its exact normal expression uses
the endpoint of the checked frame homotopy, with the fixed signs retained.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance : IsManifold (𝓡 3) ∞ {x : Sphere 7 // sphereMap x = south} :=
  regularFiber_isManifold sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance : CompactSpace {x : Sphere 7 // sphereMap x = south} :=
  RegularSphereFiber.fiber_compact sphereMap south

def southStabilizedBaseTube (p : Sphere 3 × (V 4 × ℝ)) : V 7 × ℝ :=
  (southChartTube.tube (southFiberDiffeomorph p.1, p.2.1), p.2.2)

theorem southStabilizedBaseTube_isOpenEmbedding :
    Topology.IsOpenEmbedding southStabilizedBaseTube :=
  (OpenFiberCollapse.productTube_isOpenEmbedding southChartTube.tube
    southChartTube.isOpenEmbedding).comp
      (southFiberDiffeomorph.toHomeomorph.prodCongr
        (Homeomorph.refl (V 4 × ℝ))).isOpenEmbedding

def southStabilizedTube (p : Sphere 3 × (V 4 × ℝ)) : V 8 :=
  StereographicEquator.stabilizedEquiv 7 (southStabilizedBaseTube p)

theorem southStabilizedTube_isOpenEmbedding : Topology.IsOpenEmbedding southStabilizedTube :=
  (StereographicEquator.stabilizedEquiv 7).toHomeomorph.isOpenEmbedding.comp
    southStabilizedBaseTube_isOpenEmbedding

theorem southStabilizedTube_zero (q : Sphere 3) :
    southStabilizedTube (q, 0) = (2 : ℝ) • southFiberAmbient q := by
  change StereographicEquator.stabilizedEquiv 7
    (southChartTube.tube (southFiberDiffeomorph q, 0), 0) = _
  rw [StereographicEquator.stabilizedEquiv_apply, southChartTube.tube_zero,
    southChartEmbedding_parametrized, StereographicEquator.lift_smul,
    lift_southChartUnit, zero_smul, add_zero]
  rfl

theorem southStabilizedTube_formula (q : Sphere 3) (v : V 4) (u : ℝ) :
    southStabilizedTube (q, (v, u)) = (2 : ℝ) • southFiberAmbient q +
      southRadialFrame 1 q (WithLp.toLp 2 ((2 : ℝ) * (-u),
        (2 : ℝ) • targetTailChartEquiv.symm
          (OpenPartialHomeomorph.univBall (0 : V 4) southChartTube.radius v))) := by
  let c := OpenPartialHomeomorph.univBall (0 : V 4) southChartTube.radius v
  have hf := southRadialFrame_one q c u
  have ht : southChartTube.tube (southFiberDiffeomorph q, v) =
      southChartEmbedding.toFun (southFiberDiffeomorph q) +
        southChartFrame.ambient (southFiberDiffeomorph q) c := southChartTube.formula _
  have hc : StereographicEquator.liftL 7
      (southChartEmbedding.toFun (southFiberDiffeomorph q)) =
        (2 : ℝ) • southFiberAmbient q := by
    have hs : StereographicEquator.liftL 7 ((2 : ℝ) • southChartUnit q) =
        (2 : ℝ) • southFiberAmbient q := by
      rw [map_smul, StereographicEquator.liftL_apply, lift_southChartUnit]
      rfl
    exact (congrArg (StereographicEquator.liftL 7)
      (southChartEmbedding_parametrized q)).trans hs
  have ha := (StereographicEquator.liftL 7).map_add
    (southChartEmbedding.toFun (southFiberDiffeomorph q))
    (southChartFrame.ambient (southFiberDiffeomorph q) c)
  have hfirst := congrArg (fun y : V 7 ↦
    StereographicEquator.liftL 7 y + u • (spherePole 7).val) ht
  have hsecond := congrArg (fun y : V 8 ↦ y + u • (spherePole 7).val) ha
  exact hfirst.trans (hsecond.trans ((add_assoc _ _ _).trans
    (congrArg₂ (fun x y : V 8 ↦ x + y) hc hf.symm)))

theorem southStabilizedTube_collapse (z : OnePoint (V 7 × ℝ)) :
    OpenFiberCollapse.collapseOnePoint southStabilizedTube
        ((StereographicEquator.stabilizedEquiv 7).toHomeomorph.onePointCongr z) =
      OpenFiberCollapse.collapseOnePoint
        (OpenFiberCollapse.productTube (T := ℝ) southChartTube.tube) z := by
  have ha := OpenFiberCollapse.collapseOnePoint_ambientEquiv southStabilizedBaseTube
    (StereographicEquator.stabilizedEquiv 7).toHomeomorph
    southStabilizedBaseTube_isOpenEmbedding.injective z
  have hb := OpenFiberCollapse.collapseOnePoint_baseEquiv
    (OpenFiberCollapse.productTube (T := ℝ) southChartTube.tube)
    southFiberDiffeomorph.toEquiv
    (OpenFiberCollapse.productTube_injective _ southChartTube.isOpenEmbedding.injective) z
  exact ha.trans hb

def southStabilizedPairTube
    (p : (Sphere 3 × Sphere 3) × ((V 4 × ℝ) × (V 4 × ℝ))) : SouthPairAmbientModel :=
  WithLp.toLp 2 (southStabilizedTube (p.1.1, p.2.1),
    southStabilizedTube (p.1.2, p.2.2))

theorem southStabilizedPairTube_isOpenEmbedding :
    Topology.IsOpenEmbedding southStabilizedPairTube :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toHomeomorph.isOpenEmbedding.comp
    (OpenFiberCollapse.pairedTube_isOpenEmbedding southStabilizedTube southStabilizedTube
      southStabilizedTube_isOpenEmbedding southStabilizedTube_isOpenEmbedding)

theorem southStabilizedPairTube_zero (p : Sphere 3 × Sphere 3) :
    southStabilizedPairTube (p, 0) = (2 : ℝ) • southPairAmbient p := by
  change WithLp.toLp 2 (southStabilizedTube (p.1, 0), southStabilizedTube (p.2, 0)) = _
  rw [southStabilizedTube_zero, southStabilizedTube_zero]
  rfl

theorem southStabilizedPairTube_collapse
    (z : OnePoint ((V 7 × ℝ) × (V 7 × ℝ))) :
    OpenFiberCollapse.collapseOnePoint southStabilizedPairTube
        ((StereographicEquator.stabilizedPairCoordinates 7).onePointCongr z) =
      OpenFiberCollapse.collapseOnePoint southChartTube.pairedProductTube z := by
  let B := southFiberDiffeomorph.toHomeomorph.prodCongr southFiberDiffeomorph.toHomeomorph
  let τ : (Sphere 3 × Sphere 3) × ((V 4 × ℝ) × (V 4 × ℝ)) →
      (V 7 × ℝ) × (V 7 × ℝ) := fun p ↦ southChartTube.pairedProductTube (B p.1, p.2)
  have hi : Function.Injective τ := southChartTube.pairedProductTube_isOpenEmbedding.injective.comp
    (B.prodCongr (Homeomorph.refl ((V 4 × ℝ) × (V 4 × ℝ)))).injective
  have ha := OpenFiberCollapse.collapseOnePoint_ambientEquiv τ
    (StereographicEquator.stabilizedPairCoordinates 7) hi z
  have hb := OpenFiberCollapse.collapseOnePoint_baseEquiv southChartTube.pairedProductTube
    B.toEquiv southChartTube.pairedProductTube_isOpenEmbedding.injective z
  exact ha.trans hb

theorem southStabilizedPairTube_originalMap (z : OnePoint SouthPairAmbientModel) :
    southPairedProductBasedMap.val
        (StereographicEquator.stabilizedPairSphereHomeomorph 7 z) =
      SuspensionProductComparison.productPairSphereHomeomorph 4
        (OpenFiberCollapse.collapseOnePoint southStabilizedPairTube z) := by
  obtain ⟨w, rfl⟩ := (StereographicEquator.stabilizedPairCoordinates 7).onePointCongr.surjective z
  rw [StereographicEquator.stabilizedPairSphereHomeomorph_coordinates,
    southStabilizedPairTube_collapse]
  exact southPairedProductBasedMap_formula w

end NoExoticSixSphere.QuaternionicHopf
