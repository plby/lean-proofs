import Wikipedia.HopfProblem.ConstantSheafFirstCohomology
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardCusp
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionConstants

/-!
# Actual degree-one vanishing of the constant normalization terms

The genuine constant sheaf on the actual toric component has vanishing
H¹ by the proved simply-connected covering-space argument. The actual
double curves have the constructed sphere homeomorphisms and affine
atlases, so the same native Ext argument applies to them. Genuine finite
closed pushforward and finite biproducts give the required resolution
term vanishings. No H² vanishing of the constant component is asserted.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafResolution CuspQuotient ToricCharts ToricSpace NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- Unconditional genuine H¹ vanishing of the actual constant normalization term. -/
theorem normalizationConstant_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationConstantSheaf C ε hε) 1) := by
  let e := normalizationConstantCohomologyEquiv C ε hε hε1 hC hR 1
  have h := ConstantSheafFirstCohomology.zeroRay_h1_subsingleton
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

theorem sourceCurve_simplyConnected (k : Fin 3) :
    SimplyConnectedSpace (sourceDoubleCurve C ε hε k) := by
  let : SimplyConnectedSpace RiemannSphere :=
    ConstantSheafFirstCohomology.sphere_simplyConnectedSpace
  let e := (curveSphereHomeomorph C ε hε hε1 hC hR (sourceEdgeIndex k)).symm.toHomotopyEquiv
  exact e.simplyConnectedSpace

theorem sourceCurve_locallyPathConnected (k : Fin 3) :
    LocallyPathConnectedSpace (sourceDoubleCurve C ε hε k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact ChartedSpace.locallyPathConnectedSpace ℂ (sourceDoubleCurve C ε hε k)

/-- The literal source-ordered constant curve sheaf has vanishing native H¹. -/
theorem sourceCurveConstant_h1_subsingleton (k : Fin 3) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of (sourceDoubleCurve C ε hε k))) 1) := by
  let := sourceCurve_simplyConnected C ε hε hε1 hC hR k
  let := sourceCurve_locallyPathConnected C ε hε hε1 hC hR k
  exact ConstantSheafFirstCohomology.complex_h1_subsingleton
    (X := TopCat.of (sourceDoubleCurve C ε hε k))

/-- Genuine finite closed pushforward gives H¹ vanishing of each actual curve term. -/
theorem curveConstant_h1_subsingleton (k : Fin 3) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (curveConstantSheaf C ε hε k) 1) := by
  let e := curveConstantCohomologyEquiv C ε hε hε1 hC hR k 1
  have h := sourceCurveConstant_h1_subsingleton C ε hε hε1 hC hR k
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

/-- The actual three-curve constant boundary term has vanishing genuine H¹. -/
theorem boundaryConstant_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (boundaryConstantSheaf C ε hε) 1) := by
  let K : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) ⥤ AddCommGrpCat :=
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of (CentralSpace C ε))) 1
  have : K.Additive := by
    change (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of (CentralSpace C ε))) 1).Additive
    infer_instance
  let A : Fin 3 → TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
    curveConstantSheaf C ε hε
  let ei := K.mapBiproduct A ≪≫ AddCommGrpCat.biproductIsoPi (K.obj ∘ A)
  let e := ei.addCommGroupIsoToAddEquiv
  refine ⟨fun a b => e.injective ?_⟩
  funext k
  exact (curveConstant_h1_subsingleton C ε hε hε1 hC hR k).elim ((e a) k) ((e b) k)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
