import Wikipedia.NoExoticSixSphere.QuaternionicHopfRawProductClass
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Finite linear coordinates underlying the original compactified maps

The ambient change is an actual isometry, retaining the original
stabilization and pairing orders. The target change is a continuous linear
equivalence and retains both radius factors and both normal reflections.
-/

noncomputable section

namespace NoExoticSixSphere.SuspensionProductComparison

open Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

def productFiniteLinearCoordinates (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin n)) ℝ).trans (coordinates n)

def productPairLinearCoordinates (n : ℕ) :
    ((EuclideanSpace ℝ (Fin n) × ℝ) × (EuclideanSpace ℝ (Fin n) × ℝ)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin ((n + 1) + (n + 1))) :=
  ((productFiniteLinearCoordinates n).prodCongr (productFiniteLinearCoordinates n)).trans
    EuclideanSpace.finAddEquivProd.symm

theorem productPairSphereHomeomorph_linearCoordinates (n : ℕ)
    (z : OnePoint ((EuclideanSpace ℝ (Fin n) × ℝ) × (EuclideanSpace ℝ (Fin n) × ℝ))) :
    productPairSphereHomeomorph n z = euclideanOnePointSphere ((n + 1) + (n + 1))
      ((productPairLinearCoordinates n).toHomeomorph.onePointCongr z) := by
  induction z using OnePoint.rec <;> rfl

end NoExoticSixSphere.SuspensionProductComparison

namespace NoExoticSixSphere.StereographicEquator

open Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

def stabilizedEuclideanCoordinates (n : ℕ) : V (n + 1) ≃ₗᵢ[ℝ] V (n + 1) :=
  (hilbertStabilizedEquiv n).symm.trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ (V n) ℝ).trans (headIsometry n))

def stabilizedPairEuclideanCoordinates (n : ℕ) :
    WithLp 2 (V (n + 1) × V (n + 1)) ≃ₗᵢ[ℝ] V ((n + 1) + (n + 1)) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (stabilizedEuclideanCoordinates n) (stabilizedEuclideanCoordinates n)).trans
      (EuclideanTailCoordinates.finAdd (n + 1) (n + 1)).symm

theorem stabilizedPairSphereHomeomorph_euclideanCoordinates (n : ℕ)
    (z : OnePoint (WithLp 2 (V (n + 1) × V (n + 1)))) :
    stabilizedPairSphereHomeomorph n z = euclideanOnePointSphere ((n + 1) + (n + 1))
      ((stabilizedPairEuclideanCoordinates n).toHomeomorph.onePointCongr z) := by
  induction z using OnePoint.rec <;> rfl

end NoExoticSixSphere.StereographicEquator

namespace NoExoticSixSphere.QuaternionicHopf

def southPairAmbientEuclideanCoordinates : SouthPairAmbientModel ≃ₗᵢ[ℝ] V 16 :=
  StereographicEquator.stabilizedPairEuclideanCoordinates 7

def southPairNormalEuclideanCoordinates : SouthPairNormalModel ≃L[ℝ] V 10 :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ SouthNormalModel SouthNormalModel).trans
    (southChosenNormalCoordinates.symm.prodCongr southChosenNormalCoordinates.symm)).trans
      (SuspensionProductComparison.productPairLinearCoordinates 4)

theorem southPairedSourceSphereHomeomorph_euclidean (z : OnePoint SouthPairAmbientModel) :
    StereographicEquator.stabilizedPairSphereHomeomorph 7 z = euclideanOnePointSphere 16
      (southPairAmbientEuclideanCoordinates.toHomeomorph.onePointCongr z) :=
  StereographicEquator.stabilizedPairSphereHomeomorph_euclideanCoordinates 7 z

theorem southPairedTargetSphereHomeomorph_euclidean (z : OnePoint SouthPairNormalModel) :
    southPairedTargetSphereHomeomorph z = euclideanOnePointSphere 10
      (southPairNormalEuclideanCoordinates.toHomeomorph.onePointCongr z) := by
  induction z using OnePoint.rec <;> rfl

end NoExoticSixSphere.QuaternionicHopf
