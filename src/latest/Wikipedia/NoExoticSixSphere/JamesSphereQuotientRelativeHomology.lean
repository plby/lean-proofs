import Wikipedia.NoExoticSixSphere.JamesSphereFullStageCofibration
import Wikipedia.NoExoticSixSphere.CollapsedSubspaceRelativeHomology
import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageQuotient

/-!
# The original full James quotient is an isomorphism on relative homology

Homotopy extension is now proved for the actual first-stage inclusion
in the full word space. The genuine quotient theorem therefore applies
to the original map `(J(S^n),S^n) -> (J(S^n)/S^n,*)` in every homology
degree. This is integral homology excision, not homotopy excision.
-/

noncomputable section

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

def firstStageUnit (n : ℕ) : James.stage (spherePole n) 1 := ⟨1, Nat.zero_le 1⟩

theorem quotientMap_mapsTo_point (n : ℕ) :
    Set.MapsTo (quotientMap n) (James.stage (spherePole n) 1) {basepoint n} :=
  fun w hw ↦ quotientMap_firstStage n w hw

theorem quotient_relative_homology_bijective (n d : ℕ) : Function.Bijective
    (RelativeSingularHomology.map (quotientMap n) (quotientMap_mapsTo_point n) d) :=
  CollapsedSubspace.relativeHomology_bijective (James.stage (spherePole n) 1) (firstStageUnit n)
    (FullFirstStageCofibration.hasHomotopyExtension n) d

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
