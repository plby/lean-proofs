import Wikipedia.NoExoticSixSphere.CollapsedSubspaceSeparation
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientBottomSphere

/-!
# Hausdorff separation for the genuine full James quotient

Only the collapsed first stage is compact. The full James space is not
assumed compact. The finite second-stage quotient and its bottom sphere
are consequently closed embedded subspaces of the original quotient.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

instance (n : ℕ) : T2Space (Space n) :=
  CollapsedSubspace.t2Space (James.stage (spherePole n) 1)
    (James.isCompact_stage (spherePole n) 1)

theorem isProperMap_quotientMap (n : ℕ) : IsProperMap (quotientMap n) :=
  CollapsedSubspace.isProperMap (James.stage (spherePole n) 1)
    (James.isCompact_stage (spherePole n) 1)

theorem isClosedEmbedding_stageMap (n : ℕ) : IsClosedEmbedding (stageMap n) :=
  (stageMap n).continuous.isClosedEmbedding (stageMap_injective n)

theorem isClosedEmbedding_bottomSphere (n : ℕ) : IsClosedEmbedding (bottomSphere n) :=
  (bottomSphere n).continuous.isClosedEmbedding (bottomSphere_injective n)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
