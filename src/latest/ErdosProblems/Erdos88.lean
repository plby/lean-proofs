import ErdosProblems.Erdos88.AKSFamily
import ErdosProblems.Erdos88.AKSGraph
import ErdosProblems.Erdos88.AKSPrescribed
import ErdosProblems.Erdos88.Assembly
import ErdosProblems.Erdos88.BinomialLower
import ErdosProblems.Erdos88.BooleanSlices
import ErdosProblems.Erdos88.BoundedWindow
import ErdosProblems.Erdos88.BoundedWindowFin
import ErdosProblems.Erdos88.Concentration
import ErdosProblems.Erdos88.Esseen
import ErdosProblems.Erdos88.FiniteES
import ErdosProblems.Erdos88.Foundations
import ErdosProblems.Erdos88.Fourier
import ErdosProblems.Erdos88.GaussianQuadratic
import ErdosProblems.Erdos88.GaussianUnivariateNonuniform
import ErdosProblems.Erdos88.GaussianHypercontractiveTail
import ErdosProblems.Erdos88.GaussianNonuniformSmallCoordinates
import ErdosProblems.Erdos88.GaussianThreeSpectral
import ErdosProblems.Erdos88.GaussianUniformRankTwo
import ErdosProblems.Erdos88.GaussianVariancePartition
import ErdosProblems.Erdos88.GaussianPartialUniform
import ErdosProblems.Erdos88.GaussianCommonEnvelope
import ErdosProblems.Erdos88.GaussianDensityHolder
import ErdosProblems.Erdos88.GaussianNonuniform
import ErdosProblems.Erdos88.GaussianSpectralTail
import ErdosProblems.Erdos88.GaussianMoments
import ErdosProblems.Erdos88.GaussianLocalCLT
import ErdosProblems.Erdos88.GaussianDensity
import ErdosProblems.Erdos88.GaussianDiagonalization
import ErdosProblems.Erdos88.GaussianFourierComparison
import ErdosProblems.Erdos88.GaussianRobustRank
import ErdosProblems.Erdos88.GraphQuadratic
import ErdosProblems.Erdos88.Invariance
import ErdosProblems.Erdos88.LocalToPrescribed
import ErdosProblems.Erdos88.PermutationConcentration
import ErdosProblems.Erdos88.Probability
import ErdosProblems.Erdos88.ProductPermutationConcentration
import ErdosProblems.Erdos88.ProductSliceOuter
import ErdosProblems.Erdos88.ProductSliceFourierAssembly
import ErdosProblems.Erdos88.QuadraticCancellation
import ErdosProblems.Erdos88.QuadraticHypergeometric
import ErdosProblems.Erdos88.QuadraticLemma81
import ErdosProblems.Erdos88.BoundedWindowAnalytic
import ErdosProblems.Erdos88.GaussianWindow
import ErdosProblems.Erdos88.UnstructuredWindow
import ErdosProblems.Erdos88.BoundedWindowDichotomy
import ErdosProblems.Erdos88.QuadraticLemma82
import ErdosProblems.Erdos88.QuadraticNumerics
import ErdosProblems.Erdos88.QuadraticRichness
import ErdosProblems.Erdos88.RLCD
import ErdosProblems.Erdos88.Richness
import ErdosProblems.Erdos88.RobustRank
import ErdosProblems.Erdos88.RobustRank101
import ErdosProblems.Erdos88.GraphQuadraticMoments
import ErdosProblems.Erdos88.GraphQuadraticScale
import ErdosProblems.Erdos88.GraphLinearCancellation
import ErdosProblems.Erdos88.GraphLinearNormalization
import ErdosProblems.Erdos88.LinearLCDCancellation
import ErdosProblems.Erdos88.SignedSliceConcentration
import ErdosProblems.Erdos88.SliceCoupling
import ErdosProblems.Erdos88.SliceCouplingAsymptotic
import ErdosProblems.Erdos88.SliceFamilyConcentration
import ErdosProblems.Erdos88.SliceGaussianComparison
import ErdosProblems.Erdos88.SliceMixture
import ErdosProblems.Erdos88.Structured
import ErdosProblems.Erdos88.StructuredBucket
import ErdosProblems.Erdos88.StructuredGraphBucket
import ErdosProblems.Erdos88.StructuredClaimUpper
import ErdosProblems.Erdos88.StructuredClaim121Nonuniform
import ErdosProblems.Erdos88.StructuredClaim121Lower
import ErdosProblems.Erdos88.RademacherLinearLower
import ErdosProblems.Erdos88.StructuredCountVectorLower
import ErdosProblems.Erdos88.StructuredConditioning
import ErdosProblems.Erdos88.StructuredMixture
import ErdosProblems.Erdos88.StructuredSlice
import ErdosProblems.Erdos88.StructuredCoefficients
import ErdosProblems.Erdos88.StructuredTypical
import ErdosProblems.Erdos88.StructuredAveraging
import ErdosProblems.Erdos88.StructuredClaim122
import ErdosProblems.Erdos88.StructuredClaim122Eventual
import ErdosProblems.Erdos88.StructuredClaim122Conditioned
import ErdosProblems.Erdos88.StructuredClaims
import ErdosProblems.Erdos88.Switching
import ErdosProblems.Erdos88.SwitchingDegeneracy
import ErdosProblems.Erdos88.SwitchingHalasz
import ErdosProblems.Erdos88.SwitchingLemma136
import ErdosProblems.Erdos88.SwitchingLocal
import ErdosProblems.Erdos88.SwitchingLower
import ErdosProblems.Erdos88.SwitchingMomentLower
import ErdosProblems.Erdos88.SwitchingMomentUpper
import ErdosProblems.Erdos88.SwitchingMomentComparison
import ErdosProblems.Erdos88.SwitchingRichness
import ErdosProblems.Erdos88.Unstructured

/-!
# Erdős Problem 88

Umbrella module for the formalization of the Kwan--Sah--Sauermann--Sawhney
approach to prescribed induced-edge counts.
-/

open Classical SimpleGraph

namespace Erdos88

/-- Erdős Problem 88: every sufficiently Ramsey-homogeneous-free graph
contains induced subgraphs with every prescribed edge count up to a fixed
positive quadratic proportion of its order. -/
theorem erdos_88 :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m :=
  Switching.erdos_88_of_boundedWindowFin
    BoundedWindowAnalytic.ksssBoundedWindowFin_proof

end Erdos88

#print axioms Erdos88.erdos_88
