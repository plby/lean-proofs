import ErdosProblems.Erdos88.GaussianDensityHolder
import ErdosProblems.Erdos88.StructuredClaim121Nonuniform

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Erdos88.GaussianQuadratic

open BooleanSlices

/-- The normalized upper half of KSSS Theorem 5.2.  A common
three-spectral Fourier envelope gives a quarter-Hölder density; combining
that regularity with the degree-two Gaussian tail yields the required
nonuniform exponential small-ball bound. -/
theorem ksssGaussianNonuniformUpper : KSSSGaussianNonuniformUpper := by
  intro rho hrho
  obtain ⟨eta, heta, hetaOne, hbound⟩ :=
    exists_eta_gaussianQuadraticCenteredLaw_nonuniform_of_relative_robustRankThree
      rho hrho
  refine ⟨eta, heta, hetaOne, ?_⟩
  intro n f F hF sigma hsigma hsigmaSq _hFrob hrob eps heps hepsOne x
  exact hbound f hF hsigma hsigmaSq hrob heps hepsOne x

/-- Unconditional threshold form of Claim 12.1: every fixed window above
the Fourier cutoff is admissible. -/
theorem exists_eventual_productSlice_claim121_nonuniform_upper_threshold_unconditional
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ B : ℝ, B0 ≤ B →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
          (f : Fin n → ℝ)
          (hbucket : Erdos88.RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → IsNearBalanced delta P ell →
          HasKSSSBalancedCoefficients delta P f
            (bucketCenteredAdjacency P.bucket hbucket.choose G) →
          RamseyFree C G →
          ∃ hleft : Nonempty (ProductSlicePoint P ell),
            letI := hleft
            let F := bucketCenteredAdjacency P.bucket hbucket.choose G
            let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
            0 < sigma ∧ ∀ x : ℝ,
              Erdos88.Esseen.smallBall
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                Erdos88.Esseen.relativeEsseenConstant *
                  (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                    (B / (eta * sigma)) *
                      Real.exp (-eta * |x| / (2 * sigma)) +
                    B * scale n (-6 / 5 : ℝ)) := by
  exact exists_eventual_productSlice_claim121_nonuniform_upper_threshold
    ksssGaussianNonuniformUpper C delta hC hdelta hdeltaSmall

/-- Unconditional nonuniform product-slice upper bound in Claim 12.1. -/
theorem exists_eventual_productSlice_claim121_nonuniform_upper_unconditional
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
          (f : Fin n → ℝ)
          (hbucket : Erdos88.RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → IsNearBalanced delta P ell →
          HasKSSSBalancedCoefficients delta P f
            (bucketCenteredAdjacency P.bucket hbucket.choose G) →
          RamseyFree C G →
          ∃ hleft : Nonempty (ProductSlicePoint P ell),
            letI := hleft
            let F := bucketCenteredAdjacency P.bucket hbucket.choose G
            let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
            0 < sigma ∧ ∀ x : ℝ,
              Erdos88.Esseen.smallBall
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                Erdos88.Esseen.relativeEsseenConstant *
                  (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                    (B / (eta * sigma)) *
                      Real.exp (-eta * |x| / (2 * sigma)) +
                    B * scale n (-6 / 5 : ℝ)) := by
  exact exists_eventual_productSlice_claim121_nonuniform_upper
    ksssGaussianNonuniformUpper C delta hC hdelta hdeltaSmall

end Erdos88.GaussianQuadratic
