import ErdosProblems.Erdos6.GenericFiberTermLower

/-!
# Summed lower bound for the coordinate-fiber diagonal
-/

namespace Erdos6.Maynard

open scoped BigOperators

noncomputable section

theorem tupleCoordinateFiberSquareDiagonal_lower
    {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hAbel : ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleFiberScalarSum R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleFiberEndpointIntegral R m r| ≤
          2 * largeFiberAbelEnvelope K C D R m r)
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hlogR : 2 ≤ Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
    (hlog2 : Real.log 2 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 56)
    (hlog3 : Real.log 3 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 56) :
    let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
    let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
    let eta := largeFiberRelativeError K C D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (largeShortMass ^ 2 *
            tupleOuterMaynardWeightedMoment (tupleOffFace H m) alpha
              largeOuterSquaredIntegrand N -
          (2 * eta + eta ^ 2) *
            tupleOuterMaynardWeightedMoment (tupleOffFace H m) alpha
              largeOuterContinuousDensity N) ≤
      tupleCoordinateFiberSquareDiagonal H alpha N m := by
  dsimp only
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let eta := largeFiberRelativeError K C D R
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  let S := BoundedGaps.Maynard.maynardDivisorTupleSupport
    (tupleOffFace H m) R (primorial D)
  have hpoint : ∀ u : tupleOffFace H m → ℕ,
      tupleNormalizedLogPoint (tupleOffFace H m) alpha N u =
        fun h : tupleOffFace H m => Real.log (u h) / Real.log R := by
    intro u
    rfl
  have hsum :
      ∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
          (primorial D) u *
        (largeShortMass ^ 2 *
            largeOuterSquaredIntegrand
              (tupleNormalizedLogPoint (tupleOffFace H m) alpha N u) -
          (2 * eta + eta ^ 2) *
            largeOuterContinuousDensity
              (tupleNormalizedLogPoint (tupleOffFace H m) alpha N u))) ≤
      ∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
            (BoundedGaps.Maynard.maynardYValue H R (primorial D)
              (tupleLargeCandidate H)) m (tupleOffFaceExtension m u) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G
            (tupleOffFaceExtension m u h) : ℝ) := by
    apply Finset.sum_le_sum
    intro u hu
    have ht := tupleCoordinateFiberTerm_lower hK hC hAbel m u hu hD
      hlogR hlog2 hlog3
    simpa [P, D, R, eta, hpoint u] using ht
  have hreindex := sum_coordinateOneSupport_eq_offFace R (primorial D) m
    (fun r =>
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleLargeCandidate H)) m r ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ))
  have hright :
      (∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
            (BoundedGaps.Maynard.maynardYValue H R (primorial D)
              (tupleLargeCandidate H)) m (tupleOffFaceExtension m u) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G
            (tupleOffFaceExtension m u h) : ℝ)) =
        tupleCoordinateFiberSquareDiagonal H alpha N m := by
    unfold tupleCoordinateFiberSquareDiagonal
    simpa [S, D, R, BoundedGaps.Maynard.engelsmaMaynardModulus] using
      hreindex.symm
  rw [hright] at hsum
  have hleft :
      (∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
          (primorial D) u *
        (largeShortMass ^ 2 *
            largeOuterSquaredIntegrand
              (tupleNormalizedLogPoint (tupleOffFace H m) alpha N u) -
          (2 * eta + eta ^ 2) *
            largeOuterContinuousDensity
              (tupleNormalizedLogPoint (tupleOffFace H m) alpha N u)))) =
      P * (largeShortMass ^ 2 *
          tupleOuterMaynardWeightedMoment (tupleOffFace H m) alpha
            largeOuterSquaredIntegrand N -
        (2 * eta + eta ^ 2) *
          tupleOuterMaynardWeightedMoment (tupleOffFace H m) alpha
            largeOuterContinuousDensity N) := by
    unfold tupleOuterMaynardWeightedMoment
    dsimp [S, D, R]
    simp only [BoundedGaps.Maynard.engelsmaMaynardModulus]
    simp only [mul_sub, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hleft] at hsum
  simpa [P, D, R, eta] using hsum

end

end Erdos6.Maynard
