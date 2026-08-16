import ErdosProblems.Erdos6.GenericFiberDiagonal

/-!
# Pointwise lower bound for the coordinate-fiber diagonal

This is the finite, tuple-generic inequality which turns the scalar Abel
estimate into the two continuous off-face moments used below.
-/

namespace Erdos6.Maynard

open Set
open scoped BigOperators

noncomputable section

theorem tupleOffFace_logProduct_eq_coordinateSum
    {H : Finset ℕ} {R W : ℕ} (m : H)
    (u : tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R W) (hR : 1 < R) :
    Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m
        (tupleOffFaceExtension m u)) / Real.log R =
      largeCoordinateSum
        (fun h : tupleOffFace H m => Real.log (u h) / Real.log R) := by
  have hpos : ∀ h : tupleOffFace H m, 0 < u h := by
    intro h
    exact zero_lt_one.trans_le
      ((BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp
        (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu).mem_maynardDivisorTupleBox) h).1
  rw [maynardS2OffCoordinateProduct_extension]
  have hsum :=
    BoundedGaps.Maynard.sum_normalizedDivisorLogTuple_eq_log_product_div
      hR hpos
  simpa [BoundedGaps.Maynard.normalizedDivisorLogTuple,
    largeCoordinateSum] using hsum.symm

theorem tupleCoordinateFiberTerm_lower
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
    {H : Finset ℕ} {D R : ℕ} (m : H)
    (u : tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R (primorial D))
    (hD : 2 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hlog2 : Real.log 2 / Real.log R ≤ (1 : ℝ) / 56)
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 56) :
    let r := tupleOffFaceExtension m u
    let point := fun h : tupleOffFace H m => Real.log (u h) / Real.log R
    let eta := largeFiberRelativeError K C D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
          (primorial D) u *
        (largeShortMass ^ 2 * largeOuterSquaredIntegrand point -
          (2 * eta + eta ^ 2) * largeOuterContinuousDensity point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleLargeCandidate H)) m r ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) := by
  dsimp only
  let r := tupleOffFaceExtension m u
  let point := fun h : tupleOffFace H m => Real.log (u h) / Real.log R
  let eta := largeFiberRelativeError K C D R
  let O := tupleCoordinateOuterProfile R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let c := largeOuterCutoff
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
      Real.log R)
  let g := ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r :=
    (isMaynardDivisorTuple_extension_iff R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := tupleOffFaceExtension_at m u
  have hg : 0 < g := by
    dsimp [g]
    exact BoundedGaps.Maynard.maynardS2G_product_pos_of_supported hD hr
  have hscale := tupleFiberArithmeticScale_eq_outer m u hu hR
  have hcut : c = largeOuterCutoff (largeCoordinateSum point) := by
    dsimp [c, point, r]
    rw [tupleOffFace_logProduct_eq_coordinateSum m u hu hR]
  have hdensity : O ^ 2 = largeOuterContinuousDensity point := by
    dsimp [O, point, r]
    exact tupleOffFaceExtension_outerProfile_sq m u hu hR
  by_cases hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  · have hraw := tupleCoordinateFiberSum_sq_lower hK hC hAbel m hr hrm
      (by omega) hlogR hQ hlog3
    have hdiv := (div_le_div_iff_of_pos_right hg).mpr hraw
    change (((O * S * L) * (c * largeShortMass)) ^ 2 -
      (O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g ≤ _ at hdiv
    rw [sub_div] at hdiv
    have houter :
        (O * S * L) ^ 2 / g =
          BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
            (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
              (primorial D) u * largeOuterContinuousDensity point) := by
      simpa [O, S, L, g, r, point] using hscale
    rw [show ((O * S * L) * (c * largeShortMass)) ^ 2 / g =
        ((O * S * L) ^ 2 / g) * (c ^ 2 * largeShortMass ^ 2) by
          ring,
      show ((O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g =
        ((O * S * L) ^ 2 / g) * (2 * eta + eta ^ 2) by ring,
      houter] at hdiv
    rw [hcut] at hdiv
    change BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
          (primorial D) u *
        (largeShortMass ^ 2 * largeOuterSquaredIntegrand point -
          (2 * eta + eta ^ 2) * largeOuterContinuousDensity point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleLargeCandidate H)) m r ^ 2 / g
    calc
      _ = BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
                (primorial D) u * largeOuterContinuousDensity point) *
              (largeOuterCutoff (largeCoordinateSum point) ^ 2 *
                largeShortMass ^ 2) -
            BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
                (primorial D) u * largeOuterContinuousDensity point) *
              (2 * eta + eta ^ 2) := by
          unfold largeOuterSquaredIntegrand
          ring
      _ ≤ _ := hdiv
  · have hc : c = 0 :=
      largeOuterCutoff_eq_zero_of_bad_endpoint m hr hR hQ hlog2
    have hsq0 : 0 ≤
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleLargeCandidate H)) m r ^ 2 / g :=
      div_nonneg (sq_nonneg _) hg.le
    have hweight : 0 ≤ BoundedGaps.Maynard.outerTupleWeight
        (tupleOffFace H m) (primorial D) u :=
      outerTupleWeight_nonneg _ _ _
    have heta : 0 ≤ eta :=
      largeFiberRelativeError_nonneg hK hC (by omega) hlogR
    have herr0 : 0 ≤ 2 * eta + eta ^ 2 := by
      nlinarith [sq_nonneg eta]
    have hd0 : 0 ≤ largeOuterContinuousDensity point := by
      rw [← hdensity]
      exact sq_nonneg _
    have hs0 : 0 ≤ BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 :=
      sq_nonneg _
    have hL0 : 0 ≤ L ^ 2 := sq_nonneg _
    rw [hcut] at hc
    unfold largeOuterSquaredIntegrand
    rw [hc]
    norm_num
    have hnonpos := (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hs0 hL0) hweight)
      (neg_nonpos.mpr (mul_nonneg herr0 hd0))).trans hsq0
    simpa [L, g, eta, point, r, mul_assoc, mul_left_comm, mul_comm] using hnonpos

end

end Erdos6.Maynard
