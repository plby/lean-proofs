import ErdosProblems.Erdos6.LargeFiberFactor

/-!
# Pointwise lower bounds for the arithmetic coordinate fiber
-/

namespace Erdos6.Maynard

open MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval

noncomputable section

def tupleFiberScalarSum {H : Finset ℕ} (R W : ℕ) (m : H)
    (r : H → ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport H R W m r,
    ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
      largeFiberProfile (Real.log u / Real.log R)

def tupleFiberEndpointIntegral {H : Finset ℕ} (R : ℕ) (m : H)
    (r : H → ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..
    (Real.log (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) /
        Real.log R), largeFiberProfile x

theorem tupleCoordinateOuterProfile_nonneg_le_one
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R) :
    0 ≤ tupleCoordinateOuterProfile R m r ∧
      tupleCoordinateOuterProfile R m r ≤ 1 := by
  have hbox := hr.mem_maynardDivisorTupleBox
  have hcoord : ∀ h : H,
      Real.log (r h) / Real.log R ∈ Set.Icc (0 : ℝ) 1 :=
    fun h => BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR hbox h
  unfold tupleCoordinateOuterProfile
  constructor
  · exact Finset.prod_nonneg fun h hh => largeFiberProfile_nonneg (hcoord h).1
  · calc
      (∏ h ∈ (Finset.univ : Finset H).erase m,
          largeFiberProfile (Real.log (r h) / Real.log R)) ≤
          ∏ _h ∈ (Finset.univ : Finset H).erase m, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro h hh
          exact largeFiberProfile_nonneg (hcoord h).1
        · intro h hh
          exact largeFiberProfile_le_one (hcoord h).1
      _ = 1 := by simp

theorem tupleFiberEndpointIntegral_bounds
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 56) :
    largeOuterCutoff
        (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
          Real.log R) * largeShortMass ≤
      tupleFiberEndpointIntegral R m r ∧
      tupleFiberEndpointIntegral R m r ≤ 1 := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  let q := Real.log Q / Real.log R
  let s := Real.log P / Real.log R
  let c := largeOuterCutoff s
  have hP : 0 < P :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  have hQnat : 1 < Q := by simpa [Q, P] using hQ
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQnat
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hq0 : 0 ≤ q :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQpos)) hlogR.le
  have hendpoint := coordinateFiberEndpoint_ratio_ge_complement_sub
    m hr hR hQ
  have hqLower : 1 - s - Real.log 3 / Real.log R ≤ q := by
    simpa [P, Q, q, s] using hendpoint
  have hc0 : 0 ≤ c := largeOuterCutoff_nonneg s
  have hc1 : c ≤ 1 := largeOuterCutoff_le_one s
  have hcq : c * ((1 : ℝ) / 8) ≤ q :=
    largeOuterCutoff_mul_eighth_le_complement hlog3 hq0 hqLower
  have hlower := cutoff_mul_largeShortMass_le_fiberIntegral hc0 hc1 hcq
  have hQP : Q * P < R := by
    have hle : Q * P ≤ R - 1 := by
      unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
      simpa [Nat.mul_comm] using Nat.mul_div_le (R - 1) P
    omega
  have hQltR : Q < R := by
    have hQleQP : Q ≤ Q * P := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hP
    exact hQleQP.trans_lt hQP
  have hlogQle : Real.log Q ≤ Real.log R :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hQpos))
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hQltR.le)
  have hq1 : q ≤ 1 := (div_le_one hlogR).2 hlogQle
  have hintFormula := integral_largeFiberProfile_interval hq0
  have harg : 0 < 1 + largeFiberSlope * q := by
    nlinarith [largeFiberSlope_pos]
  have hlogBound : Real.log (1 + largeFiberSlope * q) ≤
      largeFiberSlope * q := by
    have := Real.log_le_sub_one_of_pos harg
    linarith
  have hupper : (∫ x : ℝ in (0 : ℝ)..q, largeFiberProfile x) ≤ 1 := by
    rw [hintFormula]
    calc
      Real.log (1 + largeFiberSlope * q) / largeFiberSlope ≤
          (largeFiberSlope * q) / largeFiberSlope :=
        div_le_div_of_nonneg_right hlogBound largeFiberSlope_pos.le
      _ = q := by field_simp [largeFiberSlope_pos.ne']
      _ ≤ 1 := hq1
  simpa [tupleFiberEndpointIntegral, P, Q, q, s, c] using
    And.intro hlower hupper

theorem largeOuterCutoff_eq_zero_of_bad_endpoint
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R)
    (hbad : ¬1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog2 : Real.log 2 / Real.log R ≤ (1 : ℝ) / 56) :
    largeOuterCutoff
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
        Real.log R) = 0 := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  have hP : 0 < P :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  have hbad' : ¬1 < Q := by simpa [Q, P] using hbad
  have hQle : Q ≤ 1 := le_of_not_gt hbad'
  have hRsub : R - 1 < (Q + 1) * P := by
    unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
    exact (Nat.div_lt_iff_lt_mul hP).mp
      (Nat.lt_succ_self ((R - 1) / P))
  have hRle : R ≤ 2 * P := by
    have hmul : (Q + 1) * P ≤ 2 * P :=
      Nat.mul_le_mul_right P (by omega)
    omega
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
  have h2PReal : (0 : ℝ) < 2 * P := by positivity
  have hRReal : (0 : ℝ) < R := by exact_mod_cast Nat.zero_lt_of_lt hR
  have hRleReal : (R : ℝ) ≤ (2 : ℝ) * P := by exact_mod_cast hRle
  have hlogMul : Real.log R ≤ Real.log 2 + Real.log P := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hRReal)
      (Set.mem_Ioi.mpr h2PReal) hRleReal
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast hP.ne')] at hmono
    exact hmono
  have hcomp : 1 - Real.log P / Real.log R ≤
      Real.log 2 / Real.log R := by
    calc
      1 - Real.log P / Real.log R =
          (Real.log R - Real.log P) / Real.log R := by
        field_simp [hlogR.ne']
      _ ≤ Real.log 2 / Real.log R :=
        div_le_div_of_nonneg_right (by linarith) hlogR.le
  apply largeOuterCutoff_eq_zero
  linarith

theorem tupleFiberScalarSum_abel_bound
    {K C : ℝ}
    (hAbel : ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleFiberScalarSum R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleFiberEndpointIntegral R m r| ≤
          2 * largeFiberAbelEnvelope K C D R m r)
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r)
    (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) :
    |tupleFiberScalarSum R (primorial D) m r -
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
        Real.log R * tupleFiberEndpointIntegral R m r| ≤
      2 * largeFiberAbelEnvelope K C D R m r :=
  hAbel m r hr hD hlogR hQ

theorem exists_uniform_tupleFiberScalarSum_abel_bound :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleFiberScalarSum R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleFiberEndpointIntegral R m r| ≤
          2 * largeFiberAbelEnvelope K C D R m r := by
  obtain ⟨K, C, hK, hC, h⟩ := exists_uniform_largeFiberAbel_bound
  refine ⟨K, C, hK, hC, ?_⟩
  intro H D R m r hr hD hlogR hQ
  simpa [tupleFiberScalarSum, tupleFiberEndpointIntegral] using
    h m r hr hD hlogR hQ

def largeFiberRelativeError (K C : ℝ) (D R : ℕ) : ℝ :=
  22 * (K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2) / Real.log R

theorem largeFiberRelativeError_nonneg
    {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    {D R : ℕ} (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R) :
    0 ≤ largeFiberRelativeError K C D R := by
  unfold largeFiberRelativeError
  have hlogD : 0 ≤ Real.log D :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

theorem two_largeFiberAbelEnvelope_eq_relative
    {K C : ℝ} {D R : ℕ} {H : Finset ℕ} (m : H) (r : H → ℕ)
    (hlogR : Real.log R ≠ 0) :
    2 * largeFiberAbelEnvelope K C D R m r =
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
        Real.log R * largeFiberRelativeError K C D R := by
  unfold largeFiberAbelEnvelope largeFiberRelativeError
  field_simp [hlogR]
  ring

theorem sq_ge_baseline_sq_sub_error
    {z y A eta b : ℝ}
    (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hb0 : 0 ≤ b) (hby : b ≤ y) (hyA : y ≤ A)
    (herr : |z - y| ≤ A * eta) :
    b ^ 2 - A ^ 2 * (2 * eta + eta ^ 2) ≤ z ^ 2 := by
  have hy0 : 0 ≤ y := hb0.trans hby
  have hyabs : |y| = y := abs_of_nonneg hy0
  have hzabs : |z| ≤ A + A * eta := by
    calc
      |z| = |y + (z - y)| := by ring_nf
      _ ≤ |y| + |z - y| := abs_add_le _ _
      _ ≤ A + A * eta := by rw [hyabs]; gcongr
  have hsum : |z + y| ≤ 2 * A + A * eta := by
    calc
      |z + y| ≤ |z| + |y| := abs_add_le _ _
      _ ≤ (A + A * eta) + A := by rw [hyabs]; gcongr
      _ = 2 * A + A * eta := by ring
  have hfac : 0 ≤ A * eta := mul_nonneg hA heta
  have hsum0 : 0 ≤ 2 * A + A * eta := by positivity
  have hsquares : |z ^ 2 - y ^ 2| ≤
      A ^ 2 * (2 * eta + eta ^ 2) := by
    rw [show z ^ 2 - y ^ 2 = (z - y) * (z + y) by ring, abs_mul]
    calc
      |z - y| * |z + y| ≤ (A * eta) * (2 * A + A * eta) := by
        exact mul_le_mul herr hsum (abs_nonneg _) hfac
      _ = A ^ 2 * (2 * eta + eta ^ 2) := by ring
  have hyy : b ^ 2 ≤ y ^ 2 := by nlinarith
  have hdiff : y ^ 2 - z ^ 2 ≤
      A ^ 2 * (2 * eta + eta ^ 2) := by
    have := le_abs_self (y ^ 2 - z ^ 2)
    rw [abs_sub_comm] at hsquares
    exact this.trans hsquares
  linarith

theorem tupleCoordinateFiberSum_sq_lower
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
    {H : Finset ℕ} {D R : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 56) :
    let O := tupleCoordinateOuterProfile R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    let c := largeOuterCutoff
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
        Real.log R)
    let eta := largeFiberRelativeError K C D R
    ((O * S * L) * (c * largeShortMass)) ^ 2 -
        (O * S * L) ^ 2 * (2 * eta + eta ^ 2) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
        (BoundedGaps.Maynard.maynardYValue H R (primorial D)
          (tupleLargeCandidate H)) m r ^ 2 := by
  dsimp only
  let O := tupleCoordinateOuterProfile R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let I := tupleFiberEndpointIntegral R m r
  let c := largeOuterCutoff
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
      Real.log R)
  let eta := largeFiberRelativeError K C D R
  let x := tupleFiberScalarSum R (primorial D) m r
  let z := BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
    (BoundedGaps.Maynard.maynardYValue H R (primorial D)
      (tupleLargeCandidate H)) m r
  let A := O * S * L
  let y := A * I
  let b := A * (c * largeShortMass)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hO := tupleCoordinateOuterProfile_nonneg_le_one m hr hR
  have hS : 0 < S :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_pos m r hr
  have hL : 0 < L := by dsimp [L]; linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg hO.1 hS.le) hL.le
  have hI := tupleFiberEndpointIntegral_bounds m hr hR hQ hlog3
  have hI0 : 0 ≤ I := by
    have hc0 := largeOuterCutoff_nonneg
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
        Real.log R)
    have hm0 : 0 < largeShortMass :=
      inv_threeK_lt_largeShortMass.trans'
        (inv_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos)))
    exact (mul_nonneg hc0 hm0.le).trans hI.1
  have hI1 : I ≤ 1 := hI.2
  have heta : 0 ≤ eta :=
    largeFiberRelativeError_nonneg hK hC hD hlogR
  have hz : z = O * x := by
    dsimp [z, O, x]
    exact tupleCoordinateFiberSum_eq_outer_mul_scalarSum m hr hrm hR
  have hxerr := tupleFiberScalarSum_abel_bound hAbel m r hr hD hlogR hQ
  have hscale : 2 * largeFiberAbelEnvelope K C D R m r =
      S * L * eta := by
    simpa [S, L, eta] using
      two_largeFiberAbelEnvelope_eq_relative (K := K) (C := C) m r hL.ne'
  have herr : |z - y| ≤ A * eta := by
    rw [hz]
    have heq : O * x - y = O * (x - S * L * I) := by
      dsimp [y, A]
      ring
    rw [heq, abs_mul, abs_of_nonneg hO.1]
    calc
      O * |x - S * L * I| ≤ O * (2 * largeFiberAbelEnvelope K C D R m r) :=
        mul_le_mul_of_nonneg_left (by simpa [x, S, L, I] using hxerr) hO.1
      _ = A * eta := by rw [hscale]; dsimp [A]; ring
  have hc0 : 0 ≤ c := by dsimp [c]; apply largeOuterCutoff_nonneg
  have hm0 : 0 < largeShortMass := by
    have hden : 0 < 3 * (largeK : ℝ) :=
      mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos)
    have hbase : 0 < (3 * (largeK : ℝ))⁻¹ := inv_pos.mpr hden
    exact hbase.trans inv_threeK_lt_largeShortMass
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hby : b ≤ y := by
    dsimp [b, y]
    exact mul_le_mul_of_nonneg_left hI.1 hA
  have hyA : y ≤ A := by
    dsimp [y]
    nlinarith
  exact sq_ge_baseline_sq_sub_error hA heta hb0 hby hyA herr

end

end Erdos6.Maynard
