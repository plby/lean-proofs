/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Outer
import ErdosProblems.Erdos6.GenericFiberDiagonalLower

/-!
# Lower bounds for variable-candidate coordinate fibers
-/

namespace MaynardTao

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval

noncomputable section

theorem tupleOffFace_logProduct_eq_variableCoordinateSum
    {H : Finset ℕ} {R W : ℕ} (m : H)
    (u : Erdos6.Maynard.tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace H m) R W) (hR : 1 < R) :
    Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m
        (Erdos6.Maynard.tupleOffFaceExtension m u)) / Real.log R =
      Erdos4.VariableMaynard.coordinateSum
        (fun h : Erdos6.Maynard.tupleOffFace H m =>
          Real.log (u h) / Real.log R) := by
  simpa [Erdos6.Maynard.largeCoordinateSum,
    Erdos4.VariableMaynard.coordinateSum] using
    Erdos6.Maynard.tupleOffFace_logProduct_eq_coordinateSum m u hu hR

theorem tupleVariableOuterProfile_nonneg_le_one
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A)
    {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R) :
    0 ≤ tupleVariableOuterProfile A R m r ∧
      tupleVariableOuterProfile A R m r ≤ 1 := by
  have hH : 0 < H.card := Finset.card_pos.mpr ⟨m.1, m.2⟩
  have hlam : 0 < A * (H.card : ℝ) :=
    mul_pos hA (by exact_mod_cast hH)
  have hbox := hr.mem_maynardDivisorTupleBox
  have hcoord : ∀ h : H,
      Real.log (r h) / Real.log R ∈ Set.Icc (0 : ℝ) 1 :=
    fun h => BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR hbox h
  unfold tupleVariableOuterProfile
  constructor
  · exact Finset.prod_nonneg fun h hh =>
      inverseAffineProfile_nonneg hlam (hcoord h).1
  · calc
      (∏ h ∈ (Finset.univ : Finset H).erase m,
          inverseAffineProfile (A * (H.card : ℝ))
            (Real.log (r h) / Real.log R)) ≤
          ∏ _h ∈ (Finset.univ : Finset H).erase m, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro h hh
          exact inverseAffineProfile_nonneg hlam (hcoord h).1
        · intro h hh
          exact inverseAffineProfile_le_one hlam (hcoord h).1
      _ = 1 := by simp

theorem tupleVariableOuterProfile_sq_eq_density
    {H : Finset ℕ} {A : ℝ} {R W : ℕ} (m : H)
    (u : Erdos6.Maynard.tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace H m) R W) (hR : 1 < R) :
    tupleVariableOuterProfile A R m
        (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 =
      tupleVariableOuterDensity H.card A
        (fun h : Erdos6.Maynard.tupleOffFace H m =>
          Real.log (u h) / Real.log R) := by
  unfold tupleVariableOuterProfile tupleVariableOuterDensity
  rw [← Finset.prod_pow]
  rw [Erdos6.Maynard.prod_subtype_erase_eq_offFace]
  apply Finset.prod_congr rfl
  intro h hh
  have hhmem : h.1 ∈ H.erase m.1 := by
    simpa [Erdos6.Maynard.tupleOffFace] using h.2
  let hfull : H := ⟨h.1, (Finset.mem_erase.mp hhmem).2⟩
  have hne : hfull ≠ m := by
    intro heq
    exact (Finset.mem_erase.mp hhmem).1
      (by simpa [hfull] using congrArg (fun z : H => z.1) heq)
  have hext : Erdos6.Maynard.tupleOffFaceExtension m u hfull = u h := by
    rw [Erdos6.Maynard.tupleOffFaceExtension_off m u hfull hne]
  simpa [hfull, Erdos6.Maynard.tupleOffFace] using congrArg
    (fun n : ℕ => inverseAffineProfile (A * (H.card : ℝ))
      (Real.log n / Real.log R) ^ 2) hext

theorem tupleVariableFiberArithmeticScale_eq_outer
    {H : Finset ℕ} {A : ℝ} {D R : ℕ} (m : H)
    (u : Erdos6.Maynard.tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace H m) R (primorial D)) (hR : 1 < R) :
    let r := Erdos6.Maynard.tupleOffFaceExtension m u
    let O := tupleVariableOuterProfile A R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    (O * S * L) ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
        tupleVariableOuterDensity H.card A
          (fun h : Erdos6.Maynard.tupleOffFace H m =>
            Real.log (u h) / Real.log R)) := by
  dsimp only
  let r := Erdos6.Maynard.tupleOffFaceExtension m u
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r :=
    (Erdos6.Maynard.isMaynardDivisorTuple_extension_iff R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := Erdos6.Maynard.tupleOffFaceExtension_at m u
  have hseries :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
      m r hr hrm
  have houter := Erdos6.Maynard.tupleOffFaceExtension_outerWeight m u hu
  have hdensity := tupleVariableOuterProfile_sq_eq_density
    (A := A) m u hu hR
  rw [show (tupleVariableOuterProfile A R m r *
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
      Real.log R) ^ 2 /
      ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      tupleVariableOuterProfile A R m r ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)) by ring]
  rw [hseries, houter, hdensity]
  ring

theorem tupleVariableFiberEndpointIntegral_nonneg
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A)
    {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R) :
    0 ≤ tupleVariableFiberEndpointIntegral A R m r := by
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hupper : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg (Real.log_natCast_nonneg Q) hlogR.le
  unfold tupleVariableFiberEndpointIntegral
  apply intervalIntegral.integral_nonneg
  · exact hupper
  · intro x hx
    have hH : 0 < H.card := Finset.card_pos.mpr ⟨m.1, m.2⟩
    exact inverseAffineProfile_nonneg
      (mul_pos hA (by exact_mod_cast hH)) hx.1

theorem tupleVariableFiberEndpointIntegral_le_one
    {H : Finset ℕ} {A : ℝ} (hA : 0 < A)
    {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R) :
    tupleVariableFiberEndpointIntegral A R m r ≤ 1 := by
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  have hP : 0 < BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  by_cases hQ0 : Q = 0
  · simp [tupleVariableFiberEndpointIntegral, Q, hQ0]
  have hQ : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hQP : Q * BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r < R := by
    have hle : Q * BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r ≤
        R - 1 := by
      unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
      simpa [Nat.mul_comm] using
        Nat.mul_div_le (R - 1)
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
    omega
  have hQltR : Q < R := by
    have hQleQP : Q ≤ Q *
        BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hP
    exact hQleQP.trans_lt hQP
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hq0 : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQ)) hlogR.le
  have hq1 : Real.log Q / Real.log R ≤ 1 := by
    apply (div_le_one hlogR).2
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hQ))
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hQltR.le)
  have hH : 0 < H.card := Finset.card_pos.mpr ⟨m.1, m.2⟩
  have hlam : 0 < A * (H.card : ℝ) :=
    mul_pos hA (by exact_mod_cast hH)
  unfold tupleVariableFiberEndpointIntegral
  calc
    (∫ x in (0 : ℝ)..(Real.log Q / Real.log R),
      inverseAffineProfile (A * (H.card : ℝ)) x) ≤
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hq0
      · exact (continuous_inverseAffineProfile hlam).intervalIntegrable 0 _
      · exact intervalIntegrable_const
      · intro x hx
        exact inverseAffineProfile_le_one hlam hx.1
    _ = Real.log Q / Real.log R := by simp
    _ ≤ 1 := hq1

theorem variableShortMass_eq_interval_inverseAffineProfile
    {K : ℕ} {A δ : ℝ} (hδ : 0 ≤ δ) :
    variableShortMass K A δ =
      ∫ x in (0 : ℝ)..δ,
        inverseAffineProfile (A * (K : ℝ)) x := by
  unfold variableShortMass
  rw [intervalIntegral.integral_of_le hδ,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact (inverseAffineProfile_eq_factor hx.1).symm

theorem tupleVariableFiberEndpointIntegral_ge_cutoff_shortMass_of_good_endpoint
    {H : Finset ℕ} {A q0 q1 δ : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hδ : 0 < δ) (hslack : q1 + δ < 1)
    {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog3 : Real.log 3 / Real.log R ≤ 1 - q1 - δ) :
    variableOuterCutoff q0 q1
        (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
          Real.log R) *
        variableShortMass H.card A δ ≤
      tupleVariableFiberEndpointIntegral A R m r := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  let qend := Real.log Q / Real.log R
  let s := Real.log P / Real.log R
  let c := variableOuterCutoff q0 q1 s
  have hH : 0 < H.card := Finset.card_pos.mpr ⟨m.1, m.2⟩
  have hlam : 0 < A * (H.card : ℝ) :=
    mul_pos hA (by exact_mod_cast hH)
  have hshort0 : 0 ≤ variableShortMass H.card A δ :=
    (variableShortMass_pos hH hA hδ).le
  have hc0 : 0 ≤ c := variableOuterCutoff_nonneg q0 q1 s
  have hc1 : c ≤ 1 := variableOuterCutoff_le_one q0 q1 s
  by_cases hc : c = 0
  · change c * variableShortMass H.card A δ ≤
        tupleVariableFiberEndpointIntegral A R m r
    rw [hc, zero_mul]
    exact tupleVariableFiberEndpointIntegral_nonneg hA m hr hR
  have hs : s < q1 := by
    apply lt_of_not_ge
    intro hqs
    exact hc (variableOuterCutoff_eq_zero hq hqs)
  have hendpoint := Erdos6.Maynard.coordinateFiberEndpoint_ratio_ge_complement_sub
    m hr hR hQ
  have hqLower : 1 - s - Real.log 3 / Real.log R ≤ qend := by
    simpa [P, Q, qend, s] using hendpoint
  have hδq : δ ≤ qend := by
    linarith
  have hq0 : 0 ≤ qend := by
    have hQ' : 1 < Q := by simpa [Q, P] using hQ
    have hQpos : 0 < Q := by omega
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hQpos))
      (Real.log_pos (by exact_mod_cast hR)).le
  have hmono :
      (∫ x in (0 : ℝ)..δ,
        inverseAffineProfile (A * (H.card : ℝ)) x) ≤
      ∫ x in (0 : ℝ)..qend,
        inverseAffineProfile (A * (H.card : ℝ)) x := by
    apply intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := qend) le_rfl hδ.le hδq
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact inverseAffineProfile_nonneg hlam hx.1.le
    · exact (continuous_inverseAffineProfile hlam).intervalIntegrable 0 qend
  have hshortLe :
      variableShortMass H.card A δ ≤
        tupleVariableFiberEndpointIntegral A R m r := by
    rw [variableShortMass_eq_interval_inverseAffineProfile hδ.le]
    simpa [tupleVariableFiberEndpointIntegral, P, Q, qend] using hmono
  exact (mul_le_of_le_one_left hshort0 hc1).trans hshortLe

theorem variableOuterCutoff_eq_zero_of_bad_endpoint
    {H : Finset ℕ} {q0 q1 : ℝ} (hq : q0 < q1)
    {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R)
    (hbad : ¬1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog2 : Real.log 2 / Real.log R < 1 - q1) :
    variableOuterCutoff q0 q1
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
  apply variableOuterCutoff_eq_zero hq
  linarith

theorem tupleVariableCoordinateFiberSum_sq_lower
    {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    {H : Finset ℕ} {A q0 q1 δ : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hδ : 0 < δ) (hslack : q1 + δ < 1)
    (hAbel : ∀ {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleVariableFiberScalarSum A R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleVariableFiberEndpointIntegral A R m r| ≤
          2 * inverseAffineAbelEnvelope U C D R m r)
    {D R : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r)
    (hrm : r m = 1) (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r))
    (hlog3 : Real.log 3 / Real.log R ≤ 1 - q1 - δ) :
    let O := tupleVariableOuterProfile A R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    let c := variableOuterCutoff q0 q1
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
        Real.log R)
    let eta := inverseAffineRelativeError U C D R
    ((O * S * L) * (c * variableShortMass H.card A δ)) ^ 2 -
        (O * S * L) ^ 2 * (2 * eta + eta ^ 2) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
        (BoundedGaps.Maynard.maynardYValue H R (primorial D)
          (tupleVariableCandidate H A)) m r ^ 2 := by
  dsimp only
  let O := tupleVariableOuterProfile A R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let I := tupleVariableFiberEndpointIntegral A R m r
  let c := variableOuterCutoff q0 q1
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
      Real.log R)
  let eta := inverseAffineRelativeError U C D R
  let x := tupleVariableFiberScalarSum A R (primorial D) m r
  let z := BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
    (BoundedGaps.Maynard.maynardYValue H R (primorial D)
      (tupleVariableCandidate H A)) m r
  let M := O * S * L
  let y := M * I
  let b := M * (c * variableShortMass H.card A δ)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hO := tupleVariableOuterProfile_nonneg_le_one hA m hr hR
  have hS : 0 < S :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_pos m r hr
  have hL : 0 < L := by dsimp [L]; linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hO.1 hS.le) hL.le
  have hI0 : 0 ≤ I :=
    tupleVariableFiberEndpointIntegral_nonneg hA m hr hR
  have hI1 : I ≤ 1 :=
    tupleVariableFiberEndpointIntegral_le_one hA m hr hR
  have hcut := tupleVariableFiberEndpointIntegral_ge_cutoff_shortMass_of_good_endpoint
    hA hq hδ hslack m hr hR hQ hlog3
  have heta : 0 ≤ eta :=
    inverseAffineRelativeError_nonneg hU hC hD hlogR
  have hz : z = O * x := by
    dsimp [z, O, x]
    exact tupleVariableCoordinateFiberSum_eq_outer_mul_scalarSum m hr hrm hR
  have hxerr := hAbel m r hr hD hlogR hQ
  have hscale : 2 * inverseAffineAbelEnvelope U C D R m r =
      S * L * eta := by
    simpa [S, L, eta] using
      two_inverseAffineAbelEnvelope_eq_relative (U := U) (C := C) m r hL.ne'
  have herr : |z - y| ≤ M * eta := by
    rw [hz]
    have heq : O * x - y = O * (x - S * L * I) := by
      dsimp [y, M]
      ring
    rw [heq, abs_mul, abs_of_nonneg hO.1]
    calc
      O * |x - S * L * I| ≤
          O * (2 * inverseAffineAbelEnvelope U C D R m r) :=
        mul_le_mul_of_nonneg_left
          (by simpa [x, S, L, I] using hxerr) hO.1
      _ = M * eta := by rw [hscale]; dsimp [M]; ring
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact variableOuterCutoff_nonneg _ _ _
  have hshort0 : 0 ≤ variableShortMass H.card A δ := by
    have hH : 0 < H.card := Finset.card_pos.mpr ⟨m.1, m.2⟩
    exact (variableShortMass_pos hH hA hδ).le
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hby : b ≤ y := by
    dsimp [b, y]
    exact mul_le_mul_of_nonneg_left hcut hM
  have hyM : y ≤ M := by
    dsimp [y]
    nlinarith
  exact Erdos6.Maynard.sq_ge_baseline_sq_sub_error
    hM heta hb0 hby hyM herr

theorem tupleVariableCoordinateFiberTerm_lower
    {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    {H : Finset ℕ} {A q0 q1 δ : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hδ : 0 < δ) (hslack : q1 + δ < 1)
    (hAbel : ∀ {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleVariableFiberScalarSum A R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleVariableFiberEndpointIntegral A R m r| ≤
          2 * inverseAffineAbelEnvelope U C D R m r)
    {D R : ℕ} (m : H)
    (u : Erdos6.Maynard.tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace H m) R (primorial D))
    (hD : 2 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hlog2 : Real.log 2 / Real.log R < 1 - q1)
    (hlog3 : Real.log 3 / Real.log R ≤ 1 - q1 - δ) :
    let r := Erdos6.Maynard.tupleOffFaceExtension m u
    let point := fun h : Erdos6.Maynard.tupleOffFace H m =>
      Real.log (u h) / Real.log R
    let eta := inverseAffineRelativeError U C D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
        (variableShortMass H.card A δ ^ 2 *
            tupleVariableOuterSquaredIntegrand H.card A q0 q1 point -
          (2 * eta + eta ^ 2) *
            tupleVariableOuterDensity H.card A point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleVariableCandidate H A)) m r ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) := by
  dsimp only
  let r := Erdos6.Maynard.tupleOffFaceExtension m u
  let point := fun h : Erdos6.Maynard.tupleOffFace H m =>
    Real.log (u h) / Real.log R
  let eta := inverseAffineRelativeError U C D R
  let O := tupleVariableOuterProfile A R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let c := variableOuterCutoff q0 q1
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
      Real.log R)
  let g := ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r :=
    (Erdos6.Maynard.isMaynardDivisorTuple_extension_iff R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := Erdos6.Maynard.tupleOffFaceExtension_at m u
  have hg : 0 < g := by
    dsimp [g]
    exact BoundedGaps.Maynard.maynardS2G_product_pos_of_supported hD hr
  have hscale := tupleVariableFiberArithmeticScale_eq_outer
    (A := A) m u hu hR
  have hcut : c = variableOuterCutoff q0 q1
      (Erdos4.VariableMaynard.coordinateSum point) := by
    dsimp [c, point, r]
    rw [tupleOffFace_logProduct_eq_variableCoordinateSum m u hu hR]
  have hdensity : O ^ 2 =
      tupleVariableOuterDensity H.card A point := by
    dsimp [O, point, r]
    exact tupleVariableOuterProfile_sq_eq_density (A := A) m u hu hR
  by_cases hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  · have hraw := tupleVariableCoordinateFiberSum_sq_lower
      hU hC hA hq hδ hslack hAbel m hr hrm (by omega) hlogR hQ hlog3
    have hdiv := (div_le_div_iff_of_pos_right hg).mpr hraw
    change (((O * S * L) *
        (c * variableShortMass H.card A δ)) ^ 2 -
      (O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g ≤ _ at hdiv
    rw [sub_div] at hdiv
    have houter :
        (O * S * L) ^ 2 / g =
          BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
            (BoundedGaps.Maynard.outerTupleWeight
              (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
              tupleVariableOuterDensity H.card A point) := by
      simpa [O, S, L, g, r, point] using hscale
    rw [show ((O * S * L) *
        (c * variableShortMass H.card A δ)) ^ 2 / g =
        ((O * S * L) ^ 2 / g) *
          (c ^ 2 * variableShortMass H.card A δ ^ 2) by ring,
      show ((O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g =
        ((O * S * L) ^ 2 / g) * (2 * eta + eta ^ 2) by ring,
      houter] at hdiv
    rw [hcut] at hdiv
    change BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
        (variableShortMass H.card A δ ^ 2 *
            tupleVariableOuterSquaredIntegrand H.card A q0 q1 point -
          (2 * eta + eta ^ 2) *
            tupleVariableOuterDensity H.card A point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleVariableCandidate H A)) m r ^ 2 / g
    calc
      _ = BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight
                (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
                tupleVariableOuterDensity H.card A point) *
              (variableOuterCutoff q0 q1
                  (Erdos4.VariableMaynard.coordinateSum point) ^ 2 *
                variableShortMass H.card A δ ^ 2) -
            BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight
                (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
                tupleVariableOuterDensity H.card A point) *
              (2 * eta + eta ^ 2) := by
          unfold tupleVariableOuterSquaredIntegrand
          ring
      _ ≤ _ := hdiv
  · have hc : c = 0 :=
      variableOuterCutoff_eq_zero_of_bad_endpoint hq m hr hR hQ hlog2
    have hsq0 : 0 ≤
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleVariableCandidate H A)) m r ^ 2 / g :=
      div_nonneg (sq_nonneg _) hg.le
    have hweight : 0 ≤ BoundedGaps.Maynard.outerTupleWeight
        (Erdos6.Maynard.tupleOffFace H m) (primorial D) u :=
      Erdos6.Maynard.outerTupleWeight_nonneg _ _ _
    have heta : 0 ≤ eta :=
      inverseAffineRelativeError_nonneg hU hC (by omega) hlogR
    have herr0 : 0 ≤ 2 * eta + eta ^ 2 := by
      nlinarith [sq_nonneg eta]
    have hd0 : 0 ≤ tupleVariableOuterDensity H.card A point := by
      rw [← hdensity]
      exact sq_nonneg _
    have hs0 : 0 ≤ BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 :=
      sq_nonneg _
    have hL0 : 0 ≤ L ^ 2 := sq_nonneg _
    rw [hcut] at hc
    unfold tupleVariableOuterSquaredIntegrand
    rw [hc]
    norm_num
    have hnonpos := (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hs0 hL0) hweight)
      (neg_nonpos.mpr (mul_nonneg herr0 hd0))).trans hsq0
    simpa [L, g, eta, point, r, mul_assoc, mul_left_comm, mul_comm] using hnonpos

theorem tupleVariableCoordinateFiberSquareDiagonal_lower
    {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    {H : Finset ℕ} {A q0 q1 δ : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hδ : 0 < δ) (hslack : q1 + δ < 1)
    (hAbel : ∀ {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |tupleVariableFiberScalarSum A R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * tupleVariableFiberEndpointIntegral A R m r| ≤
          2 * inverseAffineAbelEnvelope U C D R m r)
    {alpha : ℝ} {N : ℕ} (m : H)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hlogR : 2 ≤ Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
    (hlog2 : Real.log 2 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) < 1 - q1)
    (hlog3 : Real.log 3 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ 1 - q1 - δ) :
    let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
    let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
    let eta := inverseAffineRelativeError U C D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (variableShortMass H.card A δ ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterSquaredIntegrand H.card A q0 q1) N -
          (2 * eta + eta ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterDensity H.card A) N) ≤
      tupleCoordinateFiberSquareDiagonalFor H alpha
        (tupleVariableCandidate H A) N m := by
  dsimp only
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let eta := inverseAffineRelativeError U C D R
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  let S := BoundedGaps.Maynard.maynardDivisorTupleSupport
    (Erdos6.Maynard.tupleOffFace H m) R (primorial D)
  have hpoint : ∀ u : Erdos6.Maynard.tupleOffFace H m → ℕ,
      Erdos6.Maynard.tupleNormalizedLogPoint
          (Erdos6.Maynard.tupleOffFace H m) alpha N u =
        fun h : Erdos6.Maynard.tupleOffFace H m =>
          Real.log (u h) / Real.log R := by
    intro u
    rfl
  have hsum :
      ∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
        (variableShortMass H.card A δ ^ 2 *
            tupleVariableOuterSquaredIntegrand H.card A q0 q1
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace H m) alpha N u) -
          (2 * eta + eta ^ 2) *
            tupleVariableOuterDensity H.card A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace H m) alpha N u))) ≤
      ∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
            (BoundedGaps.Maynard.maynardYValue H R (primorial D)
              (tupleVariableCandidate H A)) m
                (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G
            (Erdos6.Maynard.tupleOffFaceExtension m u h) : ℝ) := by
    apply Finset.sum_le_sum
    intro u hu
    have ht := tupleVariableCoordinateFiberTerm_lower hU hC hA hq hδ
      hslack hAbel m u hu hD hlogR hlog2 hlog3
    simpa [P, D, R, eta, hpoint u] using ht
  have hreindex := Erdos6.Maynard.sum_coordinateOneSupport_eq_offFace
    R (primorial D) m
    (fun r =>
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
          (BoundedGaps.Maynard.maynardYValue H R (primorial D)
            (tupleVariableCandidate H A)) m r ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ))
  have hright :
      (∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R (primorial D)
            (BoundedGaps.Maynard.maynardYValue H R (primorial D)
              (tupleVariableCandidate H A)) m
                (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G
            (Erdos6.Maynard.tupleOffFaceExtension m u h) : ℝ)) =
        tupleCoordinateFiberSquareDiagonalFor H alpha
          (tupleVariableCandidate H A) N m := by
    unfold tupleCoordinateFiberSquareDiagonalFor
    simpa [S, D, R, Erdos6.Maynard.maynardModulus,
      Erdos6.Maynard.maynardRadius,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using hreindex.symm
  rw [hright] at hsum
  have hleft :
      (∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace H m) (primorial D) u *
        (variableShortMass H.card A δ ^ 2 *
            tupleVariableOuterSquaredIntegrand H.card A q0 q1
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace H m) alpha N u) -
          (2 * eta + eta ^ 2) *
            tupleVariableOuterDensity H.card A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace H m) alpha N u)))) =
      P * (variableShortMass H.card A δ ^ 2 *
          Erdos6.Maynard.tupleOuterMaynardWeightedMoment
            (Erdos6.Maynard.tupleOffFace H m) alpha
            (tupleVariableOuterSquaredIntegrand H.card A q0 q1) N -
        (2 * eta + eta ^ 2) *
          Erdos6.Maynard.tupleOuterMaynardWeightedMoment
            (Erdos6.Maynard.tupleOffFace H m) alpha
            (tupleVariableOuterDensity H.card A) N) := by
    unfold Erdos6.Maynard.tupleOuterMaynardWeightedMoment
    dsimp [S, D, R]
    simp only [BoundedGaps.Maynard.engelsmaMaynardModulus]
    simp only [mul_sub, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hleft] at hsum
  simpa [P, D, R, eta] using hsum

theorem eventually_variableFiber_conditions
    {alpha q1 δ : ℝ} (halpha : 0 < alpha)
    (hq1 : q1 < 1) (hslack : q1 + δ < 1) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) ∧
      2 ≤ Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ∧
      Real.log 2 / Real.log
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) < 1 - q1 ∧
      Real.log 3 / Real.log
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
            1 - q1 - δ := by
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  have hL :=
    BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hlog2 : Tendsto (fun N : ℕ => Real.log 2 /
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := hL.const_div_atTop (Real.log 2)
  have hlog3 : Tendsto (fun N : ℕ => Real.log 3 /
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := hL.const_div_atTop (Real.log 3)
  have he2 := hlog2.eventually (eventually_lt_nhds
    (show (0 : ℝ) < 1 - q1 by linarith))
  have he3 := hlog3.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 - q1 - δ by linarith))
  filter_upwards [eventually_ge_atTop (N₀ + 1),
      hL.eventually (eventually_ge_atTop 2), he2, he3] with N hN hLN h2 h3
  exact ⟨hN₀ (N - 1) (by omega), hLN, h2, h3⟩

theorem eventually_tupleVariableCoordinateFiberSquareDiagonal_normalized_gt
    {H : Finset ℕ} (hcard2 : 2 ≤ H.card)
    {A q0 q1 δ γ alpha : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hq1 : q1 < 1) (hδ : 0 < δ)
    (hslack : q1 + δ < 1) (hγ : 0 < γ)
    (m : H) (halpha : 0 < alpha)
    (hgood : γ * Erdos4.VariableMaynard.baseMass H.card A ^
        Fintype.card (Erdos6.Maynard.tupleOffFace H m) <
      ∫ t : Erdos6.Maynard.tupleOffFace H m → ℝ in
        variableGoodRegion q0 (Erdos6.Maynard.tupleOffFace H m),
        Erdos4.VariableMaynard.productDensity H.card A t) :
    ∀ᶠ N : ℕ in atTop,
      variableShortMass H.card A δ ^ 2 *
          (γ * Erdos4.VariableMaynard.baseMass H.card A ^
            Fintype.card (Erdos6.Maynard.tupleOffFace H m)) <
        tupleCoordinateFiberSquareDiagonalFor H alpha
            (tupleVariableCandidate H A) N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace H m) alpha N) := by
  have hH : 0 < H.card := by omega
  have hOffCard : 0 < (Erdos6.Maynard.tupleOffFace H m).card := by
    unfold Erdos6.Maynard.tupleOffFace
    rw [Finset.card_erase_of_mem m.2]
    omega
  obtain ⟨h0val, h0mem⟩ :=
    Finset.card_pos.mp hOffCard
  let h0 : Erdos6.Maynard.tupleOffFace H m := ⟨h0val, h0mem⟩
  obtain ⟨U, C, hU, hC, hAbelRaw⟩ :=
    exists_uniform_inverseAffineFiberAbel_bound
      (mul_pos hA (show (0 : ℝ) < H.card by exact_mod_cast hH))
  have hAbel : ∀ {D R : ℕ} (m : H) (r : H → ℕ),
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r →
      1 ≤ D → 2 ≤ Real.log R →
      1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
      |tupleVariableFiberScalarSum A R (primorial D) m r -
        BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
          Real.log R * tupleVariableFiberEndpointIntegral A R m r| ≤
        2 * inverseAffineAbelEnvelope U C D R m r := by
    intro D R m r hr hD hlogR hQ
    simpa [tupleVariableFiberScalarSum,
      tupleVariableFiberEndpointIntegral] using
      hAbelRaw m r hr hD hlogR hQ
  let eta : ℕ → ℝ := fun N => inverseAffineRelativeError U C
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let Aseq : ℕ → ℝ := fun N =>
    Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
      (Erdos6.Maynard.tupleOffFace H m) alpha
      (tupleVariableOuterSquaredIntegrand H.card A q0 q1) N
  let Bseq : ℕ → ℝ := fun N =>
    Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
      (Erdos6.Maynard.tupleOffFace H m) alpha
      (tupleVariableOuterDensity H.card A) N
  let IA := ∫ t in BoundedGaps.Maynard.finiteSimplexOf
      (Erdos6.Maynard.tupleOffFace H m),
    tupleVariableOuterSquaredIntegrand H.card A q0 q1 t
  let IB := ∫ t in BoundedGaps.Maynard.finiteSimplexOf
      (Erdos6.Maynard.tupleOffFace H m),
    tupleVariableOuterDensity H.card A t
  have heta : Tendsto eta atTop (nhds 0) := by
    simpa [eta] using tendsto_inverseAffineRelativeError_zero halpha U C
  have hAseq : Tendsto Aseq atTop (nhds IA) := by
    dsimp [Aseq, IA]
    exact Erdos6.Maynard.tendsto_normalizedTupleOuterMaynardWeightedMoment
      h0 halpha
      (continuous_tupleVariableOuterSquaredIntegrand hH hA q0 q1
        (Erdos6.Maynard.tupleOffFace H m))
      (fun t ht =>
        tupleVariableOuterSquaredIntegrand_bounds hH hA q0 q1 t ht.1)
  have hBseq : Tendsto Bseq atTop (nhds IB) := by
    dsimp [Bseq, IB]
    exact Erdos6.Maynard.tendsto_normalizedTupleOuterMaynardWeightedMoment
      h0 halpha
      (continuous_tupleVariableOuterDensity_of_pos hH hA
        (Erdos6.Maynard.tupleOffFace H m))
      (fun t ht => tupleVariableOuterDensity_bounds hH hA t ht.1)
  have herr : Tendsto (fun N : ℕ => (2 * eta N + eta N ^ 2) * Bseq N)
      atTop (nhds 0) := by
    have he : Tendsto (fun N : ℕ => 2 * eta N + eta N ^ 2)
        atTop (nhds 0) := by
      convert (heta.const_mul 2).add (heta.pow 2) using 1 <;> norm_num
    simpa using he.mul hBseq
  have hbracket : Tendsto (fun N : ℕ =>
      variableShortMass H.card A δ ^ 2 * Aseq N -
        (2 * eta N + eta N ^ 2) * Bseq N)
      atTop (nhds (variableShortMass H.card A δ ^ 2 * IA)) := by
    simpa using (hAseq.const_mul (variableShortMass H.card A δ ^ 2)).sub herr
  have hIA :
      γ * Erdos4.VariableMaynard.baseMass H.card A ^
          Fintype.card (Erdos6.Maynard.tupleOffFace H m) < IA := by
    dsimp [IA]
    exact integral_tupleVariableOuterSquaredIntegrand_gt_goodMass
      hH hA hq hq1.le hgood
  have hshort : 0 < variableShortMass H.card A δ :=
    variableShortMass_pos hH hA hδ
  have hlimit :
      variableShortMass H.card A δ ^ 2 *
          (γ * Erdos4.VariableMaynard.baseMass H.card A ^
            Fintype.card (Erdos6.Maynard.tupleOffFace H m)) <
        variableShortMass H.card A δ ^ 2 * IA :=
    mul_lt_mul_of_pos_left hIA (sq_pos_of_pos hshort)
  have hbracketEventually := hbracket.eventually (eventually_gt_nhds hlimit)
  have hconditions := eventually_variableFiber_conditions halpha hq1 hslack
  have houterScale := Erdos6.Maynard.eventually_tupleNaturalScale_pos
    (H := Erdos6.Maynard.tupleOffFace H m) halpha
  filter_upwards [hbracketEventually, hconditions, houterScale] with
      N hbracketN hcond hscale
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  have hP : 0 < P := by
    dsimp [P]
    have hS := BoundedGaps.Maynard.preSieveSingularSeries_pos D
    have hL : 0 < Real.log R := by linarith [hcond.2.1]
    exact mul_pos (sq_pos_of_pos hS) (sq_pos_of_pos hL)
  have hfinite := tupleVariableCoordinateFiberSquareDiagonal_lower
    hU hC hA hq hδ hslack hAbel m
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have hdiv := div_le_div_of_nonneg_right hfinite
    (mul_nonneg hP.le hscale.le)
  have heq :
      P * (variableShortMass H.card A δ ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterSquaredIntegrand H.card A q0 q1) N -
          (2 * eta N + eta N ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterDensity H.card A) N) /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N) =
        variableShortMass H.card A δ ^ 2 * Aseq N -
          (2 * eta N + eta N ^ 2) * Bseq N := by
    dsimp [Aseq, Bseq]
    unfold Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
    field_simp [hP.ne', hscale.ne']
  change P * (variableShortMass H.card A δ ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterSquaredIntegrand H.card A q0 q1) N -
          (2 * eta N + eta N ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace H m) alpha
              (tupleVariableOuterDensity H.card A) N) /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N) ≤
        tupleCoordinateFiberSquareDiagonalFor H alpha
          (tupleVariableCandidate H A) N m /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N) at hdiv
  rw [heq] at hdiv
  exact hbracketN.trans_le (by
    simpa [D, R, P, eta] using hdiv)

end

end MaynardTao
