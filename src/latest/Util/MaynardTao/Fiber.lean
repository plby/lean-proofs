/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Profile
import Util.MaynardTao.Transport
import ErdosProblems.Erdos6.LargeOffFace

/-!
# Coordinate fibers for the variable Maynard candidate

This exposes the fixed-tuple scalar Abel argument with the inverse-affine
slope left as a parameter.
-/

namespace MaynardTao

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval

noncomputable section

def tupleVariableOuterProfile {H : Finset ℕ} (A : ℝ) (R : ℕ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∏ h ∈ (Finset.univ : Finset H).erase m,
    inverseAffineProfile (A * (H.card : ℝ))
      (Real.log (r h) / Real.log R)

def tupleVariableFiberScalarSum {H : Finset ℕ} (A : ℝ) (R W : ℕ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport H R W m r,
    ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
      inverseAffineProfile (A * (H.card : ℝ))
        (Real.log u / Real.log R)

def tupleVariableFiberEndpointIntegral {H : Finset ℕ} (A : ℝ) (R : ℕ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..
    (Real.log (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) /
        Real.log R),
      inverseAffineProfile (A * (H.card : ℝ)) x

theorem tupleVariableCandidate_eq_product_of_mem
    {H : Finset ℕ} {A : ℝ} {t : H → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    tupleVariableCandidate H A t =
      ∏ h : H, inverseAffineProfile (A * (H.card : ℝ)) (t h) := by
  rw [← tupleVariableContinuousProduct_eq_candidate_of_mem_simplex ht]
  unfold tupleVariableContinuousProduct
  apply Finset.prod_congr rfl
  intro h hh
  rw [inverseAffineProfile_eq_factor
    (hx := (ht.1 h (Set.mem_univ h)).1)]
  rw [Erdos4.variableContinuousFactor_eq_factor]
  exact mul_nonneg (Nat.cast_nonneg _) (ht.1 h (Set.mem_univ h)).1

theorem tupleVariableCandidate_update_eq_outer_mul_profile
    {H : Finset ℕ} {A : ℝ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hrm : r m = 1) (hR : 1 < R) {u : ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
      H R W m r) :
    tupleVariableCandidate H A
        (Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R)) =
      tupleVariableOuterProfile A R m r *
        inverseAffineProfile (A * (H.card : ℝ))
          (Real.log u / Real.log R) := by
  let d := Function.update r m u
  have hdMem : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W :=
    Erdos6.Maynard.update_mem_support_of_mem_coordinateFiber m hr hrm hu
  have hsimplex := Erdos6.Maynard.normalizedLog_mem_finiteSimplex_of_mem_support
    hR hdMem
  have hpoint :
      BoundedGaps.Maynard.normalizedDivisorLogTuple H R d =
        Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R) := by
    funext h
    by_cases hh : h = m
    · subst h
      simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
    · simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple, hh]
  rw [← hpoint, tupleVariableCandidate_eq_product_of_mem hsimplex]
  unfold tupleVariableOuterProfile
  rw [← Finset.mul_prod_erase (Finset.univ : Finset H)
    (fun h => inverseAffineProfile (A * (H.card : ℝ))
      (BoundedGaps.Maynard.normalizedDivisorLogTuple H R d h))
    (Finset.mem_univ m)]
  have hm : BoundedGaps.Maynard.normalizedDivisorLogTuple H R d m =
      Real.log u / Real.log R := by
    simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
  rw [hm]
  have hprod :
      (∏ h ∈ (Finset.univ : Finset H).erase m,
        inverseAffineProfile (A * (H.card : ℝ))
          (BoundedGaps.Maynard.normalizedDivisorLogTuple H R d h)) =
      ∏ h ∈ (Finset.univ : Finset H).erase m,
        inverseAffineProfile (A * (H.card : ℝ))
          (Real.log (r h) / Real.log R) := by
    apply Finset.prod_congr rfl
    intro h hh
    have hne : h ≠ m := (Finset.mem_erase.mp hh).1
    simp [BoundedGaps.Maynard.normalizedDivisorLogTuple, d, hne]
  rw [hprod]
  ring

theorem tupleVariableCoordinateFiberSum_eq_outer_mul_scalarSum
    {H : Finset ℕ} {A : ℝ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hrm : r m = 1) (hR : 1 < R) :
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R W
        (BoundedGaps.Maynard.maynardYValue H R W
          (tupleVariableCandidate H A)) m r =
      tupleVariableOuterProfile A R m r *
        tupleVariableFiberScalarSum A R W m r := by
  rw [BoundedGaps.Maynard.maynardS2CoordinateFiberSum_maynardYValue_eq_sourceSum
    m hr hrm]
  unfold tupleVariableFiberScalarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [tupleVariableCandidate_update_eq_outer_mul_profile m hr hrm hR hu]
  ring

def inverseAffineAbelEnvelope (U C : ℝ) (D R : ℕ)
    {H : Finset ℕ} (m : H) (r : H → ℕ) : ℝ :=
  11 * BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
    (U + Real.log D + (Real.log (Real.log R) + C + 2) + Real.log 2)

theorem inverseAffineAbelEnvelope_nonneg
    {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    {D R : ℕ} (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    {H : Finset ℕ} (m : H) (r : H → ℕ)
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R
      (primorial D) r) :
    0 ≤ inverseAffineAbelEnvelope U C D R m r := by
  have hS : 0 ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r :=
    (BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_pos
      m r hr).le
  have hlogD : 0 ≤ Real.log D :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold inverseAffineAbelEnvelope
  positivity

theorem exists_uniform_inverseAffineFiberAbel_bound
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ U C : ℝ, 0 < U ∧ 0 ≤ C ∧
      ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R
            (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |(∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
              H R (primorial D) m r,
            ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
              inverseAffineProfile lam (Real.log u / Real.log R)) -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R *
            (∫ x in (0 : ℝ)..
              (Real.log
                  (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
                    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) /
                Real.log R), inverseAffineProfile lam x)| ≤
          2 * inverseAffineAbelEnvelope U C D R m r := by
  obtain ⟨U, C, hU, hC, hcum⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_logarithmic
  refine ⟨U, C, hU, hC, ?_⟩
  intro H D R m r hr hD hlogR hQ
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let E := inverseAffineAbelEnvelope U C D R m r
  have hR : 1 < R := by
    by_contra hnot
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast (le_of_not_gt hnot)
    have hlogNonpos : Real.log R ≤ 0 :=
      Real.log_nonpos (by positivity) hRle
    linarith
  have hE : 0 ≤ E :=
    inverseAffineAbelEnvelope_nonneg hU hC hD hlogR m r hr
  have hQone : 1 ≤ Q := by omega
  have hG : Continuous (inverseAffineProfile lam) :=
    continuous_inverseAffineProfile hlam
  have hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt
        (fun t => inverseAffineProfile lam (Real.log t / Real.log R))
        (deriv (fun t => inverseAffineProfile lam
          (Real.log t / Real.log R)) x) x := by
    intro x hx
    exact (hasDerivAt_inverseAffineProfile_comp_log hlam hR hx.1).differentiableAt.hasDerivAt
  have hfDerivInt : IntervalIntegrable
      (deriv (fun t : ℝ => inverseAffineProfile lam
        (Real.log t / Real.log R))) volume 1 Q :=
    intervalIntegrable_deriv_inverseAffine_comp_log hlam hR hQone
  have hfInt : IntegrableOn
      (deriv (fun t : ℝ => inverseAffineProfile lam
        (Real.log t / Real.log R)))
      (Set.Icc (1 : ℝ) Q) :=
    integrableOn_deriv_inverseAffine_comp_log_Icc hlam hR
  have hfNormInt : IntegrableOn
      (fun t => |deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)) t|) (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_abs_deriv_inverseAffine_comp_log_Ioc hlam hR
  have hmainInt : IntegrableOn
      (fun t => deriv (fun z : ℝ => inverseAffineProfile lam
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_deriv_mul_log_inverseAffine_comp_log S hlam hR
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |BoundedGaps.Maynard.abelCumulative
          (BoundedGaps.Maynard.maynardS2CoordinateFiberCoefficient
            H (primorial D) m r) t -
        S * Real.log t| ≤ E := by
    intro t ht
    exact hcum m r hr hlogR ht.1
  have hvariation :
      (∫ t in Set.Ioc (1 : ℝ) Q,
        |deriv (fun z : ℝ => inverseAffineProfile lam
          (Real.log z / Real.log R)) t|) ≤ 1 :=
    integral_abs_deriv_inverseAffine_comp_log_le_one hlam hR hQone
  have hbase :=
    BoundedGaps.Maynard.abs_maynardS2CoordinateFiberWeightedSum_sub_twoScaleNormalizedLogIntegral_le
      m hr hQ hR hE hG hfDeriv hfDerivInt hfInt hfNormInt hmainInt
        happrox hvariation
  have hx : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQone))
      (Real.log_pos (by exact_mod_cast hR)).le
  have hendNonneg : 0 ≤ inverseAffineProfile lam
      (Real.log Q / Real.log R) := inverseAffineProfile_nonneg hlam hx
  have hendLe : inverseAffineProfile lam
      (Real.log Q / Real.log R) ≤ 1 := inverseAffineProfile_le_one hlam hx
  have hendAbs : |inverseAffineProfile lam
      (Real.log Q / Real.log R)| ≤ 1 := by
    rw [abs_of_nonneg hendNonneg]
    exact hendLe
  have hfactor :
      E * (|inverseAffineProfile lam (Real.log Q / Real.log R)| + 1) ≤
        2 * E := by
    nlinarith
  exact hbase.trans hfactor

def inverseAffineRelativeError (U C : ℝ) (D R : ℕ) : ℝ :=
  22 * (U + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2) / Real.log R

theorem inverseAffineRelativeError_nonneg
    {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    {D R : ℕ} (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R) :
    0 ≤ inverseAffineRelativeError U C D R := by
  unfold inverseAffineRelativeError
  have hlogD : 0 ≤ Real.log D :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

theorem two_inverseAffineAbelEnvelope_eq_relative
    {U C : ℝ} {D R : ℕ} {H : Finset ℕ} (m : H) (r : H → ℕ)
    (hlogR : Real.log R ≠ 0) :
    2 * inverseAffineAbelEnvelope U C D R m r =
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
        Real.log R * inverseAffineRelativeError U C D R := by
  unfold inverseAffineAbelEnvelope inverseAffineRelativeError
  field_simp [hlogR]
  ring

theorem tendsto_inverseAffineRelativeError_zero
    {alpha : ℝ} (halpha : 0 < alpha) (U C : ℝ) :
    Tendsto (fun N : ℕ => inverseAffineRelativeError U C
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  let L : ℕ → ℝ := fun N =>
    Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  have hL : Tendsto L atTop atTop := by
    simpa [L] using
      BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hU : Tendsto (fun N : ℕ => U / L N) atTop (nhds 0) :=
    hL.const_div_atTop U
  have hD : Tendsto (fun N : ℕ => Real.log (D N) / L N)
      atTop (nhds 0) := by
    simpa [D, L] using
      BoundedGaps.Maynard.tendsto_log_tripleLogCutoff_div_logRadius_zero
        halpha
  have hlogL : Tendsto (fun N : ℕ => Real.log (L N) / L N)
      atTop (nhds 0) := by
    simpa using
      (Real.isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have hC : Tendsto (fun N : ℕ => C / L N) atTop (nhds 0) :=
    hL.const_div_atTop C
  have htwo : Tendsto (fun N : ℕ => (2 : ℝ) / L N)
      atTop (nhds 0) := hL.const_div_atTop 2
  have hlog2 : Tendsto (fun N : ℕ => Real.log 2 / L N)
      atTop (nhds 0) := hL.const_div_atTop (Real.log 2)
  have hsum := (((hU.add hD).add ((hlogL.add hC).add htwo)).add hlog2)
  have hratio : Tendsto (fun N : ℕ =>
      (U + Real.log (D N) + (Real.log (L N) + C + 2) + Real.log 2) /
        L N) atTop (nhds 0) := by
    convert hsum using 1
    · funext N
      ring
    · norm_num
  have hscaled := hratio.const_mul (22 : ℝ)
  convert hscaled using 1
  · funext N
    unfold inverseAffineRelativeError
    dsimp [D, L]
    ring
  · norm_num

end

end MaynardTao
