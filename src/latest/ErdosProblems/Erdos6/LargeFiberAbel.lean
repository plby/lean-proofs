import ErdosProblems.Erdos6.LargeFiberProfile

/-!
# Abel summation for the large-candidate coordinate fiber

This is the analytic one-dimensional estimate used in the lower bound for the
distinguished-coordinate `S₂` diagonal.  Its error constants are uniform in
the tuple, the distinguished coordinate, and the outer divisor tuple.
-/

namespace Erdos6.Maynard

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval

noncomputable section

def largeFiberAbelEnvelope (K C : ℝ) (D R : ℕ)
    {H : Finset ℕ} (m : H) (r : H → ℕ) : ℝ :=
  11 * BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
    (K + Real.log D + (Real.log (Real.log R) + C + 2) + Real.log 2)

theorem largeFiberAbelEnvelope_nonneg
    {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    {D R : ℕ} (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    {H : Finset ℕ} (m : H) (r : H → ℕ)
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R
      (primorial D) r) :
    0 ≤ largeFiberAbelEnvelope K C D R m r := by
  have hS : 0 ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r :=
    (BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_pos
      m r hr).le
  have hlogD : 0 ≤ Real.log D :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold largeFiberAbelEnvelope
  positivity

theorem exists_uniform_largeFiberAbel_bound :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple H R
            (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) →
        |(∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
              H R (primorial D) m r,
            ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
              largeFiberProfile (Real.log u / Real.log R)) -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R *
            (∫ x in (0 : ℝ)..
              (Real.log
                  (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
                    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) /
                Real.log R), largeFiberProfile x)| ≤
          2 * largeFiberAbelEnvelope K C D R m r := by
  obtain ⟨K, C, hK, hC, hcum⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_logarithmic
  refine ⟨K, C, hK, hC, ?_⟩
  intro H D R m r hr hD hlogR hQ
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let E := largeFiberAbelEnvelope K C D R m r
  have hR : 1 < R := by
    by_contra hnot
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast (le_of_not_gt hnot)
    have hlogNonpos : Real.log R ≤ 0 :=
      Real.log_nonpos (by positivity) hRle
    linarith
  have hE : 0 ≤ E :=
    largeFiberAbelEnvelope_nonneg hK hC hD hlogR m r hr
  have hQone : 1 ≤ Q := by omega
  have hG : Continuous largeFiberProfile := continuous_largeFiberProfile
  have hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt
        (fun t => largeFiberProfile (Real.log t / Real.log R))
        (deriv (fun t => largeFiberProfile
          (Real.log t / Real.log R)) x) x := by
    intro x hx
    exact (hasDerivAt_largeFiberProfile_comp_log hR hx.1).differentiableAt.hasDerivAt
  have hfDerivInt : IntervalIntegrable
      (deriv (fun t : ℝ => largeFiberProfile
        (Real.log t / Real.log R))) volume 1 Q :=
    intervalIntegrable_deriv_largeFiber_comp_log hR hQone
  have hfInt : IntegrableOn
      (deriv (fun t : ℝ => largeFiberProfile
        (Real.log t / Real.log R))) (Set.Icc (1 : ℝ) Q) :=
    integrableOn_deriv_largeFiber_comp_log_Icc hR
  have hfNormInt : IntegrableOn
      (fun t => |deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R)) t|) (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_abs_deriv_largeFiber_comp_log_Ioc hR
  have hmainInt : IntegrableOn
      (fun t => deriv (fun z : ℝ => largeFiberProfile
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_deriv_mul_log_largeFiber_comp_log S hR
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |BoundedGaps.Maynard.abelCumulative
          (BoundedGaps.Maynard.maynardS2CoordinateFiberCoefficient
            H (primorial D) m r) t -
        S * Real.log t| ≤ E := by
    intro t ht
    exact hcum m r hr hlogR ht.1
  have hvariation :
      (∫ t in Set.Ioc (1 : ℝ) Q,
        |deriv (fun z : ℝ => largeFiberProfile
          (Real.log z / Real.log R)) t|) ≤ 1 :=
    integral_abs_deriv_largeFiber_comp_log_le_one hR hQone
  have hbase :=
    BoundedGaps.Maynard.abs_maynardS2CoordinateFiberWeightedSum_sub_twoScaleNormalizedLogIntegral_le
      m hr hQ hR hE hG hfDeriv hfDerivInt hfInt hfNormInt hmainInt
        happrox hvariation
  have hx : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQone))
      (Real.log_pos (by exact_mod_cast hR)).le
  have hendNonneg : 0 ≤ largeFiberProfile
      (Real.log Q / Real.log R) := largeFiberProfile_nonneg hx
  have hendLe : largeFiberProfile
      (Real.log Q / Real.log R) ≤ 1 := largeFiberProfile_le_one hx
  have hendAbs : |largeFiberProfile
      (Real.log Q / Real.log R)| ≤ 1 := by
    rw [abs_of_nonneg hendNonneg]
    exact hendLe
  have hfactor :
      E * (|largeFiberProfile (Real.log Q / Real.log R)| + 1) ≤
        2 * E := by
    nlinarith
  exact hbase.trans hfactor

end

end Erdos6.Maynard
