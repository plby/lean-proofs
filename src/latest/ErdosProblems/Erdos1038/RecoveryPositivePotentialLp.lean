import ErdosProblems.Erdos1038.RecoverySublevel
import ErdosProblems.Erdos1038.RecoveryPositivePlatform

/-!
# Pointwise representatives for positive-platform recovery potentials

The weak-convergence API represents logarithmic potentials as elements of
`L¹`.  This file proves, by Fubini, that this element agrees almost
everywhere with the ordinary pointwise integral against any supported root
probability.  It then specializes the bridge to the positive-buffer family
and transfers zero-set and negative-set volumes to `positiveBufferPotential`.
-/

open scoped ENNReal Real BigOperators Polynomial
open Filter MeasureTheory Set Polynomial Topology

namespace Erdos1038

noncomputable section

/-- The ordinary pointwise logarithmic potential of a probability measure. -/
def logarithmicPotentialPointwise (P : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ∫ t, logKernel t x ∂(P : Measure ℝ)

/-- The logarithmic kernel is jointly integrable against a supported root
probability and Lebesgue measure on any bounded observation interval. -/
theorem integrable_logKernel_prod_supported
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun z : ℝ × ℝ ↦ logKernel z.1 z.2)
      ((P : Measure ℝ).prod (volume.restrict (Icc a b))) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ logKernel z.1 z.2)
      ((P : Measure ℝ).prod (volume.restrict (Icc a b))) := by
    apply Measurable.aestronglyMeasurable
    unfold logKernel
    fun_prop
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with t
    exact integrableOn_logKernel_Icc hab
  · have hnorm (t : ℝ) :
        (∫ x, ‖logKernel t x‖ ∂volume.restrict (Icc a b)) =
          ‖logKernelLp a b t hab‖ := by
      symm
      exact L1.norm_of_fun_eq_integral_norm (integrableOn_logKernel_Icc hab)
    simp_rw [hnorm]
    have hstrong : AEStronglyMeasurable
        (fun t : ℝ ↦ ‖logKernelLp a b t hab‖) (P : Measure ℝ) :=
      (continuous_logKernelLp hab).norm.measurable.aestronglyMeasurable
    refine Integrable.mono' (integrable_const
      ‖logKernelRootIntervalBCF a b hab‖) hstrong ?_
    have hsupp : ∀ᵐ t ∂(P : Measure ℝ), t ∈ RootInterval :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP
    filter_upwards [hsupp] with t ht
    simpa only [norm_norm] using!
      (logKernelRootIntervalBCF a b hab).norm_coe_le_norm ⟨t, ht⟩

/-- The `L¹`-valued logarithmic kernel is integrable against every supported
root probability. -/
theorem integrable_logKernelLp_supported
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun t ↦ logKernelLp a b t hab) (P : Measure ℝ) := by
  have hstrong : AEStronglyMeasurable
      (fun t : ℝ ↦ logKernelLp a b t hab) (P : Measure ℝ) :=
    (continuous_logKernelLp hab).aestronglyMeasurable
  refine Integrable.mono' (integrable_const
    ‖logKernelRootIntervalBCF a b hab‖) hstrong ?_
  have hsupp : ∀ᵐ t ∂(P : Measure ℝ), t ∈ RootInterval :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP
  filter_upwards [hsupp] with t ht
  exact (logKernelRootIntervalBCF a b hab).norm_coe_le_norm ⟨t, ht⟩

/-- Fubini identifies the `L¹` logarithmic potential with the ordinary
pointwise integral almost everywhere on the observation interval. -/
theorem logarithmicPotentialLp_ae_eq_pointwise
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P)
    {a b : ℝ} (hab : a ≤ b) :
    logarithmicPotentialLp a b hab P hP =ᵐ[volume.restrict (Icc a b)]
      logarithmicPotentialPointwise P := by
  let mu : Measure ℝ := volume.restrict (Icc a b)
  let v : ℝ → ℝ := fun x ↦ logarithmicPotentialLp a b hab P hP x
  let w : ℝ → ℝ := logarithmicPotentialPointwise P
  have hprod := integrable_logKernel_prod_supported P hP hab
  have hv : Integrable v mu := L1.integrable_coeFn _
  have hw : Integrable w mu := by
    simpa only [w, logarithmicPotentialPointwise, logKernel, mu] using!
      hprod.integral_prod_right
  apply Integrable.ae_eq_of_forall_setIntegral_eq v w hv hw
  intro S hS hSfinite
  let T : Lp ℝ 1 mu →L[ℝ] ℝ := ContinuousLinearMap.mk
    { toFun := fun u ↦ ∫ x in S, u x ∂mu
      map_add' := fun u z ↦ by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add u z))]
        change (∫ x in S, (u x + z x) ∂mu) =
          (∫ x in S, u x ∂mu) + ∫ x in S, z x ∂mu
        rw [integral_add (L1.integrable_coeFn u).integrableOn
          (L1.integrable_coeFn z).integrableOn]
      map_smul' := fun c u ↦ by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c u))]
        change (∫ x in S, c * u x ∂mu) = c * ∫ x in S, u x ∂mu
        rw [integral_const_mul] }
    (continuous_setIntegral S)
  have hK := integrable_logKernelLp_supported P hP hab
  change T (logarithmicPotentialLp a b hab P hP) =
    ∫ x in S, w x ∂mu
  rw [logarithmicPotentialLp_eq_integral]
  rw [← T.integral_comp_comm hK]
  change (∫ t, ∫ x in S, logKernelLp a b t hab x ∂mu ∂(P : Measure ℝ)) =
    ∫ x in S, w x ∂mu
  have hinner (t : ℝ) :
      (∫ x in S, logKernelLp a b t hab x ∂mu) =
        ∫ x in S, logKernel t x ∂mu := by
    exact integral_congr_ae (ae_restrict_of_ae (logKernelLp_coeFn hab))
  simp_rw [hinner]
  have hprodS : Integrable (fun z : ℝ × ℝ ↦ logKernel z.1 z.2)
      ((P : Measure ℝ).prod (mu.restrict S)) := by
    have h : IntegrableOn (fun z : ℝ × ℝ ↦ logKernel z.1 z.2)
        (univ ×ˢ S) ((P : Measure ℝ).prod mu) := hprod.integrableOn
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  simpa only [w, logarithmicPotentialPointwise] using!
    (integral_integral_swap hprodS)

/-- The general pointwise-representative bridge specialized to the
positive-buffer probability. -/
theorem logarithmicPotentialLp_positiveBuffer_ae
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    {a b : ℝ} (hab : a ≤ b) :
    logarithmicPotentialLp a b hab
        (positiveBufferProbability s alpha hs hs1 halpha halphas)
        (positiveBufferProbability_supported hs hs1 halpha halphas)
      =ᵐ[volume.restrict (Icc a b)] positiveBufferPotential s alpha := by
  have h := logarithmicPotentialLp_ae_eq_pointwise
    (positiveBufferProbability s alpha hs hs1 halpha halphas)
    (positiveBufferProbability_supported hs hs1 halpha halphas) hab
  simpa only [logarithmicPotentialPointwise, logKernel,
    positiveBufferProbability, positiveBufferPotential] using! h

/-- On its continuous support, the `L¹` representative is almost everywhere
equal to the explicit positive-platform constant. -/
theorem logarithmicPotentialLp_positiveBuffer_ae_eq_platformValue_on_support
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    logarithmicPotentialLp (positiveBufferDistanceLeft s - 1) 1 (by
        have := positiveBufferDistanceLeft_lt_two hs hs1
        linarith)
        (positiveBufferProbability s alpha hs hs1 halpha halphas)
        (positiveBufferProbability_supported hs hs1 halpha halphas)
      =ᵐ[volume.restrict (Icc (positiveBufferDistanceLeft s - 1) 1)]
        fun _ ↦ (1 - alpha) *
            Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
          alpha * Real.log (platformD0 (positiveBufferDistanceLeft s)) := by
  have hae := logarithmicPotentialLp_positiveBuffer_ae
    hs hs1 halpha halphas (a := positiveBufferDistanceLeft s - 1) (b := 1) (by
      have := positiveBufferDistanceLeft_lt_two hs hs1
      linarith)
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [hx, positiveBufferPotential_eq_platformValue hs hs1 halpha halphas hmem]

/-- An almost-everywhere equality on a restricted interval preserves the
Lebesgue measure of every pointwise predicate inside that interval. -/
theorem volume_setOn_Icc_congr_of_ae_eq
    {a b : ℝ} {u v : ℝ → ℝ}
    (huv : u =ᵐ[volume.restrict (Icc a b)] v) (R : ℝ → Prop) :
    volume {x | x ∈ Icc a b ∧ R (u x)} =
      volume {x | x ∈ Icc a b ∧ R (v x)} := by
  apply measure_congr
  have huv' := (ae_restrict_iff' measurableSet_Icc).mp huv
  filter_upwards [huv'] with x hx
  change (x ∈ Icc a b ∧ R (u x)) = (x ∈ Icc a b ∧ R (v x))
  by_cases hmem : x ∈ Icc a b
  · simp only [hmem, true_and]
    exact propext (by rw [hx hmem])
  · simp only [hmem, false_and]

/-- The zero-set volume of the positive-buffer `L¹` representative is the
zero-set volume of its pointwise potential. -/
theorem volume_logarithmicPotentialLp_positiveBuffer_zeroSet_eq
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num)
          (positiveBufferProbability s alpha hs hs1 halpha halphas)
          (positiveBufferProbability_supported hs hs1 halpha halphas) x = 0} =
      volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential s alpha x = 0} := by
  exact volume_setOn_Icc_congr_of_ae_eq
    (logarithmicPotentialLp_positiveBuffer_ae hs hs1 halpha halphas
      (a := -2) (b := 2) (by norm_num)) (· = 0)

/-- The negative-set volume of the positive-buffer `L¹` representative is
the negative-set volume of its pointwise potential. -/
theorem volume_logarithmicPotentialLp_positiveBuffer_negativeSet_eq
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num)
          (positiveBufferProbability s alpha hs hs1 halpha halphas)
          (positiveBufferProbability_supported hs hs1 halpha halphas) x < 0} =
      volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential s alpha x < 0} := by
  exact volume_setOn_Icc_congr_of_ae_eq
    (logarithmicPotentialLp_positiveBuffer_ae hs hs1 halpha halphas
      (a := -2) (b := 2) (by norm_num)) (· < 0)

/-- Once the pointwise positive-buffer zero level is null, empirical
polynomials recover its pointwise negative-set volume. -/
theorem exists_admissiblePolynomials_sublevelVolume_tendsto_positiveBuffer
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential s alpha x = 0} = 0) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
          positiveBufferPotential s alpha x < 0})) := by
  have hzeroLp : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num)
        (positiveBufferProbability s alpha hs hs1 halpha halphas)
        (positiveBufferProbability_supported hs hs1 halpha halphas) x = 0} = 0 := by
    rw [volume_logarithmicPotentialLp_positiveBuffer_zeroSet_eq
      hs hs1 halpha halphas, hzero]
  have h := exists_admissiblePolynomials_sublevelVolume_tendsto
    (positiveBufferProbability s alpha hs hs1 halpha halphas)
    (positiveBufferProbability_supported hs hs1 halpha halphas) hzeroLp
  simpa only [volume_logarithmicPotentialLp_positiveBuffer_negativeSet_eq
    hs hs1 halpha halphas] using! h

/-- Target-value form of positive-buffer polynomial recovery. -/
theorem exists_admissiblePolynomials_sublevelVolume_tendsto_positiveBuffer_of_eq
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential s alpha x = 0} = 0)
    {V : ℝ≥0∞}
    (hvolume : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential s alpha x < 0} = V) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 V) := by
  simpa only [hvolume] using!
    exists_admissiblePolynomials_sublevelVolume_tendsto_positiveBuffer
      hs hs1 halpha halphas hzero

end

end Erdos1038
