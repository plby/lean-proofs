import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak convergence under a vanishing perturbation

Mathlib's converging-together lemma is phrased with a limiting random
variable on the original probability space.  The manuscript naturally
constructs the limiting Cauchy *measure* instead.  The theorem below proves
the corresponding law-level statement directly, using the same bounded
Lipschitz argument and retaining the convergence-in-probability hypothesis.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

variable {Ω ι E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [MeasurableSpace E]
  [SeminormedAddCommGroup E]
  [SecondCountableTopology E] [BorelSpace E]
  [OpensMeasurableSpace E]
  {l : Filter ι} [l.IsCountablyGenerated]

local instance probabilityMeasureWeakTopology :
    TopologicalSpace (ProbabilityMeasure E) :=
  ProbabilityMeasure.instTopologicalSpace

/-- If the laws of `X i` converge weakly to `ν` and `Y i - X i`
converges to zero in probability, then the laws of `Y i` also converge
weakly to `ν`. -/
theorem tendsto_map_of_tendsto_map_of_tendstoInMeasure_sub
    (X Y : ι → Ω → E) (ν : ProbabilityMeasure E)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (hXν : Tendsto
      (fun i ↦ (⟨μ.map (X i), Measure.isProbabilityMeasure_map (hX i)⟩ :
        ProbabilityMeasure E)) l
          (@nhds (ProbabilityMeasure E) probabilityMeasureWeakTopology ν))
    (hXY : TendstoInMeasure μ (Y - X) l 0) :
    Tendsto
      (fun i ↦ (⟨μ.map (Y i), Measure.isProbabilityMeasure_map (hY i)⟩ :
        ProbabilityMeasure E)) l
          (@nhds (ProbabilityMeasure E) probabilityMeasureWeakTopology ν) := by
  let x₀ : E := 0
  suffices ∀ (F : E → ℝ)
      (hF_bounded : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun i ↦ ∫ x, F x ∂(μ.map (Y i))) l
        (nhds (∫ x, F x ∂(ν : Measure E))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have hProbY i : IsProbabilityMeasure (μ.map (Y i)) :=
      Measure.isProbabilityMeasure_map (hY i)
    have hProbν : IsProbabilityMeasure (ν : Measure E) := inferInstance
    simpa using! tendsto_const_nhds
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ i in l,
      |∫ x, F x ∂(μ.map (Y i)) - ∫ x, F x ∂(ν : Measure E)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le i :
      |∫ x, F x ∂(μ.map (Y i)) - ∫ x, F x ∂(ν : Measure E)| ≤
        L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y i ω - X i ω‖} +
          |∫ x, F x ∂(μ.map (X i)) - ∫ x, F x ∂(ν : Measure E)| := by
    refine (abs_sub_le (∫ x, F x ∂(μ.map (Y i)))
      (∫ x, F x ∂(μ.map (X i))) (∫ x, F x ∂(ν : Measure E))).trans ?_
    gcongr
    have hIntY : Integrable (fun x ↦ F (Y i x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M)
        (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y i a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y i a)) (F x₀)).trans hF_bounded
    have hIntX : Integrable (fun x ↦ F (X i x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M)
        (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X i a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X i a)) (F x₀)).trans hF_bounded
    have hIntSub : Integrable (fun a ↦ ‖F (Y i a) - F (X i a)‖) μ := by
      rw [integrable_norm_iff (by fun_prop)]
      exact hIntY.sub hIntX
    rw [integral_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop),
      ← integral_sub hIntY hIntX, ← Real.norm_eq_abs]
    calc
      ‖∫ a, F (Y i a) - F (X i a) ∂μ‖
          ≤ ∫ a, ‖F (Y i a) - F (X i a)‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ a in {x | ‖Y i x - X i x‖ < ε / 2},
            ‖F (Y i a) - F (X i a)‖ ∂μ +
          ∫ a in {x | ε / 2 ≤ ‖Y i x - X i x‖},
            ‖F (Y i a) - F (X i a)‖ ∂μ := by
        symm
        simp_rw [← not_lt]
        refine integral_add_compl₀ ?_ hIntSub
        exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
      _ ≤ ∫ _a in {x | ‖Y i x - X i x‖ < ε / 2}, L * (ε / 2) ∂μ +
          ∫ _a in {x | ε / 2 ≤ ‖Y i x - X i x‖}, M ∂μ := by
        gcongr ?_ + ?_
        · refine setIntegral_mono_on₀ hIntSub.integrableOn integrableOn_const ?_ ?_
          · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
          · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
        · refine setIntegral_mono hIntSub.integrableOn integrableOn_const fun a ↦ ?_
          rw [← dist_eq_norm]
          convert! hF_bounded _ _
      _ = L * (ε / 2) * μ.real {x | ‖Y i x - X i x‖ < ε / 2} +
          M * μ.real {ω | ε / 2 ≤ ‖Y i ω - X i ω‖} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
          Set.univ_inter, smul_eq_mul]
        ring
      _ ≤ L * (ε / 2) +
          M * μ.real {ω | ε / 2 ≤ ‖Y i ω - X i ω‖} := by
        rw [mul_assoc]
        gcongr
        grw [measureReal_le_one, mul_one]
  have hTendsto :
      Tendsto
        (fun i ↦ L * (ε / 2) +
          M * μ.real {ω | ε / 2 ≤ ‖Y i ω - X i ω‖} +
          |∫ x, F x ∂(μ.map (X i)) - ∫ x, F x ∂(ν : Measure E)|)
        l (nhds (L * ε / 2)) := by
    suffices Tendsto
        (fun i ↦ L * (ε / 2) +
          M * μ.real {ω | ε / 2 ≤ ‖Y i ω - X i ω‖} +
          |∫ x, F x ∂(μ.map (X i)) - ∫ x, F x ∂(ν : Measure E)|)
        l (nhds (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · have hWeak := hXν
      rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hWeak
      simpa [tendsto_iff_dist_tendsto_zero] using!
        hWeak F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hlt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [hTendsto.eventually_lt_const hlt] with i hi using
    (h_le i).trans_lt hi

end

end Erdos1002
