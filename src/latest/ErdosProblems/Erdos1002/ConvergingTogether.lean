import ErdosProblems.Erdos1002.WeakPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A two-parameter converging-together theorem

This is the form used in the last paragraph of the manuscript.  The inner
approximants converge for each fixed cutoff; their limiting laws converge as
the cutoff grows; and the original variables are uniformly close in
probability after first taking the sample-size limit.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [MeasurableSpace E]
  [SeminormedAddCommGroup E] [SecondCountableTopology E]
  [BorelSpace E] [OpensMeasurableSpace E]

local instance probabilityMeasureWeakTopologyCT :
    TopologicalSpace (ProbabilityMeasure E) :=
  ProbabilityMeasure.instTopologicalSpace

private theorem boundedLipschitz_map_integral_sub_le
    (U V : Ω → E) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (F : E → ℝ) (M : ℝ) (L : NNReal)
    (hF_bounded : ∀ x y, dist (F x) (F y) ≤ M)
    (hF_lip : LipschitzWith L F) {r : ℝ} (hr : 0 < r) :
    |∫ x, F x ∂(μ.map U) - ∫ x, F x ∂(μ.map V)| ≤
      (L : ℝ) * r + M * μ.real {ω | r ≤ ‖U ω - V ω‖} := by
  let x₀ : E := 0
  have hF_cont : Continuous F := hF_lip.continuous
  have hIntU : Integrable (fun x ↦ F (U x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M)
      (ae_of_all _ fun a ↦ ?_)
    specialize hF_bounded (U a) x₀
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (U a)) (F x₀)).trans hF_bounded
  have hIntV : Integrable (fun x ↦ F (V x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M)
      (ae_of_all _ fun a ↦ ?_)
    specialize hF_bounded (V a) x₀
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (V a)) (F x₀)).trans hF_bounded
  have hIntNorm : Integrable (fun a ↦ ‖F (U a) - F (V a)‖) μ := by
    rw [integrable_norm_iff (by fun_prop)]
    exact hIntU.sub hIntV
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop),
    ← integral_sub hIntU hIntV, ← Real.norm_eq_abs]
  calc
    ‖∫ a, F (U a) - F (V a) ∂μ‖
        ≤ ∫ a, ‖F (U a) - F (V a)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖U x - V x‖ < r}, ‖F (U a) - F (V a)‖ ∂μ +
        ∫ a in {x | r ≤ ‖U x - V x‖}, ‖F (U a) - F (V a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ hIntNorm
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    _ ≤ ∫ _a in {x | ‖U x - V x‖ < r}, (L : ℝ) * r ∂μ +
        ∫ _a in {x | r ≤ ‖U x - V x‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ hIntNorm.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono hIntNorm.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        exact hF_bounded _ _
    _ = (L : ℝ) * r * μ.real {x | ‖U x - V x‖ < r} +
        M * μ.real {x | r ≤ ‖U x - V x‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ (L : ℝ) * r + M * μ.real {x | r ≤ ‖U x - V x‖} := by
      have hmain :
        (L : ℝ) * r * μ.real {x | ‖U x - V x‖ < r} ≤
            (L : ℝ) * r := by
        calc
          (L : ℝ) * r * μ.real {x | ‖U x - V x‖ < r} ≤
              (L : ℝ) * r * 1 := by
            exact mul_le_mul_of_nonneg_left measureReal_le_one
              (mul_nonneg (by positivity) hr.le)
          _ = (L : ℝ) * r := by ring
      linarith

/-- Billingsley's converging-together theorem, with the order of the two
limits encoded by nested `Eventually` quantifiers. -/
theorem tendsto_map_of_convergingTogether
    (X : ℕ → Ω → E) (XA : ℕ → ℕ → Ω → E)
    (νA : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hX : ∀ N, AEMeasurable (X N) μ)
    (hXA : ∀ A N, AEMeasurable (XA A N) μ)
    (hfixed : ∀ A,
      Tendsto
        (fun N ↦ (⟨μ.map (XA A N), Measure.isProbabilityMeasure_map (hXA A N)⟩ :
          ProbabilityMeasure E)) atTop
        (@nhds (ProbabilityMeasure E) probabilityMeasureWeakTopologyCT (νA A)))
    (hlimit : Tendsto νA atTop
      (@nhds (ProbabilityMeasure E) probabilityMeasureWeakTopologyCT ν))
    (hclose : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A in atTop, ∀ᶠ N in atTop,
        μ.real {ω | r ≤ ‖X N ω - XA A N ω‖} < δ) :
    Tendsto
      (fun N ↦ (⟨μ.map (X N), Measure.isProbabilityMeasure_map (hX N)⟩ :
        ProbabilityMeasure E)) atTop
      (@nhds (ProbabilityMeasure E) probabilityMeasureWeakTopologyCT ν) := by
  suffices ∀ (F : E → ℝ)
      (hF_bounded : ∃ M : ℝ, ∀ x y, dist (F x) (F y) ≤ M)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun N ↦ ∫ x, F x ∂(μ.map (X N))) atTop
        (nhds (∫ x, F x ∂(ν : Measure E))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hMbound⟩ ⟨L, hLlip⟩
  have hM : 0 ≤ M := by
    have := hMbound (0 : E) 0
    simpa using! this
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r : ℝ := ε / (4 * ((L : ℝ) + 1))
  let δ : ℝ := ε / (4 * (M + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcloseA := hclose r hr δ hδ
  have hνInt := hlimit
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hνInt
  have hνEvent : ∀ᶠ A in atTop,
      |∫ x, F x ∂(νA A : Measure E) - ∫ x, F x ∂(ν : Measure E)| < ε / 4 := by
    have ht := hνInt F ⟨M, hMbound⟩ ⟨L, hLlip⟩
    rw [Metric.tendsto_nhds] at ht
    simpa [Real.dist_eq] using! ht (ε / 4) (by positivity)
  obtain ⟨A, hcloseN, hνA⟩ := (hcloseA.and hνEvent).exists
  have hfixedInt := hfixed A
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hfixedInt
  have hfixedEvent : ∀ᶠ N in atTop,
      |∫ x, F x ∂(μ.map (XA A N)) - ∫ x, F x ∂(νA A : Measure E)| < ε / 4 := by
    have ht := hfixedInt F ⟨M, hMbound⟩ ⟨L, hLlip⟩
    rw [Metric.tendsto_nhds] at ht
    simpa [Real.dist_eq] using! ht (ε / 4) (by positivity)
  filter_upwards [hcloseN, hfixedEvent] with N hprob happroxLaw
  rw [Real.dist_eq]
  have hmap := boundedLipschitz_map_integral_sub_le
    (X N) (XA A N) (hX N) (hXA A N) F M L hMbound hLlip hr
  have hsmallL : (L : ℝ) * r ≤ ε / 4 := by
    dsimp [r]
    rw [show (L : ℝ) * (ε / (4 * ((L : ℝ) + 1))) =
        ((L : ℝ) * ε) / (4 * ((L : ℝ) + 1)) by ring]
    rw [div_le_iff₀ (by positivity : 0 < 4 * ((L : ℝ) + 1))]
    nlinarith
  have hsmallM : M * δ ≤ ε / 4 := by
    dsimp [δ]
    rw [show M * (ε / (4 * (M + 1))) =
        (M * ε) / (4 * (M + 1)) by ring]
    rw [div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    nlinarith
  have hmapδ :
      |∫ x, F x ∂(μ.map (X N)) - ∫ x, F x ∂(μ.map (XA A N))| ≤
        (L : ℝ) * r + M * δ := by
    have hmul := mul_le_mul_of_nonneg_left hprob.le hM
    nlinarith
  calc
    |∫ x, F x ∂(μ.map (X N)) - ∫ x, F x ∂(ν : Measure E)| ≤
        |∫ x, F x ∂(μ.map (X N)) - ∫ x, F x ∂(μ.map (XA A N))| +
        |∫ x, F x ∂(μ.map (XA A N)) - ∫ x, F x ∂(νA A : Measure E)| +
        |∫ x, F x ∂(νA A : Measure E) - ∫ x, F x ∂(ν : Measure E)| := by
      have h₁ := abs_sub_le
        (∫ x, F x ∂(μ.map (X N)))
        (∫ x, F x ∂(μ.map (XA A N)))
        (∫ x, F x ∂(ν : Measure E))
      have h₂ := abs_sub_le
        (∫ x, F x ∂(μ.map (XA A N)))
        (∫ x, F x ∂(νA A : Measure E))
        (∫ x, F x ∂(ν : Measure E))
      nlinarith
    _ < ((L : ℝ) * r + M * δ) + ε / 4 + ε / 4 := by
      nlinarith
    _ ≤ ε := by linarith

end

end Erdos1002
