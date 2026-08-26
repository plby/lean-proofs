import ErdosProblems.Erdos1002.ProbabilityFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lévy's continuity theorem on the real line

This file proves the direction needed in the manuscript: pointwise convergence
of characteristic functions of probability measures on `ℝ` to the
characteristic function of a probability measure implies weak convergence.
The proof derives tightness from the standard integrated-characteristic-
function tail bound, applies Prokhorov compactness, and identifies every
cluster point by uniqueness of characteristic functions.
-/

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

theorem continuous_charFun_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (charFun μ) := by
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℂ)) μ := by fun_prop
  have hfourier :
      Continuous (VectorFourier.fourierIntegral Real.probChar μ
        (innerₗ ℝ) 1) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_probChar
      (by fun_prop) hone
  have heq :
      charFun μ =
        (VectorFourier.fourierIntegral Real.probChar μ (innerₗ ℝ) 1) ∘
          (fun t : ℝ ↦ -t) := by
    funext t
    simpa only [Function.comp_apply] using! charFun_eq_fourierIntegral (E := ℝ) (μ := μ) t
  rw [heq]
  exact hfourier.comp continuous_neg

theorem continuous_charFun_probabilityMeasure (t : ℝ) :
    Continuous (fun ρ : ProbabilityMeasure ℝ ↦ charFun (ρ : Measure ℝ) t) := by
  rw [continuous_iff_continuousAt]
  intro ρ
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
      (tendsto_id : Tendsto id (nhds ρ) (nhds ρ))
      (BoundedContinuousFunction.innerProbChar t)
  simpa only [charFun_eq_integral_innerProbChar] using! h

private theorem tendsto_intervalIntegral_one_sub_charFun
    (μSeq : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n ↦ charFun (μSeq n : Measure ℝ) t) atTop
        (nhds (charFun (μ : Measure ℝ) t)))
    (a b : ℝ) :
    Tendsto
      (fun n ↦ ∫ t in a..b, 1 - charFun (μSeq n : Measure ℝ) t)
      atTop
      (nhds (∫ t in a..b, 1 - charFun (μ : Measure ℝ) t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ ↦ 2) ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun _ ↦ by fun_prop
  · exact Filter.Eventually.of_forall fun n ↦
      ae_of_all _ fun _ _ ↦ norm_one_sub_charFun_le_two
  · exact ae_of_all _ fun t _ ↦ tendsto_const_nhds.sub (hchar t)

private theorem eventually_uniform_charFun_tail
    (μSeq : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n ↦ charFun (μSeq n : Measure ℝ) t) atTop
        (nhds (charFun (μ : Measure ℝ) t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n in atTop,
        (μSeq n : Measure ℝ).real {x : ℝ | R < |x|} ≤ ε := by
  have hcont : ContinuousAt (charFun (μ : Measure ℝ)) 0 :=
    (continuous_charFun_measure (μ : Measure ℝ)).continuousAt
  rcases (Metric.continuousAt_iff.mp hcont) (ε / 4) (by positivity) with
    ⟨δ, hδ, hnear⟩
  let d : ℝ := δ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hpoint : ∀ t ∈ Set.uIoc (-d) d,
      ‖1 - charFun (μ : Measure ℝ) t‖ ≤ ε / 4 := by
    intro t ht
    have ht_bounds : -d < t ∧ t ≤ d := by
      simpa [Set.uIoc_of_le (by linarith : -d ≤ d)] using! ht
    have ht_abs : |t| ≤ d := (abs_le).mpr ⟨ht_bounds.1.le, ht_bounds.2⟩
    have ht_dist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      exact ht_abs.trans_lt (by dsimp [d]; linarith)
    have h := hnear ht_dist
    rw [dist_eq_norm] at h
    have h' : ‖charFun (μ : Measure ℝ) t - 1‖ < ε / 4 := by
      simpa only [charFun_zero,
        isProbabilityMeasure_iff_real.mp inferInstance] using! h
    rw [show (1 : ℂ) - charFun (μ : Measure ℝ) t =
      -(charFun (μ : Measure ℝ) t - 1) by ring, norm_neg]
    exact h'.le
  have hlimit_bound :
      ‖∫ t in -d..d, 1 - charFun (μ : Measure ℝ) t‖ ≤ ε * d / 2 := by
    calc
      ‖∫ t in -d..d, 1 - charFun (μ : Measure ℝ) t‖
          ≤ (ε / 4) * |d - (-d)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = ε * d / 2 := by rw [abs_of_pos (by linarith : 0 < d - -d)]; ring
  have hIntegral := tendsto_intervalIntegral_one_sub_charFun μSeq μ hchar (-d) d
  have hlimit_lt :
      ‖∫ t in -d..d, 1 - charFun (μ : Measure ℝ) t‖ < ε * d :=
    hlimit_bound.trans_lt (by nlinarith)
  have heventually :
      ∀ᶠ n in atTop,
        ‖∫ t in -d..d, 1 - charFun (μSeq n : Measure ℝ) t‖ < ε * d :=
    hIntegral.norm.eventually_lt_const hlimit_lt
  let R : ℝ := 2 / d
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  filter_upwards [heventually] with n hn
  have htail := measureReal_abs_gt_le_integral_charFun
    (μ := (μSeq n : Measure ℝ)) hR
  have hscale : 2 * R⁻¹ = d := by
    dsimp [R]
    field_simp
  have hscaleNeg : -2 * R⁻¹ = -d := by linarith
  rw [hscale, hscaleNeg] at htail
  exact htail.trans (le_of_lt <| calc
    2⁻¹ * R * ‖∫ t in -d..d, 1 - charFun (μSeq n : Measure ℝ) t‖
        < 2⁻¹ * R * (ε * d) := mul_lt_mul_of_pos_left hn (by positivity)
    _ = ε := by dsimp [R]; field_simp)

private theorem isTightMeasureSet_probability_prefix
    (μSeq : ℕ → ProbabilityMeasure ℝ) (N : ℕ) :
    IsTightMeasureSet
      {m : Measure ℝ | ∃ n < N, (μSeq n : Measure ℝ) = m} := by
  induction N with
  | zero =>
      apply (isTightMeasureSet_singleton
        (μ := (μSeq 0 : Measure ℝ))).subset
      simp
  | succ N hN =>
      have hset :
          {m : Measure ℝ | ∃ n < N + 1, (μSeq n : Measure ℝ) = m} =
            {m : Measure ℝ | ∃ n < N, (μSeq n : Measure ℝ) = m} ∪
              {(μSeq N : Measure ℝ)} := by
        ext m
        simp only [mem_setOf_eq, mem_union, mem_singleton_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
          · exact Or.inl ⟨n, hn, rfl⟩
          · exact Or.inr rfl
        · rintro (⟨n, hn, rfl⟩ | rfl)
          · exact ⟨n, hn.trans_le (Nat.le_succ N), rfl⟩
          · exact ⟨N, Nat.lt_succ_self N, rfl⟩
      rw [hset]
      exact hN.union (isTightMeasureSet_singleton
        (μ := (μSeq N : Measure ℝ)))

private theorem isTightMeasureSet_range_of_charFun_tendsto
    (μSeq : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n ↦ charFun (μSeq n : Measure ℝ) t) atTop
        (nhds (charFun (μ : Measure ℝ) t))) :
    IsTightMeasureSet
      {m : Measure ℝ | ∃ n : ℕ, (μSeq n : Measure ℝ) = m} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεtop : ε = ∞
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ _hρ
    simp [hεtop]
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨R, hR, htail⟩ :=
    eventually_uniform_charFun_tail μSeq μ hchar hεreal
  rw [eventually_atTop] at htail
  obtain ⟨N, hN⟩ := htail
  have hprefix := isTightMeasureSet_probability_prefix μSeq N
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hprefix
  obtain ⟨Kprefix, hKprefix, hprefix_bound⟩ := hprefix ε hε
  let Ktail : Set ℝ := Metric.closedBall 0 R
  have hKtail : IsCompact Ktail := isCompact_closedBall 0 R
  have hKtail_compl : Ktailᶜ = {x : ℝ | R < |x|} := by
    ext x
    simp only [Ktail, mem_compl_iff, Metric.mem_closedBall, mem_setOf_eq]
    rw [Real.dist_eq, sub_zero]
    exact not_le
  refine ⟨Kprefix ∪ Ktail, hKprefix.union hKtail, ?_⟩
  intro ρ hρ
  rcases hρ with ⟨n, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · calc
      (μSeq n : Measure ℝ) (Kprefix ∪ Ktail)ᶜ
          ≤ (μSeq n : Measure ℝ) Kprefixᶜ := by
            apply measure_mono
            simp
      _ ≤ ε := hprefix_bound _ ⟨n, hn, rfl⟩
  · calc
      (μSeq n : Measure ℝ) (Kprefix ∪ Ktail)ᶜ
          ≤ (μSeq n : Measure ℝ) Ktailᶜ := by
            apply measure_mono
            simp
      _ = (μSeq n : Measure ℝ) {x : ℝ | R < |x|} := by rw [hKtail_compl]
      _ ≤ ε := by
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) hεtop).mp
        simpa only [Measure.real] using! hN n hn

/-- **Lévy continuity theorem on `ℝ` (probability-limit direction).**
Pointwise convergence of the characteristic functions to that of a
probability measure implies weak convergence of the probability measures. -/
theorem levy_continuity_real
    (μSeq : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n ↦ charFun (μSeq n : Measure ℝ) t) atTop
        (nhds (charFun (μ : Measure ℝ) t))) :
    Tendsto μSeq atTop (nhds μ) := by
  let S : Set (ProbabilityMeasure ℝ) := Set.range μSeq
  have htight :
      IsTightMeasureSet
        {m : Measure ℝ | ∃ ρ ∈ S, (ρ : Measure ℝ) = m} := by
    simpa only [S, mem_range, exists_exists_eq_and] using!
      isTightMeasureSet_range_of_charFun_tendsto μSeq μ hchar
  have hcompact : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet htight
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
  · exact Filter.Eventually.of_forall fun n ↦
      subset_closure (mem_range_self n)
  · intro ν _hν hcluster
    obtain ⟨ψ, hψmono, hψlim⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
    have hchar_eq :
        charFun (ν : Measure ℝ) = charFun (μ : Measure ℝ) := by
      funext t
      have htoν :
          Tendsto (fun k ↦ charFun (μSeq (ψ k) : Measure ℝ) t) atTop
            (nhds (charFun (ν : Measure ℝ) t)) := by
        have hc :
            Tendsto (fun ρ : ProbabilityMeasure ℝ ↦
              charFun (ρ : Measure ℝ) t) (nhds ν)
              (nhds (charFun (ν : Measure ℝ) t)) :=
          (continuous_charFun_probabilityMeasure t).continuousAt
        have h := hc.comp hψlim
        simpa only [Function.comp_apply] using! h
      have htoμ :
          Tendsto (fun k ↦ charFun (μSeq (ψ k) : Measure ℝ) t) atTop
            (nhds (charFun (μ : Measure ℝ) t)) :=
        (hchar t).comp hψmono.tendsto_atTop
      exact tendsto_nhds_unique htoν htoμ
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.ext_of_charFun hchar_eq

end

end Erdos1002
