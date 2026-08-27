import ErdosProblems.Erdos4.FGKMTRoundBounds

/-! The expected selected hit count is close to its deterministic model degree. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def testDegree (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (T : Finset V) : ℝ := ∑ v ∈ T, vertexDegree μ v / p v

theorem testDegree_nonneg (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (T : Finset V) : 0 ≤ testDegree μ p T :=
  Finset.sum_nonneg (fun v _hv => div_nonneg (vertexDegree_nonneg μ v) (hp v).le)

theorem testDegree_le {μ : I → FiniteLaw (Finset V)} {p : V → ℝ}
    {r A : ℕ} {κ δ D : ℝ} (h : RoundBounds μ p r κ δ D)
    (T : Finset V) (hT : T.card ≤ A) : testDegree μ p T ≤ (A : ℝ) * D := by
  calc
    _ ≤ ∑ _v ∈ T, D := Finset.sum_le_sum (fun v _hv => h.vertex_degree v)
    _ = (T.card : ℝ) * D := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) h.degree_nonneg

theorem conditioned_raw_total_error (ν : FiniteLaw (Finset V))
    {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r A : ℕ} {κ δ ε D : ℝ}
    (h : RoundBounds μ p r κ δ D) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A)
    (T : Finset V) (hT : T.card ≤ A) :
    (conditionSurvival ν T).mean
      (fun W => |(∑ v ∈ T, rawDegree μ p W v) - testDegree μ p T|) ≤
        (A : ℝ) * (2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A) := by
  calc
    _ ≤ (conditionSurvival ν T).mean
        (fun W => ∑ v ∈ T, |rawDegree μ p W v - vertexDegree μ v / p v|) := by
      apply (conditionSurvival ν T).mean_mono
      intro W
      rw [testDegree, ← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ T, (conditionSurvival ν T).mean
        (fun W => |rawDegree μ p W v - vertexDegree μ v / p v|) :=
      FiniteLaw.mean_finset_sum _ _ _
    _ ≤ ∑ _v ∈ T, 2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A := by
      apply Finset.sum_le_sum
      intro v hv
      exact conditioned_degree_error ν μ p h.kappa_pos h.kappa_le_one h.delta_nonneg hε0 hε1
        h.degree_nonneg h.model_lower h.edge_size hacc hrA T hT v hv (h.vertex_degree v)
        (fun w hw => h.pair_degree v w (Ne.symm hw))
    _ = (T.card : ℝ) * (2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (by have := h.kappa_pos; positivity)

theorem conditioned_normalization_error (ν : FiniteLaw (Finset V))
    {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r A : ℕ} {κ δ ε t D : ℝ}
    (h : RoundBounds μ p r κ δ D) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A)
    (T : Finset V) (hT : T.card ≤ A) :
    (conditionSurvival ν T).mean (fun W => ∑ i,
      |(selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e) -
        eventNumerator (μ i) p W (fun e => ¬Disjoint T e)|) ≤
      2 * (normalizationError r κ δ ε t * (A : ℝ) * D / κ ^ r) / κ ^ A := by
  have hK := normalizationError_nonneg r h.kappa_pos h.delta_nonneg hε0 ht0.le
  apply conditioned_error_le ν p h.kappa_pos h.kappa_le_one hε1 h.model_lower hacc T hT _
    (fun W => Finset.sum_nonneg (fun i _hi => abs_nonneg _))
  have hh := aggregate_normalization_error ν μ p h.kappa_pos h.kappa_le_one h.delta_nonneg hε0
    ht0 ht1 h.degree_nonneg h.model_lower h.model_upper h.edge_size h.sparse h.vertex_degree
    (fun e he => hacc e (he.trans hrA)) T
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (pow_pos h.kappa_pos r).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hT) hK) h.degree_nonneg

theorem selected_total_mean_error (ν : FiniteLaw (Finset V))
    {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r A : ℕ} {κ δ ε t D : ℝ}
    (h : RoundBounds μ p r κ δ D) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A)
    (T : Finset V) (hT : T.card ≤ A) :
    (conditionSurvival ν T).mean (fun W =>
      |(∑ i, (selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e)) -
        testDegree μ p T|) ≤ roundMeanLoss r A κ δ ε t D := by
  have hnorm := conditioned_normalization_error ν h hε0 hε1 ht0 ht1 hacc hrA T hT
  have hraw := conditioned_raw_total_error ν h hε0 hε1 hacc hrA T hT
  have hover (W : Finset V) :
      |(∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e)) -
        ∑ v ∈ T, rawDegree μ p W v| ≤ (A : ℝ) ^ 2 * δ / κ ^ r := by
    rw [abs_sub_comm]
    apply (aggregate_raw_union_error μ p h.kappa_pos h.kappa_le_one h.delta_nonneg
      h.model_lower h.edge_size h.pair_degree W T).trans
    apply div_le_div_of_nonneg_right _ (pow_pos h.kappa_pos r).le
    apply mul_le_mul_of_nonneg_right _ h.delta_nonneg
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hT) 2
  calc
    _ ≤ (conditionSurvival ν T).mean (fun W =>
        (∑ i, |(selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e) -
          eventNumerator (μ i) p W (fun e => ¬Disjoint T e)|) +
          (A : ℝ) ^ 2 * δ / κ ^ r +
          |(∑ v ∈ T, rawDegree μ p W v) - testDegree μ p T|) := by
      apply (conditionSurvival ν T).mean_mono
      intro W
      have hfirst :
          |(∑ i, (selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e)) -
            ∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e)| ≤
          ∑ i, |(selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e) -
            eventNumerator (μ i) p W (fun e => ¬Disjoint T e)| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      have htri₁ := abs_sub_le
        (∑ i, (selectLaw (μ i) p h.model_pos t W).prob (fun e => ¬Disjoint T e))
        (∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e)) (testDegree μ p T)
      have htri₂ := abs_sub_le
        (∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e))
        (∑ v ∈ T, rawDegree μ p W v) (testDegree μ p T)
      linarith [hover W]
    _ ≤ roundMeanLoss r A κ δ ε t D := by
      rw [FiniteLaw.mean_add, FiniteLaw.mean_add, FiniteLaw.mean_const]
      exact add_le_add (add_le_add hnorm le_rfl) hraw

end Erdos4.FGKMT
