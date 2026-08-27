import ErdosProblems.Erdos4.FGKMTConditionalLaw
import ErdosProblems.Erdos4.FGKMTSupport

/-! Condition on full-tuple survival before mapping centers to clipped target edges. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

noncomputable def initialCenterNormalizer (μ : FiniteLaw Ω) (E : Ω → Prop) (σ : ℝ) (k : ℕ) : ℝ :=
  μ.prob E / σ ^ k

noncomputable def initialPinnedIncidence (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) (σ : ℝ) (k : ℕ) (v : V) : ℝ :=
  μ.prob (fun o => E o ∧ v ∈ edge o) / σ ^ (k - 1)

noncomputable def initialEdgeLaw (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) (σ : ℝ) (k : ℕ) (o₀ : Ω) : FiniteLaw (Finset V) :=
  if |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2 then
    (μ.condition E o₀).map edge else FiniteLaw.dirac ∅

theorem initialPinnedIncidence_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (v : V) :
    0 ≤ initialPinnedIncidence μ E edge σ k v :=
  div_nonneg (μ.prob_nonneg _) (pow_nonneg hσ.le _)

theorem initial_good_mass_bounds (μ : FiniteLaw Ω) (E : Ω → Prop) {σ : ℝ} (hσ : 0 < σ) (k : ℕ)
    (hgood : |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2) :
    0 < μ.prob E ∧ σ ^ k / 2 ≤ μ.prob E ∧ μ.prob E ≤ 3 * σ ^ k / 2 := by
  obtain ⟨hlow', hupp'⟩ := abs_le.mp hgood
  change - (1 / 2 : ℝ) ≤ μ.prob E / σ ^ k - 1 at hlow'
  change μ.prob E / σ ^ k - 1 ≤ (1 / 2 : ℝ) at hupp'
  have hlo : 1 / 2 ≤ μ.prob E / σ ^ k := by linarith
  have hup : μ.prob E / σ ^ k ≤ 3 / 2 := by linarith
  have hl := (le_div_iff₀ (pow_pos hσ k)).mp hlo
  have hu := (div_le_iff₀ (pow_pos hσ k)).mp hup
  have hlow : σ ^ k / 2 ≤ μ.prob E := by linarith
  exact ⟨(by positivity : 0 < σ ^ k / 2).trans_le hlow, hlow, by linarith⟩

theorem initialEdgeLaw_event (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (o₀ : Ω)
    (F : Finset V → Prop) (hF : ¬F ∅) :
    (initialEdgeLaw μ E edge σ k o₀).prob F =
      if |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2 then
        μ.prob (fun o => E o ∧ F (edge o)) / μ.prob E else 0 := by
  unfold initialEdgeLaw
  by_cases hgood : |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2
  · rw [if_pos hgood, if_pos hgood, FiniteLaw.prob_map,
      FiniteLaw.condition_prob μ E _ o₀ (initial_good_mass_bounds μ E hσ k hgood).1.ne']
  · rw [if_neg hgood, if_neg hgood, FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac]
    simp only [if_neg hF]

theorem initialEdgeLaw_event_le (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (o₀ : Ω)
    (F : Finset V → Prop) (hF : ¬F ∅) :
    (initialEdgeLaw μ E edge σ k o₀).prob F ≤ 2 * μ.prob (fun o => F (edge o)) / σ ^ k := by
  rw [initialEdgeLaw_event μ E edge hσ k o₀ F hF]
  by_cases hgood : |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2
  · rw [if_pos hgood]
    have hb := initial_good_mass_bounds μ E hσ k hgood
    calc
      _ ≤ μ.prob (fun o => F (edge o)) / μ.prob E :=
        div_le_div_of_nonneg_right (μ.prob_mono (fun o ho => ho.2)) hb.1.le
      _ ≤ μ.prob (fun o => F (edge o)) / (σ ^ k / 2) :=
        div_le_div_of_nonneg_left (μ.prob_nonneg _) (by positivity) hb.2.1
      _ = _ := by field_simp
  · rw [if_neg hgood]
    exact div_nonneg (mul_nonneg (by norm_num) (μ.prob_nonneg _)) (pow_nonneg hσ.le _)

theorem initialEdgeLaw_vertex_lower (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k) (o₀ : Ω) (v : V) :
    (if |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2 then
      (2 / (3 * σ)) * initialPinnedIncidence μ E edge σ k v else 0) ≤
        (initialEdgeLaw μ E edge σ k o₀).prob (fun e => v ∈ e) := by
  rw [initialEdgeLaw_event μ E edge hσ k o₀ (fun e => v ∈ e) (by simp)]
  by_cases hgood : |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2
  · rw [if_pos hgood, if_pos hgood]
    have hb := initial_good_mass_bounds μ E hσ k hgood
    have hpow : σ ^ k = σ ^ (k - 1) * σ := by rw [← pow_succ, Nat.sub_add_cancel hk]
    calc
      _ = μ.prob (fun o => E o ∧ v ∈ edge o) / (3 * σ ^ k / 2) := by
        unfold initialPinnedIncidence
        rw [hpow]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (μ.prob_nonneg _) hb.1 hb.2.2
  · simp only [if_neg hgood, le_refl]

theorem initialEdgeLaw_support (μ : FiniteLaw Ω) (E : Ω → Prop)
    (edge : Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (o₀ : Ω)
    (e : Finset V) (he : 0 < (initialEdgeLaw μ E edge σ k o₀).weight e) :
    e = ∅ ∨ ∃ o, E o ∧ 0 < μ.weight o ∧ edge o = e := by
  by_cases hgood : |initialCenterNormalizer μ E σ k - 1| ≤ 1 / 2
  · right
    rw [initialEdgeLaw, if_pos hgood] at he
    obtain ⟨o, ho, hedge⟩ := FiniteLaw.map_support (μ.condition E o₀) edge e he
    have hmass := (initial_good_mass_bounds μ E hσ k hgood).1
    have hE := FiniteLaw.condition_support μ E o₀ o hmass.ne' ho
    rw [FiniteLaw.condition_weight μ E o₀ o hmass.ne', if_pos hE] at ho
    exact ⟨o, hE, (div_pos_iff_of_pos_right hmass).mp ho, hedge⟩
  · left
    rw [initialEdgeLaw, if_neg hgood] at he
    by_contra hne
    simp only [FiniteLaw.dirac, if_neg hne] at he
    linarith

end Erdos4.FGKMT
