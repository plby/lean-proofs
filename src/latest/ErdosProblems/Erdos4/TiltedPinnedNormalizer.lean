import ErdosProblems.Erdos4.TiltedPrimeRatios
import ErdosProblems.Erdos4.TiltedNormalizerVariance
import ErdosProblems.Erdos4.FGKMTNormalizerMoments

/-! Exact importance normalizers remain concentrated after any small prime edge is pinned. -/

namespace Erdos4.Tilted

open FGKMT

theorem mixed_eventNormalizer_second {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ρ ν : FiniteLaw Ω) (μ : FiniteLaw I) (E : I → Ω → Prop) :
    ρ.mean (fun o => eventNormalizer ν μ E o ^ 2) =
      μ.mean (fun i => μ.mean (fun j => ρ.mean
        (fun o => eventWeight ν (E i) o * eventWeight ν (E j) o))) := by
  calc
    _ = ρ.mean (fun o => (pairLaw μ μ).mean (fun ij =>
        eventWeight ν (E ij.1) o * eventWeight ν (E ij.2) o)) := by
      apply ρ.mean_congr
      intro o
      rw [pairLaw_mean_mul μ μ (fun i => eventWeight ν (E i) o) (fun i => eventWeight ν (E i) o)]
      exact pow_two _
    _ = _ := by rw [mean_swap, pairLaw_mean]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pinned_mean_subsetWeight (ν : FiniteLaw (Finset V)) (T E : Finset V)
    (hT : survival ν T ≠ 0) :
    (conditionSurvival ν T).mean (eventWeight ν (fun W => E ⊆ W)) =
      survival ν (T ∪ E) / (survival ν T * survival ν E) := by
  classical
  calc
    _ = (conditionSurvival ν T).mean (fun W => if E ⊆ W then 1 / survival ν E else 0) := by
      apply (conditionSurvival ν T).mean_congr
      intro W
      by_cases h : E ⊆ W <;> simp [eventWeight, survival, h]
    _ = (1 / survival ν E) * survival (conditionSurvival ν T) E := mean_indicator_const _ _ _
    _ = _ := by rw [conditional_survival ν T E hT]; ring

theorem pinned_mean_subsetWeight_mul (ν : FiniteLaw (Finset V)) (T E F : Finset V)
    (hT : survival ν T ≠ 0) :
    (conditionSurvival ν T).mean (fun W =>
      eventWeight ν (fun W => E ⊆ W) W * eventWeight ν (fun W => F ⊆ W) W) =
      survival ν (T ∪ E ∪ F) / (survival ν T * survival ν E * survival ν F) := by
  classical
  calc
    _ = (conditionSurvival ν T).mean (fun W =>
        if E ∪ F ⊆ W then 1 / (survival ν E * survival ν F) else 0) := by
      apply (conditionSurvival ν T).mean_congr
      intro W
      by_cases hE : E ⊆ W <;> by_cases hF : F ⊆ W <;>
        simp [eventWeight, survival, Finset.union_subset_iff, hE, hF, div_eq_mul_inv, mul_comm]
    _ = (1 / (survival ν E * survival ν F)) * survival (conditionSurvival ν T) (E ∪ F) :=
      mean_indicator_const _ _ _
    _ = _ := by rw [conditional_survival ν T _ hT, ← Finset.union_assoc]; ring

open Classical in
theorem mean_three_overlap_le (μ : FiniteLaw (Finset V)) (T : Finset V) {r : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hT : T.card ≤ r)
    (hsize : ∀ E, 0 < μ.weight E → E.card ≤ r)
    (hsparse : ∀ v, μ.prob (fun E => v ∈ E) ≤ δ) :
    μ.mean (fun E => μ.mean (fun F =>
      if ¬Disjoint T E ∨ ¬Disjoint T F ∨ ¬Disjoint E F then (1 : ℝ) else 0)) ≤ 3 * r * δ := by
  have hmeet : μ.prob (fun E => ¬Disjoint T E) ≤ (r : ℝ) * δ :=
    (meeting_prob_le μ T hsparse).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hT) hδ)
  have hinner (E : Finset V) :
      μ.mean (fun F => if ¬Disjoint T E ∨ ¬Disjoint T F ∨ ¬Disjoint E F then (1 : ℝ) else 0) ≤
        (if ¬Disjoint T E then (1 : ℝ) else 0) + μ.prob (fun F => ¬Disjoint T F) +
          μ.prob (fun F => ¬Disjoint E F) := by
    calc
      _ ≤ μ.mean (fun F => (if ¬Disjoint T E then (1 : ℝ) else 0) +
          (if ¬Disjoint T F then 1 else 0) + (if ¬Disjoint E F then 1 else 0)) := by
        apply μ.mean_mono
        intro F
        by_cases hTE : Disjoint T E <;> by_cases hTF : Disjoint T F <;>
          by_cases hEF : Disjoint E F <;> simp [hTE, hTF, hEF]
      _ = _ := by rw [FiniteLaw.mean_add, FiniteLaw.mean_add, FiniteLaw.mean_const,
        ← FiniteLaw.prob_eq_mean, ← FiniteLaw.prob_eq_mean]
  calc
    _ ≤ μ.mean (fun E => (if ¬Disjoint T E then (1 : ℝ) else 0) +
        μ.prob (fun F => ¬Disjoint T F) + (r : ℝ) * δ) := by
      apply μ.mean_mono_support
      intro E hE
      apply (hinner E).trans
      exact add_le_add le_rfl ((meeting_prob_le μ E hsparse).trans
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hsize E hE)) hδ))
    _ = 2 * μ.prob (fun E => ¬Disjoint T E) + (r : ℝ) * δ := by
      rw [FiniteLaw.mean_add, FiniteLaw.mean_add, FiniteLaw.mean_const, FiniteLaw.mean_const,
        ← FiniteLaw.prob_eq_mean]
      ring
    _ ≤ _ := by linarith

theorem pinned_subsetNormalizer_variance (ν μ : FiniteLaw (Finset V)) {σ ε δ : ℝ} {r : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδ : 0 ≤ δ)
    (hacc : SurvivalAccurate ν (fun _ => σ) (3 * r) ε)
    (hsize : ∀ E, 0 < μ.weight E → E.card ≤ r)
    (hsparse : ∀ v, μ.prob (fun E => v ∈ E) ≤ δ)
    (T : Finset V) (hT : T.card ≤ r) :
    (conditionSurvival ν T).mean (fun W =>
      (eventNormalizer ν μ (fun E W => E ⊆ W) W - 1) ^ 2) ≤
        24 * ε + 12 * r * δ / σ ^ (3 * r) := by
  classical
  have hTpos := survival_pos_of_accurate ν (fun _ => σ) (fun _ => hσ)
    (by linarith : ε < 1) hacc (show T.card ≤ 3 * r by omega)
  have hfirst : 1 - 4 * ε ≤ (conditionSurvival ν T).mean
      (eventNormalizer ν μ (fun E W => E ⊆ W)) := by
    change 1 - 4 * ε ≤ (conditionSurvival ν T).mean
      (fun W => μ.mean (fun E => eventWeight ν (fun W => E ⊆ W) W))
    rw [mean_swap]
    calc
      _ = μ.mean (fun _ => 1 - 4 * ε) := (μ.mean_const _).symm
      _ ≤ _ := by
        apply μ.mean_mono_support
        intro E hE
        rw [pinned_mean_subsetWeight ν T E hTpos.ne']
        exact survival_pair_ratio_lower ν hσ hσ1 hε0 hε hacc T E (by have hh := hsize E hE; omega)
  have hsecond : (conditionSurvival ν T).mean
      (fun W => eventNormalizer ν μ (fun E W => E ⊆ W) W ^ 2) ≤
        1 + 16 * ε + 12 * r * δ / σ ^ (3 * r) := by
    rw [mixed_eventNormalizer_second]
    calc
      _ ≤ μ.mean (fun E => μ.mean (fun F => 1 + 16 * ε + (4 / σ ^ (3 * r)) *
          (if ¬Disjoint T E ∨ ¬Disjoint T F ∨ ¬Disjoint E F then (1 : ℝ) else 0))) := by
        apply μ.mean_mono_support
        intro E hE
        apply μ.mean_mono_support
        intro F hF
        rw [pinned_mean_subsetWeight_mul ν T E F hTpos.ne']
        by_cases hbad : ¬Disjoint T E ∨ ¬Disjoint T F ∨ ¬Disjoint E F
        · rw [if_pos hbad, mul_one]
          apply (survival_triple_ratio_upper ν hσ hσ1 hε hacc T E F hT (hsize E hE) (hsize F hF)).trans
          linarith
        · rw [if_neg hbad, mul_zero, add_zero]
          have hd : Disjoint T E ∧ Disjoint T F ∧ Disjoint E F := by simpa only [not_or, not_not] using hbad
          exact survival_triple_ratio_upper_disjoint ν hσ hε0 hε hacc T E F
            (by have he := hsize E hE; have hf := hsize F hF; omega) hd.1 hd.2.1 hd.2.2
      _ = 1 + 16 * ε + (4 / σ ^ (3 * r)) * μ.mean (fun E => μ.mean (fun F =>
          if ¬Disjoint T E ∨ ¬Disjoint T F ∨ ¬Disjoint E F then (1 : ℝ) else 0)) := by
        simp only [FiniteLaw.mean_add, FiniteLaw.mean_const, FiniteLaw.mean_const_mul]
      _ ≤ 1 + 16 * ε + (4 / σ ^ (3 * r)) * (3 * r * δ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mean_three_overlap_le μ T hδ hT hsize hsparse) (by positivity))
      _ = _ := by ring
  rw [FiniteLaw.mean_sq_sub_one]
  linarith

end Erdos4.Tilted
