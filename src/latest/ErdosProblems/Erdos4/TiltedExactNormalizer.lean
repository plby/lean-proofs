import ErdosProblems.Erdos4.TiltedNormalizerVariance
import ErdosProblems.Erdos4.FGKMTRawDegree

/-! Concentration for exact importance weights, including the erased incidence law. -/

namespace Erdos4.Tilted

open FGKMT

theorem mean_eventNormalizer_support {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (μ : FiniteLaw I) (E : I → Ω → Prop)
    (hE : ∀ i, 0 < μ.weight i → ν.prob (E i) ≠ 0) :
    ν.mean (eventNormalizer ν μ E) = 1 := by
  change ν.mean (fun o => μ.mean (fun i => eventWeight ν (E i) o)) = 1
  rw [mean_swap]
  calc
    _ = μ.mean (fun _ => 1) := μ.mean_congr_support (fun i hi => mean_eventWeight ν (E i) (hE i hi))
    _ = _ := μ.mean_const 1

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exactNormalizer_le_model (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {ε : ℝ} (hp : ∀ v, 0 < p v) (hε : ε < 1)
    (hsize : ∀ E, 0 < μ.weight E → E.card ≤ r)
    (hacc : SurvivalAccurate ν p r ε) (W : Finset V) :
    eventNormalizer ν μ (fun E W => E ⊆ W) W ≤ (1 / (1 - ε)) * normalizer μ p W := by
  classical
  have hepos : 0 < 1 - ε := by linarith
  calc
    _ ≤ μ.mean (fun E => (1 / (1 - ε)) * (if E ⊆ W then 1 / setProduct p E else 0)) := by
      apply μ.mean_mono_support
      intro E hE
      have hprod := setProduct_pos p hp E
      have hlo : (1 - ε) * setProduct p E ≤ survival ν E :=
        (le_div_iff₀ hprod).mp (by have hh := (abs_le.mp (hacc E (hsize E hE))).1; linarith)
      by_cases hEW : E ⊆ W
      · simp only [eventWeight, if_pos hEW]
        calc
          _ ≤ 1 / ((1 - ε) * setProduct p E) := one_div_le_one_div_of_le (mul_pos hepos hprod) hlo
          _ = _ := by simp only [one_div, mul_inv_rev, mul_comm]
      · simp only [eventWeight, if_neg hEW, mul_zero]
        exact le_rfl
    _ = _ := by rw [FiniteLaw.mean_const_mul, ← normalizer_eq_mean]

theorem exactNormalizer_variance (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {κ δ ε : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ E, 0 < μ.weight E → E.card ≤ r)
    (hsparse : ∀ v, μ.prob (fun E => v ∈ E) ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) :
    ν.mean (fun W => (eventNormalizer ν μ (fun E W => E ⊆ W) W - 1) ^ 2) ≤
      8 * ε + 4 * r * δ / κ ^ r := by
  have hp0 : ∀ v, 0 < p v := fun v => hκ.trans_le (hp v)
  have hepos : 0 < 1 - ε := by linarith
  have hfirst : ν.mean (eventNormalizer ν μ (fun E W => E ⊆ W)) = 1 := by
    apply mean_eventNormalizer_support
    intro E hE
    exact (survival_pos_of_accurate ν p hp0 (by linarith : ε < 1) hacc
      (by have hh := hsize E hE; omega)).ne'
  have hfac : (1 / (1 - ε)) ^ 2 * (1 + ε) ≤ 1 + 8 * ε := by
    have heq : (1 / (1 - ε)) ^ 2 * (1 + ε) = (1 + ε) / (1 - ε) ^ 2 := by
      rw [div_pow]
      ring
    rw [heq]
    apply (div_le_iff₀ (pow_pos hepos 2)).mpr
    have hh : 0 ≤ ε * (5 - 15 * ε) + 8 * ε ^ 3 := by
      exact add_nonneg (mul_nonneg hε0 (by linarith)) (by positivity)
    nlinarith
  have hfac4 : (1 / (1 - ε)) ^ 2 * (1 + ε) ≤ 4 := hfac.trans (by linarith)
  have hsecond : ν.mean (fun W => eventNormalizer ν μ (fun E W => E ⊆ W) W ^ 2) ≤
      1 + 8 * ε + 4 * r * δ / κ ^ r := by
    calc
      _ ≤ ν.mean (fun W => ((1 / (1 - ε)) * normalizer μ p W) ^ 2) := by
        apply ν.mean_mono
        intro W
        exact pow_le_pow_left₀ (eventNormalizer_nonneg ν μ _ W)
          (exactNormalizer_le_model ν μ p hp0 (by linarith : ε < 1) hsize
            (fun E hE => hacc E (by omega)) W) 2
      _ = (1 / (1 - ε)) ^ 2 * ν.mean (fun W => normalizer μ p W ^ 2) := by
        simp only [mul_pow, FiniteLaw.mean_const_mul]
      _ ≤ (1 / (1 - ε)) ^ 2 * ((1 + ε) * (1 + (r : ℝ) * δ / κ ^ r)) :=
        mul_le_mul_of_nonneg_left
          (normalizer_second_moment ν μ p hκ hκ1 hδ hε0 hp hsize hsparse hacc) (sq_nonneg _)
      _ = (1 / (1 - ε)) ^ 2 * (1 + ε) +
          ((1 / (1 - ε)) ^ 2 * (1 + ε)) * ((r : ℝ) * δ / κ ^ r) := by ring
      _ ≤ (1 + 8 * ε) + 4 * ((r : ℝ) * δ / κ ^ r) := add_le_add hfac
        (mul_le_mul_of_nonneg_right hfac4 (by positivity))
      _ = _ := by ring
  rw [FiniteLaw.mean_sq_sub_one, hfirst]
  linarith

theorem rooted_incidence_variance {I : Type*} [Fintype I]
    (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V)) (v : V)
    {r : ℕ} {σ ε δ : ℝ} (hr : 1 ≤ r) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) (hδ : 0 ≤ δ)
    (hacc : SurvivalAccurate ν (fun _ => σ) (3 * r) ε)
    (hsize : ∀ i E, 0 < (μ i).weight E → E.card ≤ r)
    (hd : 0 < vertexDegree μ v) (hpair : ∀ w, w ≠ v → pairDegree μ v w ≤ δ) :
    (conditionSurvival ν {v}).mean (fun W =>
      (eventNormalizer (conditionSurvival ν {v}) (erasedIncidence μ v) (fun E W => E ⊆ W) W - 1) ^ 2) ≤
        32 * ε + 4 * r * δ / (vertexDegree μ v * σ ^ r) := by
  have hac := conditional_accuracy ν (fun _ => σ) (fun _ => hσ) (by linarith : ε < 1)
    hacc ({v} : Finset V) (B := 2 * r) (by simp only [Finset.card_singleton]; omega)
  have hac' : SurvivalAccurate (conditionSurvival ν {v}) (pinnedModel (fun _ => σ) {v}) (2 * r) (4 * ε) := by
    intro E hE
    apply (hac E hE).trans
    apply (div_le_iff₀ (by linarith : 0 < 1 - ε)).mpr
    nlinarith [mul_nonneg hε0 (show 0 ≤ 1 / 2 - ε by linarith)]
  have hp : ∀ w, σ ≤ pinnedModel (fun _ => σ) {v} w := by
    intro w
    unfold pinnedModel
    split_ifs
    · exact hσ1
    · exact le_rfl
  have hh := exactNormalizer_variance (conditionSurvival ν {v}) (erasedIncidence μ v)
    (pinnedModel (fun _ => σ) {v}) hσ hσ1 (div_nonneg hδ hd.le)
    (by positivity : 0 ≤ 4 * ε) (by linarith : 4 * ε ≤ 1 / 4) hp
    (erasedIncidence_size μ v hd hsize) (erasedIncidence_sparse μ v hd hδ hpair) hac'
  exact hh.trans_eq (by ring)

end Erdos4.Tilted
