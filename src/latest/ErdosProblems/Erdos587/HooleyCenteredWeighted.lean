import ErdosProblems.Erdos587.HooleyCenteredMean
import ErdosProblems.Erdos587.HooleyCauchy
import ErdosProblems.Erdos587.FrequencyWeights

/-!
# The centered mean with an enlarged Fourier cutoff

The base prefix may exceed the reciprocal physical width. Its exact cost
is the factor `σ * M₀`; all later frequencies are summed with quadratic
decay, rather than charged one harmonic factor per dyadic block.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_physical_frequency_decay_le_kernel {σ : ℝ} {M : ℕ} (hσ : 0 < σ)
    (hM : 0 < M) (hlo : 1 ≤ σ * M) (n : ℕ) :
    σ / (1 + σ * (n + 1)) ^ 2 ≤ (σ * M) * frequencyDecayKernel M n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (M : ℝ) + n + 1 ≤ M * (1 + σ * (n + 1)) := by
    have hh := mul_le_mul_of_nonneg_right hlo (show (0 : ℝ) ≤ n + 1 by positivity)
    nlinarith
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ M + n + 1 by positivity) hden 2
  have hnum : σ * ((M : ℝ) + n + 1) ^ 2 ≤
      (σ * M) * M * (1 + σ * (n + 1)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsquare hσ.le
    exact hh.trans_eq (by ring)
  calc
    _ ≤ ((σ * M) * M) / ((M : ℝ) + n + 1) ^ 2 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr hnum
    _ ≤ ((σ * M) * M) / (((M : ℝ) + n) * ((M : ℝ) + n + 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ = _ := by unfold frequencyDecayKernel; ring

theorem exists_delta_centered_weighted_prefix_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a q M₀ N X : ℕ, 0 < q → q.Coprime a →
      0 < M₀ → M₀ ≤ N → ∀ L : ℝ, 1 ≤ L → 2 * N * L ≤ X →
      (q : ℝ) * (X : ℝ) ^ κ ≤ M₀ * L →
      ∀ f : ℕ → 𝓢(ℝ, ℂ), (∀ m ∈ Finset.Icc 1 N, f m ∈ W) →
      ∀ σ B : ℝ, 0 < σ → 0 ≤ B → 1 ≤ σ * M₀ →
      ∀ w : ℕ → ℂ, (∀ m ∈ Finset.Icc 1 N, ‖w m‖ ≤ B * σ / (1 + σ * m) ^ 2) →
      (∑ m ∈ Finset.Icc 1 N, ‖w m * deltaSmoothCenteredQuadratic (f m) L q (a * m)‖) ≤
        C * B * σ * M₀ * Real.sqrt L *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_smooth_centered_mean hW hκ
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro a q M₀ N X hq hcop hM₀ hMN L hL hsize hsep f hf σ B hσ hB hσM w hw
  let F := max 1 (Real.log (Real.log (X : ℝ)))
  let D := (C + 1) * Real.sqrt L * F ^ (7 / 2 : ℝ)
  let R (m : ℕ) := deltaSmoothCenteredQuadratic (f m) L q (a * m)
  have hD : 0 ≤ D := by dsimp [D, F]; positivity
  have hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, ‖R (i + 1)‖) ≤ D * (n + M₀) := by
    intro n hn
    let M := max n M₀
    have hMn : n ≤ M := le_max_left _ _
    have hMM₀ : M₀ ≤ M := le_max_right _ _
    have hM : 1 ≤ M := hM₀.trans_le hMM₀
    have hMN' : M ≤ N := max_le hn hMN
    have hsizeM : 2 * (M : ℝ) * L ≤ X := by
      apply le_trans _ hsize
      gcongr
    have hsepM : (q : ℝ) * (X : ℝ) ^ κ ≤ M * L := by
      apply hsep.trans
      gcongr
    have hfm : ∀ m ∈ Finset.Icc 1 M, f m ∈ W := fun m hm =>
      hf m ((Finset.Icc_subset_Icc le_rfl hMN') hm)
    have hsq := hmean a M q X hM hq hcop L hL hsizeM hsepM f hfm
    have hcard : ((Finset.Icc 1 M).card : ℝ) ≤ 2 * M := by
      simp only [Nat.card_Icc, Nat.add_sub_cancel]
      linarith [Nat.cast_nonneg (α := ℝ) M]
    have hnorm := delta_sum_norm_le_of_seventh_power (Finset.Icc 1 M) R hC.le
      (Nat.cast_nonneg M) (by linarith : 0 ≤ L) (by positivity) hcard hsq
    rw [sum_range_succ_eq_sum_Icc (fun m => ‖R m‖) n]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ‖R m‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc le_rfl hMn
        · intro m hm hnot
          exact norm_nonneg _
      _ ≤ (C + 1) * M * Real.sqrt L * F ^ (7 / 2 : ℝ) := hnorm
      _ = D * M := by dsimp [D]; ring
      _ ≤ D * (n + M₀) := mul_le_mul_of_nonneg_left (by
        have hh : M ≤ n + M₀ := by dsimp [M]; omega
        exact_mod_cast hh) hD
  have hweights : ∀ n < N, ‖w (n + 1)‖ ≤ (B * σ * M₀) * frequencyDecayKernel M₀ n := by
    intro n hn
    have hh := hw (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    calc
      _ ≤ B * (σ / (1 + σ * ((n : ℝ) + 1)) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hh
      _ ≤ B * ((σ * M₀) * frequencyDecayKernel M₀ n) :=
        mul_le_mul_of_nonneg_left (delta_physical_frequency_decay_le_kernel hσ hM₀ hσM n) hB
      _ = _ := by ring
  apply (sum_decaying_frequency_mul_le hM₀ R w N D (B * σ * M₀) hD (by positivity)
    hprefix hweights).trans_eq
  dsimp [D, F]
  ring

end Erdos587
