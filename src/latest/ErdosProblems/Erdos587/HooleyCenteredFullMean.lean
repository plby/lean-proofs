import ErdosProblems.Erdos587.HooleyCenteredWeighted
import ErdosProblems.Erdos587.HooleyCenteredTail
import ErdosProblems.Erdos587.PrefixTail

/-! # A complete centered weighted mean with an explicit summable tail -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_centered_full_positive_mean (f : 𝓢(ℝ, ℂ)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ a q M₀ N X : ℕ, 0 < q → q.Coprime a → 0 < M₀ → M₀ ≤ N →
      ∀ L : ℝ, 1 ≤ L → 2 * N * L ≤ X → (q : ℝ) * (X : ℝ) ^ κ ≤ M₀ * L →
      ∀ σ B E : ℝ, 0 < σ → 0 ≤ B → 1 ≤ σ * M₀ →
      ∀ w : ℕ → ℂ, Summable (fun n : ℕ => ‖w (n + 1)‖) →
      (∀ m ∈ Finset.Icc 1 N, ‖w m‖ ≤ B * σ / (1 + σ * m) ^ 2) →
      (∑' n : ℕ, if N < n + 1 then ‖w (n + 1)‖ else 0) ≤ E →
      Summable (fun n : ℕ => ‖w (n + 1) * deltaSmoothCenteredQuadratic f L q (a * (n + 1))‖) ∧
      (∑' n : ℕ, ‖w (n + 1) * deltaSmoothCenteredQuadratic f L q (a * (n + 1))‖) ≤
        C * B * σ * M₀ * Real.sqrt L *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) + D * L * E := by
  obtain ⟨C, hC, hprefix⟩ := exists_delta_centered_weighted_prefix_mean
    (Bornology.isVonNBounded_singleton (𝕜 := ℝ) f) hκ
  obtain ⟨D, hD, hpoint⟩ := exists_delta_centered_pointwise_bound f
  refine ⟨C, hC, D, hD, ?_⟩
  intro a q M₀ N X hq hcop hM₀ hMN L hL hsize hsep σ B E hσ hB hσM w hwsum hw htail
  let R (m : ℕ) := deltaSmoothCenteredQuadratic f L q (a * m)
  let F (n : ℕ) := ‖w (n + 1) * R (n + 1)‖
  let G (n : ℕ) := if N < n + 1 then ‖w (n + 1)‖ else 0
  have hR (m : ℕ) : ‖R m‖ ≤ D * L := hpoint q hq (a * m) L hL
  have hGnonneg (n : ℕ) : 0 ≤ G n := by dsimp [G]; split_ifs <;> positivity
  have hGsum : Summable G := by
    apply hwsum.of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (hGnonneg n)]
    dsimp [G]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hmajor (n : ℕ) : (if N < n + 1 then F n else 0) ≤ (D * L) * G n := by
    dsimp only [G]
    split_ifs with hn
    · dsimp only [F]
      rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hR (n + 1)) (norm_nonneg _)
    · simp
  have hFnonneg (n : ℕ) : 0 ≤ F n := norm_nonneg _
  have htailnonneg (n : ℕ) : 0 ≤ (if N < n + 1 then F n else 0) := by
    split_ifs <;> simp [hFnonneg]
  have hFtail : Summable (fun n => if N < n + 1 then F n else 0) := by
    apply (hGsum.mul_left (D * L)).of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (htailnonneg n)]
    exact hmajor n
  have hFtailbound : (∑' n, if N < n + 1 then F n else 0) ≤ D * L * E := by
    calc
      _ ≤ ∑' n, (D * L) * G n := hFtail.tsum_le_tsum hmajor (hGsum.mul_left _)
      _ = (D * L) * ∑' n, G n := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)
  obtain ⟨hFsum, hFbound⟩ := summable_and_tsum_le_prefix_add_tail F N hFnonneg hFtail
  have hp := hprefix a q M₀ N X hq hcop hM₀ hMN L hL hsize hsep (fun _ => f)
    (fun _ _ => Set.mem_singleton f) σ B hσ hB hσM w hw
  have hp' : (∑ n ∈ Finset.range N, F n) ≤ C * B * σ * M₀ * Real.sqrt L *
      (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
    rw [show (∑ n ∈ Finset.range N, F n) = ∑ m ∈ Finset.Icc 1 N, ‖w m * R m‖ from
      sum_range_succ_eq_sum_Icc (fun m => ‖w m * R m‖) N]
    exact hp
  exact ⟨hFsum, hFbound.trans (add_le_add hp' hFtailbound)⟩

end Erdos587
