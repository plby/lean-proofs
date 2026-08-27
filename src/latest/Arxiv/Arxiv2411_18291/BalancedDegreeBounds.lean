import Arxiv.Arxiv2411_18291.BalancedPairPartition

/-! # Degree bounds after a balanced split -/

open Finset

namespace Arxiv2411_18291

theorem card_inter_complement_of_subset {V : Type*} [DecidableEq V]
    {N S A : Finset V} (hNS : N ⊆ S) :
    (N ∩ (S \ A)).card + (N ∩ A).card = N.card := by
  have heq : N ∩ (S \ A) = N \ A := by
    ext x
    simp only [mem_inter, mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hNS h.1, h.2⟩⟩
  rw [heq]
  exact card_sdiff_add_card_inter N A

theorem balanced_complement_error {N x c : ℝ}
    (h : |x - N / 2| ≤ c * (N / 2)) : |(N - x) - N / 2| ≤ c * (N / 2) := by
  rw [show (N - x) - N / 2 = -(x - N / 2) by ring, abs_neg]
  exact h

theorem balanced_half_count_bounds {N x D c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hN : |N - D| ≤ c * D) (hx : |x - N / 2| ≤ c * (N / 2)) :
    (1 - c) ^ 2 * D / 2 ≤ x ∧ x ≤ (1 + c) ^ 2 * D / 2 := by
  obtain ⟨hNl, hNu⟩ := abs_le.mp hN
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have hlo : (1 - c) * D ≤ N := by linarith only [hNl]
  have hhi : N ≤ (1 + c) * D := by linarith only [hNu]
  have hlow := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hc1)
  have hhigh := mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 1 + c)
  constructor
  · nlinarith only [hlow, hxl]
  · nlinarith only [hhigh, hxu]

end Arxiv2411_18291
