import Util.Bernays.FiniteCutoffError
import Util.Bernays.CountingReparametrization

/-!
# Exact natural-endpoint cutoff errors
-/

open Set Filter Topology
open scoped Classical ContDiff

namespace Bernays

theorem spatial_sum_eq_Icc {a : ℕ → ℂ} {Ψ : ℝ → ℂ} {b x : ℝ}
    (hx : 0 < x) (hb : 0 ≤ b) (hzero : Ψ 0 = 0)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b) :
    (∑' n : ℕ, a n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.Icc 1 ⌊b * x⌋₊, a n * Ψ ((n : ℝ) / x) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hz : n = 0
  · simp only [hz, Nat.cast_zero, zero_div, hzero, mul_zero]
  · have hΨ : Ψ ((n : ℝ) / x) = 0 := by
      by_contra hne
      have hnx : (n : ℝ) ≤ b * x := (div_le_iff₀ hx).mp (hsupp _ hne)
      exact hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz,
        (Nat.le_floor_iff (mul_nonneg hb hx.le)).mpr hnx⟩)
    rw [hΨ, mul_zero]

theorem natural_sharp_cutoff_error (a : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε)
    (Ψ : ℝ → ℝ) (hΨ : ∀ y : ℝ, 0 ≤ Ψ y ∧ Ψ y ≤ 1) (hΨ₀ : Ψ 0 = 0)
    (hone : ∀ y ∈ Icc ε 1, Ψ y = 1)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ 1 + ε)
    {N : ℕ} (hN : 0 < N) :
    ‖(∑ n ∈ Finset.Icc 1 N, a n) - ∑' n : ℕ, a n * (Ψ ((n : ℝ) / N) : ℂ)‖ ≤
      (∑ n ∈ Finset.Icc 1 ⌊ε * N⌋₊, ‖a n‖) +
        (∑ n ∈ Finset.Icc 1 ⌊(1 + ε) * N⌋₊, ‖a n‖) - ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 ≤ 1 + ε := by linarith
  have hAB : Finset.Icc 1 N ⊆ Finset.Icc 1 ⌊(1 + ε) * N⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    apply (Nat.le_floor_iff (mul_nonneg hb hNR.le)).mpr
    nlinarith
  have hSB : Finset.Icc 1 ⌊ε * N⌋₊ ⊆ Finset.Icc 1 ⌊(1 + ε) * N⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    apply Nat.floor_mono
    nlinarith
  have hcut := finite_cutoff_error (Finset.Icc 1 N) (Finset.Icc 1 ⌊(1 + ε) * N⌋₊)
    (Finset.Icc 1 ⌊ε * N⌋₊) hAB hSB a (fun n => Ψ ((n : ℝ) / N))
    (fun n _ => hΨ _) (fun n hn hnot => ?_)
  · rw [spatial_sum_eq_Icc (a := a) (Ψ := fun y : ℝ => (Ψ y : ℂ)) hNR hb
      (by simp only [hΨ₀, Complex.ofReal_zero])
      (fun y hy => hsupp y (by simpa only [ne_eq, Complex.ofReal_eq_zero] using hy))]
    rw [Finset.sum_sdiff_eq_sub (f := fun n : ℕ => ‖a n‖) hAB] at hcut
    linarith
  · have hn₁ : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnotfloor : ¬ n ≤ ⌊ε * N⌋₊ := fun h => hnot (Finset.mem_Icc.mpr ⟨hn₁, h⟩)
    have hnε : ε * N < (n : ℝ) := by
      exact lt_of_not_ge (fun h => hnotfloor ((Nat.le_floor_iff (mul_nonneg hε.le hNR.le)).mpr h))
    exact hone _ ⟨((le_div_iff₀ hNR).mpr hnε.le),
      (div_le_one hNR).mpr (by exact_mod_cast hnN)⟩

theorem exists_sharp_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ Ioi 0 ∧
      (∀ y : ℝ, 0 ≤ Ψ y ∧ Ψ y ≤ 1) ∧ Ψ 0 = 0 ∧
      (∀ y ∈ Icc ε 1, Ψ y = 1) ∧ (∀ y : ℝ, Ψ y ≠ 0 → y ≤ 1 + ε) := by
  obtain ⟨Ψ, hΨ, hsupp, hlo, hhi, hs⟩ := smooth_urysohn_support_Ioo
    (show ε / 2 < ε by linarith) (show (1 : ℝ) < 1 + ε by linarith)
  have hbounds (y : ℝ) : 0 ≤ Ψ y ∧ Ψ y ≤ 1 :=
    ⟨(Set.indicator_nonneg (fun _ _ => zero_le_one) y).trans (hlo y),
      (hhi y).trans (Set.indicator_le_self' (fun _ _ => zero_le_one) y)⟩
  have hplus : tsupport Ψ ⊆ Ioi 0 := by
    rw [tsupport, hs]
    apply (closure_mono Ioo_subset_Icc_self).trans
    rw [isClosed_Icc.closure_eq]
    intro y hy
    exact lt_of_lt_of_le (half_pos hε) hy.1
  refine ⟨Ψ, hΨ, hsupp, hplus, hbounds, ?_, ?_, ?_⟩
  · by_contra hzero
    exact (lt_irrefl (0 : ℝ)) (hplus (subset_closure hzero))
  · intro y hy
    have h := hlo y
    rw [Set.indicator_of_mem hy, Pi.one_apply] at h
    exact le_antisymm (hbounds y).2 h
  · intro y hy
    have hmem : y ∈ Function.support Ψ := hy
    rw [hs] at hmem
    exact hmem.2.le

end Bernays
