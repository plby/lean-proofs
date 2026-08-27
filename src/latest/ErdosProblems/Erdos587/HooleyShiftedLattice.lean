import ErdosProblems.Erdos587.LatticeBounds

/-!
# A uniformly shifted lattice sum for the major-arc envelope

Nearest-integer recentering isolates one lattice point. Every other
point is at least half as far from the real center as from that integer,
so one fixed summable kernel controls all spacings at least one quarter.
-/

open scoped BigOperators

namespace Erdos587

theorem delta_shifted_lattice_decay_bound {σ : ℝ} (hσ : 1 / 4 ≤ σ) (θ : ℝ) :
    Summable (fun n : ℤ => 1 / (1 + σ * |(n : ℝ) - θ|) ^ 2) ∧
      (∑' n : ℤ, 1 / (1 + σ * |(n : ℝ) - θ|) ^ 2) ≤ 41 := by
  classical
  let w : ℤ → ℝ := fun n => (1 / 8 : ℝ) / (1 + (1 / 8 : ℝ) * |(n : ℝ)|) ^ 2
  obtain ⟨hwsum, hwbound⟩ := normalized_lattice_kernel_bound
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
  change Summable w at hwsum
  change (∑' n : ℤ, w n) ≤ 5 at hwbound
  have hw (n : ℤ) : 0 ≤ w n := by dsimp only [w]; positivity
  have hσ0 : 0 < σ := by linarith
  have hpoint (n : ℤ) : 1 / (1 + σ * |(n : ℝ) - θ|) ^ 2 ≤
      (if n = round θ then 1 else 0) + 8 * w (n - round θ) := by
    by_cases hn : n = round θ
    · rw [if_pos hn]
      have hden : 1 ≤ (1 + σ * |(n : ℝ) - θ|) ^ 2 := by
        have hmul : 0 ≤ σ * |(n : ℝ) - θ| := by positivity
        nlinarith
      calc
        _ ≤ 1 := (div_le_one (by positivity)).mpr hden
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by norm_num) (hw _))
    · rw [if_neg hn, zero_add]
      have hgap : (1 : ℝ) ≤ |((n - round θ : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hn)
      have htriangle := abs_sub_le (n : ℝ) θ (round θ : ℝ)
      have hround := abs_sub_round θ
      have hhalf : |((n - round θ : ℤ) : ℝ)| / 8 ≤ (1 / 4 : ℝ) * |(n : ℝ) - θ| := by
        push_cast at hgap ⊢
        nlinarith
      have hdist : (1 / 8 : ℝ) * |((n - round θ : ℤ) : ℝ)| ≤ σ * |(n : ℝ) - θ| := by
        have hmul := mul_le_mul_of_nonneg_right hσ (abs_nonneg ((n : ℝ) - θ))
        linarith
      calc
        _ ≤ 1 / (1 + (1 / 8 : ℝ) * |((n - round θ : ℤ) : ℝ)|) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ = _ := by dsimp only [w]; ring
  have hfinite (S : Finset ℤ) :
      (∑ n ∈ S, 1 / (1 + σ * |(n : ℝ) - θ|) ^ 2) ≤ 41 := by
    have hind : (∑ n ∈ S, if n = round θ then (1 : ℝ) else 0) ≤ 1 := by
      simp only [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    have hshift : (∑ n ∈ S, w (n - round θ)) ≤ 5 := by
      have hinj : Set.InjOn (fun n : ℤ => n - round θ) (S : Set ℤ) := by
        intro n hn m hm heq
        change n - round θ = m - round θ at heq
        omega
      rw [← Finset.sum_image hinj]
      exact (hwsum.sum_le_tsum _ (fun n _ => hw n)).trans hwbound
    calc
      _ ≤ ∑ n ∈ S, ((if n = round θ then 1 else 0) + 8 * w (n - round θ)) :=
        Finset.sum_le_sum (fun n _ => hpoint n)
      _ = (∑ n ∈ S, if n = round θ then (1 : ℝ) else 0) +
          8 * ∑ n ∈ S, w (n - round θ) := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 41 := by linarith
  have hnonneg : 0 ≤ (fun n : ℤ => 1 / (1 + σ * |(n : ℝ) - θ|) ^ 2) := fun n => by positivity
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

end Erdos587
