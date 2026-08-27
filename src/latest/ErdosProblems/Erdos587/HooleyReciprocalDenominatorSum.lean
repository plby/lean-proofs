import ErdosProblems.Erdos587.HooleyWeightedGcd

/-! # Denominator sums for the reciprocal short-progression range -/

open scoped BigOperators

namespace Erdos587

lemma delta_harmonic_dyadic_bound (D : ℕ) :
    (∑ b ∈ Finset.Icc (1 : ℕ) (2 ^ D), (1 : ℝ) / b) ≤ 2 * (D + 1) := by
  classical
  let S := Finset.Icc 1 (2 ^ D)
  have hmap (b : ℕ) (hb : b ∈ S) : Nat.clog 2 b ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.clog_le_of_le_pow (Finset.mem_Icc.mp hb).2))
  have hlevel (j : ℕ) (hj : j ∈ Finset.range (D + 1)) :
      (∑ b ∈ S with Nat.clog 2 b = j, (1 : ℝ) / b) ≤ 2 := by
    let T := S.filter (fun b => Nat.clog 2 b = j)
    have hsub : T ⊆ Finset.Icc 1 (2 ^ j) := by
      intro b hb
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1, ?_⟩
      have h := Nat.le_pow_clog (by norm_num : 1 < 2) b
      simpa only [(Finset.mem_filter.mp hb).2] using h
    have hcard : (T.card : ℝ) ≤ 2 ^ j := by
      have h := Finset.card_le_card hsub
      simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
      exact_mod_cast h
    have hpoint (b : ℕ) (hb : b ∈ T) : (1 : ℝ) / b ≤ 2 / 2 ^ j := by
      have hbpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      have hlo := (delta_dyadic_denominator_bounds hbpos).1
      rw [(Finset.mem_filter.mp hb).2] at hlo
      calc
        _ ≤ 1 / ((2 : ℝ) ^ j / 2) := one_div_le_one_div_of_le (by positivity) hlo.le
        _ = _ := by ring
    calc
      _ ≤ ∑ _b ∈ T, (2 : ℝ) / 2 ^ j := Finset.sum_le_sum hpoint
      _ = (T.card : ℝ) * (2 / 2 ^ j) := by simp
      _ ≤ 2 ^ j * (2 / 2 ^ j) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 := by field_simp
  calc
    _ = ∑ j ∈ Finset.range (D + 1), ∑ b ∈ S with Nat.clog 2 b = j, (1 : ℝ) / b :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _j ∈ Finset.range (D + 1), (2 : ℝ) := Finset.sum_le_sum hlevel
    _ = _ := by simp; ring

lemma delta_short_denominator_card {D : ℕ} {H : ℝ} (hH : 0 ≤ H) :
    (((Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H)).card : ℝ) ≤ H := by
  have hsub : (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H) ⊆
      Finset.Icc 1 ⌊H⌋₊ := by
    intro b hb
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1, Nat.le_floor (Finset.mem_filter.mp hb).2⟩
  have h := Finset.card_le_card hsub
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
  exact (show (((Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H)).card : ℝ) ≤ ⌊H⌋₊ by
    exact_mod_cast h).trans (Nat.floor_le hH)

lemma delta_short_denominator_shell_cost (D : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (∑ b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H),
      (((D - Nat.clog 2 b : ℕ) : ℝ) + 3)) ≤ H * (D + 3) := by
  calc
    _ ≤ ∑ _b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H), ((D : ℝ) + 3) := by
      apply Finset.sum_le_sum
      intro b hb
      have h : ((D - Nat.clog 2 b : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.sub_le D _
      linarith
    _ = (((Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H)).card : ℝ) * (D + 3) := by
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (delta_short_denominator_card hH) (by positivity)

lemma delta_reciprocal_short_denominator_cost (D : ℕ) {H U V : ℝ}
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H),
      (U * ((D - Nat.clog 2 b : ℕ) + 3) + V / b)) ≤
        U * H * (D + 3) + 2 * V * (D + 1) := by
  have hreciprocal :
      (∑ b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H), (1 : ℝ) / b) ≤
        2 * (D + 1) := by
    apply le_trans _ (delta_harmonic_dyadic_bound D)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b hb hnot => by positivity)
  calc
    _ = U * (∑ b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H),
        (((D - Nat.clog 2 b : ℕ) : ℝ) + 3)) +
      V * (∑ b ∈ (Finset.Icc 1 (2 ^ D)).filter (fun b : ℕ => (b : ℝ) ≤ H), (1 : ℝ) / b) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        ring
    _ ≤ U * (H * (D + 3)) + V * (2 * (D + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left (delta_short_denominator_shell_cost D hH) hU)
        (mul_le_mul_of_nonneg_left hreciprocal hV)
    _ = _ := by ring

end Erdos587
