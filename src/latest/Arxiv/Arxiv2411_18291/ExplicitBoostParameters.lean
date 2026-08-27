import Arxiv.Arxiv2411_18291.ExplicitBoostSize

/-! # Finite margins for the two rooted clique counts in regularity boosting -/

namespace Arxiv2411_18291

theorem boost_decode_margin_quarter {q r : ℕ} (hqr : r + 1 < q) :
    ((q + (r + 1)).choose (r + 1) : ℝ) * boostComplementBound q ≤ 1 / 4 := by
  have hn : 4 * (q + (r + 1)).choose (r + 1) ≤ 2 ^ (3 * q) := by
    calc
      _ ≤ 4 * 2 ^ (q + (r + 1)) := Nat.mul_le_mul_left 4 (Nat.choose_le_two_pow _ _)
      _ = 2 ^ (q + (r + 1) + 2) := by rw [pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hh : 4 * ((q + (r + 1)).choose (r + 1) : ℝ) ≤ (2 : ℝ) ^ (3 * q) := by
    exact_mod_cast hn
  have hp : (0 : ℝ) < (2 : ℝ) ^ (3 * q) := by positivity
  have hm := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hp.le)
  rw [mul_inv_cancel₀ hp.ne'] at hm
  unfold boostComplementBound
  nlinarith only [hm]

theorem explicit_boost_count_numerics {q r n : ℕ} (hqr : r + 1 < q)
    (hn : (4 * q) ^ (90 * q) ≤ n) :
    (q : ℝ) * (q - (r + 1) : ℕ) +
        (q.choose (r + 1) : ℝ) * boostComplementBound q * n ≤
      (2 * (q.choose (r + 1) : ℝ) * boostComplementBound q) * n ∧
    (q + (r + 1) : ℕ) * (q : ℝ) +
        ((q + (r + 1)).choose (r + 1) : ℝ) * boostComplementBound q * n ≤ (n : ℝ) / 2 := by
  have hq : 2 ≤ q := by omega
  obtain ⟨hsize, hgeom, _⟩ := boost_threshold_root_size_bounds hq hn
  have hsize' : (q : ℝ) ^ 2 * (2 : ℝ) ^ (3 * q) ≤ n := by exact_mod_cast hsize
  have hgeom' : 8 * (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hgeom
  have hθ : 0 ≤ boostComplementBound q := by unfold boostComplementBound; positivity
  have hbase : (q : ℝ) ^ 2 ≤ boostComplementBound q * n := by
    calc
      _ ≤ (n : ℝ) / (2 : ℝ) ^ (3 * q) := (le_div_iff₀ (by positivity)).mpr hsize'
      _ = _ := by unfold boostComplementBound; ring
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hpart : (q : ℝ) * (q - (r + 1) : ℕ) ≤
      (q.choose (r + 1) : ℝ) * boostComplementBound q * n := by
    calc
      _ ≤ (q : ℝ) ^ 2 := by
        have hs : ((q - (r + 1) : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q (r + 1)
        have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)
        nlinarith only [hh]
      _ ≤ _ := hbase
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hk
          (mul_nonneg hθ (Nat.cast_nonneg n))
        nlinarith only [hh]
  have hd := mul_le_mul_of_nonneg_right (boost_decode_margin_quarter hqr) (Nat.cast_nonneg n)
  have hrq : ((r + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hqr.le
  have hsum := mul_le_mul_of_nonneg_right (add_le_add_left hrq (q : ℝ)) (Nat.cast_nonneg q)
  push_cast
  constructor
  · nlinarith only [hpart]
  · push_cast at hsum
    nlinarith only [hsum, hd, hgeom']

end Arxiv2411_18291
