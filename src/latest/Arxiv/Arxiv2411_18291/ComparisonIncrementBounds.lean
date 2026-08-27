import Arxiv.Arxiv2411_18291.DiscreteReciprocalBounds

/-!
# Explicit increments for power main terms and reciprocal errors

Both signs of each comparison error are included. These finite-step bounds
allow larger reciprocal errors to replace the logarithmic errors in an
eventual clique-removal argument.
-/

namespace Arxiv2411_18291

theorem scaled_power_increment_bounds {s p C : ℝ} (hs : 0 ≤ s) (hsp : s ≤ p)
    (hC : 0 ≤ C) (k : ℕ) :
    -(k : ℝ) * C * p ^ (k - 1) * (p - s) ≤ C * s ^ k - C * p ^ k ∧
      C * s ^ k - C * p ^ k ≤ -(k : ℝ) * C * p ^ (k - 1) * (p - s) +
        C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := real_pow_difference_error hs hsp k
  have hlo' := mul_le_mul_of_nonneg_left hlo hC
  have hhi' := mul_le_mul_of_nonneg_left hhi hC
  constructor <;> nlinarith only [hlo', hhi']

theorem scaled_reciprocal_increment_bounds {s p A : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) (hA : 0 ≤ A) :
    A * (p - s) / p ^ 2 ≤ A / s - A / p ∧
      A / s - A / p ≤ 2 * A * (p - s) / p ^ 2 := by
  obtain ⟨hlo, hhi⟩ := reciprocal_difference_bounds hs hsp hhalf
  have hlo' := mul_le_mul_of_nonneg_left hlo hA
  have hhi' := mul_le_mul_of_nonneg_left hhi hA
  constructor
  · calc
      _ = A * ((p - s) / p ^ 2) := by ring
      _ ≤ A * (1 / s - 1 / p) := hlo'
      _ = _ := by ring
  · calc
      _ = A * (1 / s - 1 / p) := by ring
      _ ≤ A * (2 * (p - s) / p ^ 2) := hhi'
      _ = _ := by ring

theorem scaled_reciprocal_square_increment_bounds {s p A : ℝ} (hs : 0 < s)
    (hsp : s ≤ p) (hhalf : p ≤ 2 * s) (hA : 0 ≤ A) :
    2 * A * (p - s) / p ^ 3 ≤ A / s ^ 2 - A / p ^ 2 ∧
      A / s ^ 2 - A / p ^ 2 ≤ 8 * A * (p - s) / p ^ 3 := by
  obtain ⟨hlo, hhi⟩ := reciprocal_square_difference_bounds hs hsp hhalf
  have hlo' := mul_le_mul_of_nonneg_left hlo hA
  have hhi' := mul_le_mul_of_nonneg_left hhi hA
  simp only [div_pow, one_pow] at hlo' hhi'
  constructor
  · calc
      _ = A * (2 * (p - s) / p ^ 3) := by ring
      _ ≤ A * (1 / s ^ 2 - 1 / p ^ 2) := hlo'
      _ = _ := by ring
  · calc
      _ = A * (1 / s ^ 2 - 1 / p ^ 2) := by ring
      _ ≤ A * (8 * (p - s) / p ^ 3) := hhi'
      _ = _ := by ring

theorem power_add_reciprocal_increment_bounds {s p C A : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) (hC : 0 ≤ C) (hA : 0 ≤ A) (k : ℕ) :
    let L := -(k : ℝ) * C * p ^ (k - 1) * (p - s)
    let E := C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2
    L + A * (p - s) / p ^ 2 ≤ (C * s ^ k + A / s) - (C * p ^ k + A / p) ∧
      (C * s ^ k + A / s) - (C * p ^ k + A / p) ≤ L + E + 2 * A * (p - s) / p ^ 2 := by
  obtain ⟨hplo, hphi⟩ := scaled_power_increment_bounds hs.le hsp hC k
  obtain ⟨helo, hehi⟩ := scaled_reciprocal_increment_bounds hs hsp hhalf hA
  dsimp only
  constructor <;> linarith only [hplo, hphi, helo, hehi]

theorem power_sub_reciprocal_increment_bounds {s p C A : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) (hC : 0 ≤ C) (hA : 0 ≤ A) (k : ℕ) :
    let L := -(k : ℝ) * C * p ^ (k - 1) * (p - s)
    let E := C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2
    L - 2 * A * (p - s) / p ^ 2 ≤ (C * s ^ k - A / s) - (C * p ^ k - A / p) ∧
      (C * s ^ k - A / s) - (C * p ^ k - A / p) ≤ L + E - A * (p - s) / p ^ 2 := by
  obtain ⟨hplo, hphi⟩ := scaled_power_increment_bounds hs.le hsp hC k
  obtain ⟨helo, hehi⟩ := scaled_reciprocal_increment_bounds hs hsp hhalf hA
  dsimp only
  constructor <;> linarith only [hplo, hphi, helo, hehi]

theorem power_add_reciprocal_square_increment_bounds {s p C A : ℝ} (hs : 0 < s)
    (hsp : s ≤ p) (hhalf : p ≤ 2 * s) (hC : 0 ≤ C) (hA : 0 ≤ A) (k : ℕ) :
    let L := -(k : ℝ) * C * p ^ (k - 1) * (p - s)
    let E := C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2
    L + 2 * A * (p - s) / p ^ 3 ≤ (C * s ^ k + A / s ^ 2) - (C * p ^ k + A / p ^ 2) ∧
      (C * s ^ k + A / s ^ 2) - (C * p ^ k + A / p ^ 2) ≤
        L + E + 8 * A * (p - s) / p ^ 3 := by
  obtain ⟨hplo, hphi⟩ := scaled_power_increment_bounds hs.le hsp hC k
  obtain ⟨helo, hehi⟩ := scaled_reciprocal_square_increment_bounds hs hsp hhalf hA
  dsimp only
  constructor <;> linarith only [hplo, hphi, helo, hehi]

theorem power_sub_reciprocal_square_increment_bounds {s p C A : ℝ} (hs : 0 < s)
    (hsp : s ≤ p) (hhalf : p ≤ 2 * s) (hC : 0 ≤ C) (hA : 0 ≤ A) (k : ℕ) :
    let L := -(k : ℝ) * C * p ^ (k - 1) * (p - s)
    let E := C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2
    L - 8 * A * (p - s) / p ^ 3 ≤ (C * s ^ k - A / s ^ 2) - (C * p ^ k - A / p ^ 2) ∧
      (C * s ^ k - A / s ^ 2) - (C * p ^ k - A / p ^ 2) ≤
        L + E - 2 * A * (p - s) / p ^ 3 := by
  obtain ⟨hplo, hphi⟩ := scaled_power_increment_bounds hs.le hsp hC k
  obtain ⟨helo, hehi⟩ := scaled_reciprocal_square_increment_bounds hs hsp hhalf hA
  dsimp only
  constructor <;> linarith only [hplo, hphi, helo, hehi]

end Arxiv2411_18291
