import ErdosProblems.Erdos547.SkewRoutingCapacity

/-!
# Numerical margins used to construct the shrub host setup
-/

namespace Erdos547

theorem allocation_surplus_product (s β : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1 / 100)
    (hβ : 0 ≤ β) (hβs : β ≤ s / 100) :
    1 ≤ (1 - s) * (1 + 10 * s) * (1 - 2 * s) * (1 - 2 * β) := by
  have hleft : 1 + 8 * s ≤ (1 - s) * (1 + 10 * s) := by nlinarith only [hs, hs1]
  have hright : 1 - 3 * s ≤ (1 - 2 * s) * (1 - 2 * β) := by
    nlinarith only [hβs, hs, hβ, mul_nonneg hs hβ]
  have hm := mul_le_mul hleft hright (show 0 ≤ 1 - 3 * s by linarith only [hs1])
    (show 0 ≤ (1 - s) * (1 + 10 * s) from mul_nonneg
      (by linarith only [hs1]) (by linarith only [hs]))
  nlinarith only [hm, hs, hs1]

theorem relative_allocation_mean (s β m M N : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 100) (hβ : 0 ≤ β) (hβs : β ≤ s / 100)
    (hm : 0 < m) (hN : 0 < N) (hM : (1 - 2 * β) * m ≤ M) :
    N / ((1 - s) * ((1 + 10 * s) / m) * N) + s * M ≤ (1 - s) * M := by
  have hden : 0 < (1 - s) * (1 + 10 * s) := by
    apply mul_pos
    · linarith only [hs1]
    · linarith only [hs]
  have he : N / ((1 - s) * ((1 + 10 * s) / m) * N) =
      m / ((1 - s) * (1 + 10 * s)) := by
    field_simp
  have hprod := allocation_surplus_product s β hs hs1 hβ hβs
  have hmprod := mul_le_mul_of_nonneg_right hprod hm.le
  have hMprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 - 2 * s by linarith only [hs1])) hden.le
  have hmean : m / ((1 - s) * (1 + 10 * s)) ≤ (1 - 2 * s) * M := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hmprod, hMprod]
  rw [he]
  nlinarith only [hmean]

theorem relative_capacity_fits (M s ε D w : ℝ)
    (hM : 0 ≤ M) (hs : s ≤ 1) (hw : w ≤ D) (herr : ε ≤ s * D) :
    (1 - s) * M * w ≤ (D - ε) * M := by
  have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ 1 - s by linarith only [hs])
  have hfit : (1 - s) * w ≤ D - ε := by nlinarith only [hh, herr]
  have hm := mul_le_mul_of_nonneg_right hfit hM
  nlinarith only [hm]

theorem reservoir_neighbour_margin (D ε θ β q m : ℝ)
    (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hm : 0 ≤ m)
    (hD : θ ≤ D) (hε : ε ≤ θ / 2) (hq : β * m / 2 ≤ q)
    (hmargin : 48 * ε ≤ θ * β) : 12 * ε * m ≤ (D - ε) * q := by
  have hd : θ / 2 ≤ D - ε := by linarith only [hD, hε]
  have hh := mul_le_mul hd hq (show 0 ≤ β * m / 2 by positivity)
    (show 0 ≤ D - ε by linarith only [hd, hθ])
  have hl := mul_le_mul_of_nonneg_right hmargin hm
  nlinarith only [hh, hl]

end Erdos547

#print axioms Erdos547.relative_allocation_mean
#print axioms Erdos547.reservoir_neighbour_margin
