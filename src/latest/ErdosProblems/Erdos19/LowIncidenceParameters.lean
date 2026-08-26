import ErdosProblems.Erdos19.CoveredColorParameters
import ErdosProblems.Erdos19.ReservedPaletteParameters

/-! # Numerical bounds for coloring a low-incidence hypergraph -/

namespace Erdos19

theorem near_full_degree_lower (n s : ℕ) (hs : 2 ≤ s) :
    n ≤ 2 * (n - n / s) := by
  have hq := Nat.mul_div_le n s
  have hscale : 2 * (n / s) ≤ s * (n / s) := Nat.mul_le_mul_right _ hs
  omega

theorem near_full_palette_slack (n s : ℕ) (hs : 2 ≤ s) (hn : s ≤ n) :
    (1 + 1 / (4 * (s : ℝ))) * ((n - n / s : ℕ) : ℝ) ≤
      ((n - n / (2 * s) : ℕ) : ℝ) := by
  have hspos : 0 < s := by omega
  have hqpos : 1 ≤ n / s := (Nat.le_div_iff_mul_le hspos).mpr (by simpa using hn)
  have hfloor := Nat.lt_mul_div_succ n hspos
  have hscale := Nat.mul_le_mul_left s (show n / s + 1 ≤ 2 * (n / s) by omega)
  have hDscale : n - n / s ≤ 2 * s * (n / s) := by
    have hsub := Nat.sub_le n (n / s)
    nlinarith only [hfloor, hscale, hsub]
  have hq2 := scaled_floor_le_div n 2 s hspos
  have hqle := Nat.div_le_self n s
  have hq2le := Nat.div_le_self n (2 * s)
  have hDsum : ((n - n / s : ℕ) : ℝ) + (n / s : ℕ) = n := by
    exact_mod_cast Nat.sub_add_cancel hqle
  have hPsum : ((n - n / (2 * s) : ℕ) : ℝ) + (n / (2 * s) : ℕ) = n := by
    exact_mod_cast Nat.sub_add_cancel hq2le
  have hq2R : (2 : ℝ) * (n / (2 * s) : ℕ) ≤ (n / s : ℕ) := by exact_mod_cast hq2
  have hDscaleR : ((n - n / s : ℕ) : ℝ) ≤ 2 * s * (n / s : ℕ) := by
    exact_mod_cast hDscale
  have hden : (0 : ℝ) < 4 * s := by positivity
  have hslack : ((n - n / s : ℕ) : ℝ) / (4 * s) ≤ (n / s : ℕ) / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDscaleR]
  rw [add_mul, one_mul, one_div_mul_eq_div]
  linarith only [hslack, hq2R, hDsum, hPsum]

theorem total_incidence_capacity_load (n D T a : ℕ) (hD : 0 < D)
    (hdegree : n ≤ 2 * D) (htotal : 16 * a * T ≤ n ^ 2) :
    8 * a * (T / D) ≤ n := by
  have hdiv := Nat.mul_div_le T D
  have hdivScale := Nat.mul_le_mul_left (16 * a) hdiv
  have hdegreeScale := Nat.mul_le_mul_left n hdegree
  apply Nat.le_of_mul_le_mul_left (c := D) _ hD
  nlinarith only [hdivScale, htotal, hdegreeScale]

theorem total_incidence_capacity_room (n D T a r L M : ℕ) (ha : 0 < a)
    (hD : 0 < D) (hdegree : n ≤ 2 * D) (htotal : 16 * a * T ≤ n ^ 2)
    (hDM : D ≤ L * M)
    (hp : 2 * (2 * r + (2 * r) * (2 * r * M)) + 2 ≤ n / a) :
    T / D + 2 * r + (2 * r) * ((2 * r) * D / L) < n / a := by
  have hload : 8 * (T / D) ≤ n / a := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    have h := total_incidence_capacity_load n D T a hD hdegree htotal
    nlinarith only [h]
  have hdiv : (2 * r) * D / L ≤ 2 * r * M := by
    apply Nat.div_le_of_le_mul
    have h := Nat.mul_le_mul_left (2 * r) hDM
    nlinarith only [h]
  have hterm := Nat.mul_le_mul_left (2 * r) hdiv
  omega

#print axioms near_full_palette_slack
#print axioms total_incidence_capacity_room

end Erdos19
