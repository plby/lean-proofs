import ErdosProblems.Erdos19.DilutedParameters
import ErdosProblems.Erdos76.PippengerSpencerParameters

/-! # Eventual numerical bounds for the diluted local lemma -/

namespace Erdos19

theorem half_le_exp_neg_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hle : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith only [hsq, Real.exp_one_lt_three]
  rw [Real.exp_neg, inv_eq_one_div]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by linarith only [hle])

theorem diluted_exponents_bounded (L D t d : ℕ) (hL : 1 ≤ L) (hd : 0 < d)
    (hdD : d ≤ D) (hDt : D ≤ 2 * L * t) :
    Real.exp (-(t : ℝ) ^ 2 / (8 * d)) ≤ Real.exp (-(1 / (32 * (L : ℝ) ^ 2)) * D) ∧
      (1 / 2 : ℝ) ^ (t + 1) ≤ Real.exp (-(1 / (32 * (L : ℝ) ^ 2)) * D) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htR : (0 : ℝ) ≤ t := by positivity
  have hDtR : (D : ℝ) ≤ 2 * L * t := by exact_mod_cast hDt
  have hraw : (D : ℝ) * d ≤ 4 * (L : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
    have h₁ := Nat.mul_le_mul_left D hdD
    have h₂ := Nat.pow_le_pow_left hDt 2
    have h₁R : (D : ℝ) * d ≤ (D : ℝ) ^ 2 := by
      exact_mod_cast (show D * d ≤ D ^ 2 by simpa only [pow_two] using h₁)
    have h₂R : (D : ℝ) ^ 2 ≤ (2 * (L : ℝ) * t) ^ 2 := by exact_mod_cast h₂
    nlinarith only [h₁R, h₂R]
  let c : ℝ := 1 / (32 * (L : ℝ) ^ 2)
  have hgauss : c * D ≤ (t : ℝ) ^ 2 / (8 * d) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      c * D * (8 * d) = ((D : ℝ) * d) / (4 * (L : ℝ) ^ 2) := by
        dsimp only [c]
        field_simp
        ring
      _ ≤ (t : ℝ) ^ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hraw])
  have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith only [h]
  have hgeo : c * D ≤ (t : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hLsq htR
    have hid : c * D = (D : ℝ) / (32 * (L : ℝ) ^ 2) := by dsimp only [c]; ring
    rw [hid]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hDtR, hm]
  constructor
  · apply Real.exp_le_exp.mpr
    change -(t : ℝ) ^ 2 / (8 * d) ≤ -c * D
    rw [neg_div]
    linarith only [hgauss]
  · calc
      (1 / 2 : ℝ) ^ (t + 1) ≤ Real.exp (-(1 / 2 : ℝ)) ^ (t + 1) :=
        pow_le_pow_left₀ (by norm_num) half_le_exp_neg_half _
      _ = Real.exp (-((t : ℝ) + 1) / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change -((t : ℝ) + 1) / 2 ≤ -c * D
        linarith only [hgeo]

theorem exists_diluted_tail_budget (L : ℕ) (hL : 16 ≤ L) :
    ∃ N : ℕ, 2 * L ≤ N ∧ ∀ D : ℕ, N ≤ D → ∀ d : ℕ, 0 < d → d ≤ D →
      ((4 * (D + 1) ^ 4 : ℕ) : ℝ) *
        (Real.exp (-((D / L : ℕ) : ℝ) ^ 2 / (8 * d)) + (1 / 2 : ℝ) ^ (D / L + 1)) ≤ 1 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  let c : ℝ := 1 / (32 * (L : ℝ) ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨N₀, hN₀⟩ := Erdos76.PippengerSpencerParameters.exists_exp_tail_mul_polynomial_le_one c 64 4 hc
  refine ⟨max N₀ (2 * L), le_max_right _ _, ?_⟩
  intro D hD d hd hdD
  have hD₂ : 2 * L ≤ D := (le_max_right _ _).trans hD
  have hDpos : 0 < D := by omega
  have hDt := (diluted_basic_parameters D L hL hD₂).2.2.2.2.2
  obtain ⟨hgauss, hgeo⟩ := diluted_exponents_bounded L D (D / L) d (by omega) hd hdD hDt
  have hpoly : (D + 1 : ℝ) ^ 4 ≤ 16 * (D : ℝ) ^ 4 := by
    have h : (D : ℝ) + 1 ≤ 2 * D := by exact_mod_cast (show D + 1 ≤ 2 * D by omega)
    have hp := pow_le_pow_left₀ (by positivity) h 4
    nlinarith only [hp]
  calc
    _ ≤ (4 * ((D : ℝ) + 1) ^ 4) * (2 * Real.exp (-c * D)) := by
      push_cast
      have hs := add_le_add hgauss hgeo
      change _ + _ ≤ Real.exp (-c * D) + Real.exp (-c * D) at hs
      nlinarith only [mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * ((D : ℝ) + 1) ^ 4 by positivity)]
    _ ≤ 2 * Real.exp (-c * D) * (64 * (D : ℝ) ^ 4 + 1) := by
      have hm := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (-c * D))
      nlinarith only [hm, Real.exp_nonneg (-c * D)]
    _ ≤ 1 := hN₀ D ((le_max_left _ _).trans hD)

#print axioms exists_diluted_tail_budget

end Erdos19
