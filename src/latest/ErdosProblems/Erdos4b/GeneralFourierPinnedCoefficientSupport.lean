/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceBounds

/-!
# Pinned coordinates of the literal source coefficient

Nonzero coefficients have positive squarefree coordinates. Their
individual companion support is at most `Y`, even when the product
support is as large as `Y^K`. Residual coprimality then forces each
pinned companion coordinate to be one.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sourceAnalyticSelbergCoefficient_nonzero_squarefree
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (LD LE : ℝ) (d e : ι → ℕ)
    (hne : sourceAnalyticSelbergCoefficient S F G LD LE d e ≠ 0) :
    ∀ i, Squarefree (d i) ∧ Squarefree (e i) := by
  have hmu := (mul_ne_zero_iff.mp hne).1
  intro i
  have hi := mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hmu) i (Finset.mem_univ i))
  constructor
  · apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    exact_mod_cast hi.1
  · apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    exact_mod_cast hi.2

theorem sourceAnalyticSelbergCoefficient_nonzero_profiles
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (LD LE : ℝ) (d e : ι → ℕ)
    (hne : sourceAnalyticSelbergCoefficient S F G LD LE d e ≠ 0) :
    ∃ j ∈ S, ∀ i,
      F j i (Real.log (d i) / LD) ≠ 0 ∧ G (Real.log (e i) / LE) ≠ 0 := by
  obtain ⟨j, hj, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hne).2
  exact ⟨j, hj, fun i ↦
    mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))⟩

theorem sourceAnalyticSelbergCoefficient_first_coordinate_lt
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    {LD LE : ℝ} (hLD : 0 < LD)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    {p₀ : ℕ} (hp₀ : 0 < p₀) (hD : LD / 10 < Real.log p₀)
    (d e : ι → ℕ) (hne : sourceAnalyticSelbergCoefficient S F G LD LE d e ≠ 0) :
    ∀ i, d i < p₀ := by
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD LE d e hne
  obtain ⟨j, hj, hprofiles⟩ := sourceAnalyticSelbergCoefficient_nonzero_profiles S F G LD LE d e hne
  intro i
  have hd : 0 < d i := (hsq i).1.ne_zero.bot_lt
  have hdi : (0 : ℝ) < d i := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log (d i) := Real.log_nonneg (by exact_mod_cast hd)
  have hs := hFsupport j hj i _ (div_nonneg hlog0 hLD.le) (hprofiles i).1
  have hbound := (div_le_iff₀ hLD).mp hs
  have hlt : Real.log (d i) < Real.log p₀ := by linarith
  exact_mod_cast (Real.log_lt_log_iff hdi (by exact_mod_cast hp₀)).mp hlt

theorem sourceAnalyticSelbergCoefficient_companion_coordinate_le
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (LD : ℝ) {Y : ℕ} (hY : 1 < Y)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (d e : ι → ℕ)
    (hne : sourceAnalyticSelbergCoefficient S F G LD (Real.log Y) d e ≠ 0) :
    ∀ i, e i ≤ Y := by
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD (Real.log Y) d e hne
  obtain ⟨j, hj, hprofiles⟩ :=
    sourceAnalyticSelbergCoefficient_nonzero_profiles S F G LD (Real.log Y) d e hne
  have hYR : (1 : ℝ) < Y := by exact_mod_cast hY
  have hLE : 0 < Real.log Y := Real.log_pos hYR
  intro i
  have he : 0 < e i := (hsq i).2.ne_zero.bot_lt
  have hei : (0 : ℝ) < e i := by exact_mod_cast he
  have hlog0 : 0 ≤ Real.log (e i) := Real.log_nonneg (by exact_mod_cast he)
  have hs := hGsupport _ (div_nonneg hlog0 hLE.le) (hprofiles i).2
  have hbound : Real.log (e i) ≤ Real.log Y := by
    simpa only [one_mul] using (div_le_iff₀ hLE).mp hs
  exact_mod_cast (Real.log_le_log_iff hei (zero_lt_one.trans hYR)).mp hbound

theorem sourceAnalyticSelbergCoefficient_pinned_coordinates_eq_one
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    {LD : ℝ} (hLD : 0 < LD) {Y m p₀ : ℕ} (hY : 1 < Y) (hp₀ : p₀.Prime)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hD : LD / 10 < Real.log p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d e : ι → ℕ)
    (hne : sourceAnalyticSelbergCoefficient S F G LD (Real.log Y) d e ≠ 0)
    (h : ι) (hd : d h ∣ p₀) (he : e h ∣ m * p₀ - 1) : d h = 1 ∧ e h = 1 := by
  have hsmall := sourceAnalyticSelbergCoefficient_first_coordinate_lt
    S F G hLD hFsupport hp₀.pos hD d e hne h
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD (Real.log Y) d e hne
  have hbound := sourceAnalyticSelbergCoefficient_companion_coordinate_le
    S F G LD hY hGsupport d e hne h
  constructor
  · exact (hp₀.eq_one_or_self_of_dvd (d h) hd).resolve_right (ne_of_lt hsmall)
  · exact Nat.eq_one_of_dvd_coprimes hcop he
      ((hsq h).2.dvd_primorial.trans (primorial_dvd_primorial hbound))

end

end Erdos4b
