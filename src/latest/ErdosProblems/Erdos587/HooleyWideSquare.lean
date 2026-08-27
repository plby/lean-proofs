import ErdosProblems.Erdos587.HooleyWideMain
import ErdosProblems.Erdos587.HooleyWideComparison
import ErdosProblems.Erdos587.HooleyCriticalSquare

/-! # A positive square in the power-separated terminal rectangle -/

open Filter
open scoped SchwartzMap

namespace Erdos587

theorem exists_delta_wide_square_of_main_budgets (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a b t u v H J : ℕ, 0 < v → 0 < H → H ≤ v →
      a * u = b * v + 1 → u.Coprime v →
      (t : ℝ) + u * H + v * J ≤ T → (u : ℝ) * H ≤ v * J →
      T ≤ C₀ * ((u : ℝ) * H + v * J) →
      (v : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) → A * Real.sqrt v ≤ H →
      (v : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨F, hF, hweights⟩ := exists_finite_critical_root_weights hC₀
  obtain ⟨A, hA, C, hC, hmain⟩ := exists_delta_periodic_main_plateau C₀ hC₀
  obtain ⟨E, hE, herror⟩ := exists_delta_finite_wide_count_comparison F physicalSquareWeight
  refine ⟨A, hA, ?_⟩
  filter_upwards [herror, eventually_delta_wide_cutoff_error_budget (E * C) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with T herr hcut hT1
  intro a b t u v H J hv hH hHv hab huv hambient horient hspan hvhi hHden hbudget
  have hT : 0 < T := by linarith
  have hL : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hupper : (t : ℝ) + u * H + v * J ≤ (Real.sqrt T) ^ 2 := by rwa [hsq]
  obtain ⟨f, hfF, hfsupp, hfplateau⟩ := hweights t ((u : ℝ) * H) ((v : ℝ) * J)
    (Real.sqrt T) (Nat.cast_nonneg _) (by positivity) (by positivity) hL horient hupper
    (by rwa [hsq])
  obtain ⟨hfreal, hfpos, _hfone⟩ := hF f hfF
  have hfpl : ∀ z : ℝ, 0 ≤ z →
      (t : ℝ) + v * J / 8 + 5 * ((u : ℝ) * H) / 32 ≤ z ^ 2 →
      z ^ 2 ≤ t + (v : ℝ) * J / 2 + 7 * ((u : ℝ) * H) / 32 →
      1 ≤ (f ((Real.sqrt T)⁻¹ * z)).re := by
    intro z hz hzlo hzhi
    rw [hfplateau z hz hzlo hzhi]
    norm_num
  have hgpl : ∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (physicalSquareWeight x).re := by
    intro x hx
    rw [physicalSquareWeight_plateau hx]
    norm_num
  have hmainT := hmain f physicalSquareWeight a u b v H J t v (Real.sqrt T)
    hv hab huv le_rfl hHden hL horient hupper (by rwa [hsq])
    hfreal hfpos physicalSquareWeight_nonneg hfpl hgpl
  have hva : v.Coprime a := by
    have hh : v.Coprime (a * u) := by
      rw [hab, Nat.mul_comm b v, Nat.coprime_mul_left_add_right]
      exact Nat.coprime_one_right v
    exact hh.of_dvd_right (dvd_mul_right a u)
  have hvT : (v : ℝ) ≤ T := by
    apply hvhi.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show (3 / 4 - 1 / 1000 : ℝ) ≤ 1 by norm_num)
  let Λ := max 1 (Real.log (Real.log T))
  let Λv := max 1 (Real.log (Real.log (v : ℝ)))
  let σ := ((v : ℝ) / H)⁻¹
  let M := ⌊T ^ (1 / 4 : ℝ) / Λ ^ 6⌋₊
  have hlogs : Λv ≤ Λ := delta_loglog_nat_real_mono hvT
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hσ : 0 < σ := inv_pos.mpr (div_pos hvR hHR)
  have hdenpos : 0 < C * v * Λv := by dsimp [Λv]; positivity
  have hdominates : E * σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4 <
      Real.sqrt T * H / (C * v * Λv) := by
    apply (lt_div_iff₀ hdenpos).mpr
    calc
      _ ≤ (E * σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4) * (C * v * Λ) := by gcongr
      _ = ((E * C) * M * Λ ^ 5) * (Real.sqrt (Real.sqrt T) * H) := by
        dsimp only [σ]
        rw [inv_div]
        field_simp
      _ < Real.sqrt (Real.sqrt T) * (Real.sqrt (Real.sqrt T) * H) :=
        mul_lt_mul_of_pos_right hcut (by positivity)
      _ = Real.sqrt T * H := by
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Real.sqrt_nonneg T)]
  have herrT := herr f hfF a v H t hv hH hHv hva hvhi hbudget
  have hcount := ne_zero_of_norm_sub_lt_re (herrT.trans_lt (hdominates.trans_le hmainT))
  apply positive_square_of_supported_count f physicalSquareWeight hv hH hab t
    (Real.sqrt T) _ _ hcount
  · intro x hx
    obtain ⟨hlo, hhi⟩ := physicalSquareWeight_support hx
    exact ⟨by linarith, hhi.le⟩
  · intro z hz
    obtain ⟨hzpos, hzlo, hzhi⟩ := hfsupp (z : ℝ) hz
    exact ⟨by exact_mod_cast hzpos, hzlo, hzhi⟩

end Erdos587
