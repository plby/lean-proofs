import ErdosProblems.Erdos587.HooleyCriticalMain
import ErdosProblems.Erdos587.HooleyFiniteComparison
import ErdosProblems.Erdos587.CriticalSquare

/-! # A positive square from the critical log-log main and error budgets -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_loglog_nat_real_mono {u : ℕ} {T : ℝ} (huT : (u : ℝ) ≤ T) :
    max 1 (Real.log (Real.log (u : ℝ))) ≤ max 1 (Real.log (Real.log T)) := by
  by_cases hu : 2 ≤ u
  · apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < u by omega)))
    exact Real.log_le_log (by exact_mod_cast (show 0 < u by omega)) huT
  · have hu' : u = 0 ∨ u = 1 := by omega
    rcases hu' with rfl | rfl <;>
      simpa only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one, max_eq_left zero_le_one]
        using (le_max_left (1 : ℝ) (Real.log (Real.log T)))

lemma delta_rpow_ninth_half_mul_self {F : ℝ} (hF : 0 < F) :
    F ^ (9 / 2 : ℝ) * F = F ^ (11 / 2 : ℝ) := by
  calc
    _ = F ^ (9 / 2 : ℝ) * F ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = F ^ ((9 / 2 : ℝ) + 1) := (Real.rpow_add hF _ _).symm
    _ = _ := by norm_num

theorem exists_delta_critical_square_of_main_budgets (C₀ c₀ : ℝ)
    (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) :
    ∃ A : ℝ, 0 < A ∧ ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a b t u v H J : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
      a * u = b * v + 1 → b.Coprime u → u.Coprime v →
      (t : ℝ) + u * H + v * J ≤ T → (u : ℝ) * H ≤ v * J →
      T ≤ C₀ * ((u : ℝ) * H + v * J) →
      T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
      c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
      Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → A * Real.sqrt u ≤ J →
      K * T ^ (3 / 4 : ℝ) * (max 1 (Real.log (Real.log T))) ^ (11 / 2 : ℝ) < (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨F, hF, hweights⟩ := exists_finite_critical_root_weights hC₀
  obtain ⟨A, hA, C, hC, hmain⟩ := exists_delta_critical_main_plateau
  obtain ⟨E, hE, herror⟩ :=
    exists_delta_finite_critical_count_comparison F physicalSquareWeight c₀ hc₀
  refine ⟨A, hA, E * C, by positivity, ?_⟩
  filter_upwards [herror, eventually_ge_atTop (1 : ℝ)] with T herr hT1
  intro a b t u v H J hu hv hH hHv hab hb huv hambient horient hspan
    hu0 hu1 hv0 hv1 hH0 hJden hprod
  have hT : 0 < T := by linarith
  have hL : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hupper : (t : ℝ) + u * H + v * J ≤ (Real.sqrt T) ^ 2 := by rwa [hsq]
  obtain ⟨f, hfF, hfsupp, hfplateau⟩ := hweights t ((u : ℝ) * H) ((v : ℝ) * J)
    (Real.sqrt T) (Nat.cast_nonneg _) (by positivity) (by positivity) hL horient hupper
    (by rwa [hsq])
  obtain ⟨hfreal, hfpos, _hfone⟩ := hF f hfF
  have hfpl : ∀ z : ℝ, 0 ≤ z →
      (t : ℝ) + v * J / 8 + 5 * (u : ℝ) * H / 32 ≤ z ^ 2 →
      z ^ 2 ≤ t + (v : ℝ) * J / 2 + 7 * (u : ℝ) * H / 32 →
      1 ≤ (f ((Real.sqrt T)⁻¹ * z)).re := by
    intro z hz hzlo hzhi
    have hh := hfplateau z hz (by nlinarith) (by nlinarith)
    rw [hh]
    norm_num
  have hgpl : ∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (physicalSquareWeight x).re := by
    intro x hx
    rw [physicalSquareWeight_plateau hx]
    norm_num
  have hmainT := hmain f physicalSquareWeight a u b v H J t (Real.sqrt T)
    hu hv hH hab huv.symm hL hupper hJden hfreal hfpos physicalSquareWeight_nonneg hfpl hgpl
  have huH : (u : ℝ) * H ≤ T := by
    have ht0 := Nat.cast_nonneg (α := ℝ) t
    have hvJ0 : (0 : ℝ) ≤ v * J := by positivity
    linarith
  have huT : (u : ℝ) ≤ T := by
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    exact (le_mul_of_one_le_right (Nat.cast_nonneg u) hH1).trans huH
  let Λ := max 1 (Real.log (Real.log T))
  let Λu := max 1 (Real.log (Real.log (u : ℝ)))
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  have hlogs : Λu ≤ Λ := delta_loglog_nat_real_mono huT
  have hdenpos : 0 < C * Real.sqrt T * Λu := by dsimp [Λu]; positivity
  have hdominates : E * Real.sqrt (Real.sqrt T) * Λ ^ (9 / 2 : ℝ) <
      (H : ℝ) * J / (C * Real.sqrt T * Λu) := by
    apply (lt_div_iff₀ hdenpos).mpr
    calc
      _ = (E * C) * (Real.sqrt (Real.sqrt T) * Real.sqrt T) *
          (Λ ^ (9 / 2 : ℝ) * Λu) := by ring
      _ ≤ (E * C) * (Real.sqrt (Real.sqrt T) * Real.sqrt T) *
          (Λ ^ (9 / 2 : ℝ) * Λ) := by gcongr
      _ = (E * C) * T ^ (3 / 4 : ℝ) * Λ ^ (11 / 2 : ℝ) := by
        rw [critical_root_scale_product hT, delta_rpow_ninth_half_mul_self hΛ]
      _ < _ := hprod
  have herrT := herr f hfF a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH
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
