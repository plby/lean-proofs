import ErdosProblems.Erdos4.ChebyshevIntervals

/-! A fixed enlargement of the prime frontier pays for any fixed cleanup constant. -/

namespace Erdos4.FGKMT

open Filter ChebyshevIntervals

theorem exists_growing_reserve (D : ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ x : ℕ in atTop,
      D * x / Real.log (x : ℝ) ≤ ((primeInterval x (K * x)).card : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨h, hh⟩ := exists_nat_gt (max 1 (2 * D / Real.log 2))
  have hhR : (1 : ℝ) < h := (le_max_left _ _).trans_lt hh
  have hh1 : 1 ≤ h := by exact_mod_cast hhR.le
  have hbudget : D ≤ Real.log 2 * h / 2 := by
    have hdiv : 2 * D / Real.log 2 < h := (le_max_right _ _).trans_lt hh
    have hm := (div_lt_iff₀ hlog2).mp hdiv
    nlinarith
  refine ⟨16 * h, by omega, ?_⟩
  have hnx : ∀ x : ℕ, x ≤ h * x := by
    intro x
    simpa only [one_mul] using Nat.mul_le_mul_right x hh1
  have htendsto : Tendsto (fun x : ℕ => h * x) atTop atTop :=
    tendsto_atTop_mono hnx tendsto_id
  filter_upwards [htendsto.eventually eventually_primeInterval_lower,
    eventually_ge_atTop (max 2 h)] with x hsupply hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hhx : h ≤ x := (le_max_right _ _).trans hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  have hn2 : 2 ≤ h * x := hx2.trans (hnx x)
  have hnpos : (0 : ℝ) < (h * x : ℕ) := by exact_mod_cast (show 0 < h * x by omega)
  have hlogn : 0 < Real.log (h * x : ℕ) := Real.log_pos (by exact_mod_cast hn2)
  have harg : ((h * x : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 := by
    exact_mod_cast (by simpa only [pow_two] using Nat.mul_le_mul_right x hhx)
  have hlogupper : Real.log (h * x : ℕ) ≤ 2 * Real.log (x : ℝ) := by
    have hm := Real.log_le_log hnpos harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using hm
  have hsub : primeInterval (h * x) (16 * (h * x)) ⊆ primeInterval x ((16 * h) * x) := by
    intro p hp
    obtain ⟨hpprime, hplow, hphigh⟩ := mem_primeInterval.mp hp
    exact mem_primeInterval.mpr ⟨hpprime, (hnx x).trans_lt hplow,
      by simpa only [Nat.mul_assoc] using hphigh⟩
  calc
    _ ≤ (Real.log 2 * h / 2) * x / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hxpos.le) hLpos.le
    _ = Real.log 2 * (h * x : ℕ) / (2 * Real.log (x : ℝ)) := by push_cast; ring
    _ ≤ Real.log 2 * (h * x : ℕ) / Real.log (h * x : ℕ) :=
      div_le_div_of_nonneg_left (mul_nonneg hlog2.le hnpos.le) hlogn hlogupper
    _ ≤ ((primeInterval (h * x) (16 * (h * x))).card : ℝ) := hsupply.2
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end Erdos4.FGKMT
