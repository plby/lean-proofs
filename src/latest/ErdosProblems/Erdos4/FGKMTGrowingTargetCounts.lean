import ErdosProblems.Erdos4.FGKMTInitialScaleBudget
import ErdosProblems.Erdos4.ChebyshevIntervals

/-! Uniform target-prime counts and conversion of arithmetic exceptional sets to vertex subsets. -/

namespace Erdos4.FGKMT

open Filter Classical ChebyshevIntervals

noncomputable def targetBadSubset (targets bad : Finset ℕ) : Finset targets :=
  Finset.univ.filter (fun q : targets => q.val ∈ bad)

theorem mem_targetBadSubset (targets bad : Finset ℕ) (q : targets) :
    q ∈ targetBadSubset targets bad ↔ q.val ∈ bad := by
  simp only [targetBadSubset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem targetBadSubset_card_le (targets bad : Finset ℕ) :
    (targetBadSubset targets bad).card ≤ bad.card := by
  have hsub : (targetBadSubset targets bad).image Subtype.val ⊆ bad := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    exact (mem_targetBadSubset targets bad v).mp hv
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem eventually_growing_target_count :
    ∀ᶠ x : ℕ in atTop, ∀ Y : ℕ, x ≤ Y →
      ((primeInterval x Y).card : ℝ) ≤ (3 * Real.log 2) * Y / Real.log (x : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_primeCounting_upper
  filter_upwards [eventually_ge_atTop (max N 2)] with x hx
  intro Y hXY
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  have hlogle : Real.log (x : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hxpos (by exact_mod_cast hXY)
  have hcard : (primeInterval x Y).card ≤ Nat.primeCounting Y := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card Finset.sdiff_subset
  calc
    _ ≤ (Nat.primeCounting Y : ℝ) := by exact_mod_cast hcard
    _ ≤ (3 * Real.log 2) * Y / Real.log (Y : ℝ) := hN Y ((le_max_left _ _).trans (hx.trans hXY))
    _ ≤ _ := div_le_div_of_nonneg_left
      (by have hh := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le; positivity) hlogx hlogle

theorem eventually_growing_count_budgets :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ growingIndex x ∧
      1 ≤ (x : ℝ) / Real.log (x : ℝ) ∧
      1 / Real.log (x : ℝ) ^ (40 : ℕ) ≤ 1 / (growingIndex x : ℝ) ^ (2 : ℕ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growingDimension_bounds,
    growingIndex_tendsto.eventually (eventually_ge_atTop 1),
    hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
    with x hdim hj hL hx
  change 1 ≤ Real.log (x : ℝ) at hL
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast (show 0 < growingIndex x by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hjdim : growingIndex x ≤ sieveDimension (growingIndex x) := (Nat.lt_two_pow_self).le
  have hjL : (growingIndex x : ℝ) ≤ Real.log (x : ℝ) := by
    apply (show (growingIndex x : ℝ) ≤ sieveDimension (growingIndex x) by exact_mod_cast hjdim).trans
    apply hdim.2.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 100 : ℝ) ≤ 1)
  refine ⟨hj, ?_, ?_⟩
  · apply (le_div_iff₀ hLpos).mpr
    have hh := Real.log_le_sub_one_of_pos hxpos
    linarith
  · apply one_div_le_one_div_of_le (pow_pos hjpos 2)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hjL 2).trans
      (pow_le_pow_right₀ hL (by norm_num : 2 ≤ (40 : ℕ)))

end Erdos4.FGKMT
