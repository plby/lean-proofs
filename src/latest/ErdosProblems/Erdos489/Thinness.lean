import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- A sequence which eventually dominates the squares has summable reciprocals. -/
theorem summable_inv_of_eventually_sq_le (a : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, (n + 1) ^ 2 ≤ a n) :
    Summable (fun n : ℕ => ((a n : ℝ)⁻¹)) := by
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    have hζ : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
      Real.summable_nat_pow_inv.mpr (by omega)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hζ.comp_injective Nat.succ_injective
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [h] with n hn
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have ha : 0 < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (n + 1) ^ 2) hn)
  have hb : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [inv_le_inv₀ ha hb]
  exact_mod_cast hn

/-- Little-o square-root growth of a predicate's counting function forces the
reciprocals of its increasing enumeration to be summable. -/
theorem summable_inv_nth_of_count_isLittleO_sqrt (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Summable (fun n : ℕ => ((Nat.nth p n : ℝ)⁻¹)) := by
  apply summable_inv_of_eventually_sq_le
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc : ∀ᶠ n in atTop,
      ‖(Nat.count p (Nat.nth p n) : ℝ)‖ ≤
        (1 / 2 : ℝ) * ‖Real.sqrt (Nat.nth p n : ℝ)‖ := ht.eventually hb
  filter_upwards [hbc, eventually_ge_atTop 1] with n hn hnpos
  rw [Nat.count_nth_of_infinite hp n] at hn
  have hnreal : (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : (2 : ℝ) * n ≤ Real.sqrt (Nat.nth p n : ℝ) := by
    linarith
  have hsquare : ((2 : ℝ) * n) ^ 2 ≤ (Nat.nth p n : ℝ) := by
    calc
      ((2 : ℝ) * n) ^ 2 ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    norm_num at hsquare ⊢
    nlinarith
  exact_mod_cast hcast

/-- For a predicate false at zero, strict counting through `x+1` is the
inclusive `[1,x]` filtered cardinality used in Erdős 489. -/
lemma count_succ_eq_card_filter_Icc (p : ℕ → Prop) [DecidablePred p]
    (hp0 : ¬p 0) (x : ℕ) :
    Nat.count p (x + 1) = ((Finset.Icc 1 x).filter p).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hnx, hpn⟩
    refine ⟨⟨?_, by omega⟩, hpn⟩
    by_contra hn1
    have : n = 0 := by omega
    exact hp0 (this ▸ hpn)
  · rintro ⟨⟨_, hnx⟩, hpn⟩
    exact ⟨by omega, hpn⟩

/-- The exact inclusive counting hypothesis in Erdős 489 implies summability
of the reciprocal series of the forbidden set (when zero is absent). -/
theorem summable_inv_nth_of_Icc_count_isLittleO_sqrt (p : ℕ → Prop)
    [DecidablePred p] (hp0 : ¬p 0) (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => ((((Finset.Icc 1 x).filter p).card : ℝ)))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Summable (fun n : ℕ => ((Nat.nth p n : ℝ)⁻¹)) := by
  apply summable_inv_of_eventually_sq_le
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc := ht.eventually hb
  filter_upwards [hbc] with n hn
  have hcard : ((Finset.Icc 1 (Nat.nth p n)).filter p).card = n + 1 := by
    rw [← count_succ_eq_card_filter_Icc p hp0]
    exact Nat.count_nth_succ_of_infinite hp n
  rw [hcard] at hn
  have hnreal : ((n + 1 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : (((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (Nat.nth p n : ℝ) := by
    have : (0 : ℝ) ≤ Real.sqrt (Nat.nth p n : ℝ) := Real.sqrt_nonneg _
    linarith
  have hsquare : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    calc
      ((((n + 1) ^ 2 : ℕ) : ℝ)) = (((n + 1 : ℕ) : ℝ)) ^ 2 := by norm_num
      _ ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  exact_mod_cast hsquare

/-- Quantitative form: the square of the enumeration index divided by the
corresponding forbidden integer tends to zero. -/
theorem tendsto_sq_index_div_nth_zero_of_Icc_count_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p] (hp0 : ¬p 0)
    (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => ((((Finset.Icc 1 x).filter p).card : ℝ)))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2) / (Nat.nth p n : ℝ))
      atTop (𝓝 0) := by
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have ho := hcount.comp_tendsto ht
  have traw := ho.tendsto_div_nhds_zero
  have hratio : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / Real.sqrt (Nat.nth p n : ℝ))
      atTop (𝓝 0) := by
    apply traw.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [show ((Finset.Icc 1 (Nat.nth p n)).filter p).card = n + 1 by
      rw [← count_succ_eq_card_filter_Icc p hp0]
      exact Nat.count_nth_succ_of_infinite hp n]
  have hsquared := hratio.pow 2
  convert hsquared using 1
  · funext n
    have hpos : 0 < (Nat.nth p n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (fun hz => hp0 (hz ▸ Nat.nth_mem_of_infinite hp n)))
    rw [div_pow, Real.sq_sqrt hpos.le]
  · norm_num

end Erdos489
