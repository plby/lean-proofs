import ErdosProblems.Erdos4.TiltedParameters

/-! Disjoint fixed-ratio prime intervals provide the composite colors and final cleanup reserve. -/

namespace Erdos4.Tilted

open Filter ChebyshevIntervals

theorem mem_compositeColors {x p : ℕ} : p ∈ compositeColors x ↔ p.Prime ∧ x < p ∧ p ≤ 16 * x :=
  mem_primeInterval

theorem mem_reserveColors {x p : ℕ} : p ∈ reserveColors x ↔ p.Prime ∧ 16 * x < p ∧ p ≤ 256 * x :=
  mem_primeInterval

theorem composite_reserve_disjoint (x : ℕ) : Disjoint (compositeColors x) (reserveColors x) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hh := mem_compositeColors.mp hp
  have hq' := mem_reserveColors.mp hq
  omega

theorem eventually_color_supply :
    ∀ᶠ x : ℕ in atTop,
      0 < (compositeColors x).card ∧
      Real.log 2 * (x : ℝ) / Real.log (x : ℝ) ≤ ((compositeColors x).card : ℝ) ∧
      1 / ((compositeColors x).card : ℝ) ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x ∧
      Real.log 2 * (x : ℝ) / Real.log (x : ℝ) ≤ ((reserveColors x).card : ℝ) := by
  have hmul : Tendsto (fun x : ℕ => 16 * x) atTop atTop :=
    tendsto_atTop_mono (fun x => by omega : ∀ x : ℕ, x ≤ 16 * x) tendsto_id
  filter_upwards [eventually_primeInterval_lower, hmul.eventually eventually_primeInterval_lower,
    log_tendsto.eventually (eventually_ge_atTop (1 / Real.log 2))]
    with x hcomp hreserve hL
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcount : Real.log 2 * (x : ℝ) / Real.log (x : ℝ) ≤ ((compositeColors x).card : ℝ) := hcomp.2
  have hcardpos : (0 : ℝ) < (compositeColors x).card := (by positivity : 0 < Real.log 2 * (x : ℝ) / Real.log (x : ℝ)).trans_le hcount
  have hinv : 1 / ((compositeColors x).card : ℝ) ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x := by
    calc
      _ ≤ 1 / (Real.log 2 * (x : ℝ) / Real.log (x : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hcount
      _ = (1 / Real.log 2) * Real.log (x : ℝ) / x := by field_simp
      _ ≤ Real.log (x : ℝ) * Real.log (x : ℝ) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hlogx.le) hxpos.le
      _ = _ := by ring
  have hlogN : 0 < Real.log (16 * x : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < 16 * x by omega))
  have hlogle : Real.log (16 * x : ℕ) ≤ 2 * Real.log (x : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hxpos.ne']
    have hh : Real.log 16 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by exact_mod_cast hcomp.1)
    linarith
  have hres : Real.log 2 * (x : ℝ) / Real.log (x : ℝ) ≤ ((reserveColors x).card : ℝ) := by
    calc
      _ ≤ 8 * Real.log 2 * (x : ℝ) / Real.log (x : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogx.le
        nlinarith [mul_pos hlog2 hxpos]
      _ = Real.log 2 * ((16 * x : ℕ) : ℝ) / (2 * Real.log (x : ℝ)) := by push_cast; ring
      _ ≤ Real.log 2 * ((16 * x : ℕ) : ℝ) / Real.log (16 * x : ℕ) :=
        div_le_div_of_nonneg_left (by positivity) hlogN hlogle
      _ ≤ _ := by simpa only [reserveColors, ← Nat.mul_assoc, show (16 : ℕ) * 16 = 256 by norm_num] using hreserve.2
  exact ⟨by exact_mod_cast hcardpos, hcount, hinv, hres⟩

end Erdos4.Tilted
