import ErdosProblems.Erdos421.CanonicalUpperSieve
import ErdosProblems.Erdos421.BuchstabSieveBounds
import ErdosProblems.Erdos421.RoughRankinMass

/-! # An unconditional lower sieve with a relative main-term error -/

namespace Erdos421

noncomputable def canonicalLowerValue (D z n : ℕ) : ℝ :=
  buchstabLowerValue z (fun p ↦ canonicalUpperSieve D p) n

noncomputable def canonicalLowerMain (D z : ℕ) : ℝ :=
  1 - ∑ p ∈ sievePrimes 0 z, canonicalUpperMain D p / (p : ℝ)

theorem canonicalLowerValue_le {D : ℕ} (hD : 1 ≤ D) (z n : ℕ) :
    canonicalLowerValue D z n ≤ roughIndicator n z :=
  buchstabLowerValue_le_roughIndicator z _ (fun p _ ↦ canonicalUpperSieve_isUpper hD p) n

theorem canonicalLowerMain_ge_exp_error {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    (hlevel : 16 * Real.exp 1 + 33 ≤ Real.log D / Real.log z) :
    (1 - 32 * Real.exp (16 * Real.exp 1 + 32 - Real.log D / Real.log z)) *
      roughEulerProduct z ≤ canonicalLowerMain D z := by
  have hzlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hDlog : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  have hepos := Real.exp_pos 1
  have hterm (p : ℕ) (hp : p ∈ sievePrimes 0 z) :
      canonicalUpperMain D p / (p : ℝ) ≤ roughEulerProduct p / (p : ℝ) +
        (2 * Real.exp (16 * Real.exp 1)) *
          (roughEulerProduct p / (p : ℝ) * Real.exp (-Real.log D / Real.log p)) := by
    have hprime := (Finset.mem_filter.mp hp).2
    have hpz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le
    have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have hratio : Real.log D / Real.log (z : ℝ) ≤ Real.log D / Real.log (p : ℝ) :=
      div_le_div_of_nonneg_left hDlog hplog
        (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpz))
    have hb := canonicalUpperMain_le_level_error hD hprime.two_le (by linarith)
    apply (div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)).trans
    have hexp : Real.exp (16 * Real.exp 1 - Real.log D / Real.log p) =
        Real.exp (16 * Real.exp 1) * Real.exp (-Real.log D / Real.log p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    exact le_of_eq (by ring)
  have hsum : (∑ p ∈ sievePrimes 0 z, canonicalUpperMain D p / (p : ℝ)) ≤
      1 - roughEulerProduct z +
        32 * Real.exp (16 * Real.exp 1 + 32 - Real.log D / Real.log z) * roughEulerProduct z := by
    calc
      _ ≤ ∑ p ∈ sievePrimes 0 z, (roughEulerProduct p / (p : ℝ) +
          (2 * Real.exp (16 * Real.exp 1)) *
            (roughEulerProduct p / (p : ℝ) * Real.exp (-Real.log D / Real.log p))) :=
        Finset.sum_le_sum hterm
      _ = 1 - roughEulerProduct z + (2 * Real.exp (16 * Real.exp 1)) *
          ∑ p ∈ sievePrimes 0 z,
            roughEulerProduct p / (p : ℝ) * Real.exp (-Real.log D / Real.log p) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, roughEulerProduct_prefix]
      _ ≤ 1 - roughEulerProduct z + (2 * Real.exp (16 * Real.exp 1)) *
          (16 * roughEulerProduct z * Real.exp (32 - Real.log D / Real.log z)) := by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left (rough_rankin_mass_le hz (by linarith)) (by positivity)
      _ = _ := by
        rw [show 16 * Real.exp 1 + 32 - Real.log D / Real.log z =
          16 * Real.exp 1 + (32 - Real.log D / Real.log z) by ring, Real.exp_add]
        ring
  unfold canonicalLowerMain
  linarith

theorem canonicalLowerMain_ge_one_sub {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z) :
    (1 - ε) * roughEulerProduct z ≤ canonicalLowerMain D z := by
  have hfrac : 1 ≤ 32 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hlog := Real.log_nonneg hfrac
  have he : 32 * Real.exp (16 * Real.exp 1 + 32 - Real.log D / Real.log z) ≤ ε := by
    calc
      _ ≤ 32 * Real.exp (-Real.log (32 / ε)) := by
        gcongr
        linarith
      _ = ε := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  apply le_trans _ (canonicalLowerMain_ge_exp_error hD hz (by linarith))
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) (roughEulerProduct_pos z).le

end Erdos421
