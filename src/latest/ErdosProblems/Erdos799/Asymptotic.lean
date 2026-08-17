/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1037
import Util.Ramsey

/-!
# A sublinear diagonal Ramsey bound

For a graph on `n` vertices with no clique of size `Erdos1037.r_val n`, the
list-colouring argument for Erdős Problem 799 produces, for every positive
integer `q`, the bound

`n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1`.

This file proves that the infimum of those bounds is `o(n)`.  Only the
elementary fixed-`q` Ramsey estimate `R(h,q) ≤ (h+q)^q` is needed.
-/

open Filter Real Set
open scoped Topology

namespace Erdos799

/-- The logarithmic clique threshold `Erdos1037.r_val` is eventually positive. -/
lemma r_val_eventually_one_le :
    Filter.Eventually (fun n ↦ 1 ≤ Erdos1037.r_val n) atTop := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hlogb : 0 < Real.logb (2 : ℝ) (n : ℝ) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < n by omega))
  simpa [Erdos1037.r_val] using
    (Nat.ceil_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 3) hlogb))

/-- The logarithmic clique threshold is `O(log n)`. -/
lemma r_val_isBigO_log :
    (fun n : ℕ ↦ (Erdos1037.r_val n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2half : (1 : ℝ) / 2 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hdiv : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ hlog2pos]
    have hfac : 0 ≤ 2 * Real.log 2 - 1 := by linarith
    nlinarith [mul_nonneg hlogn0 hfac]
  have hlogb0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    (Real.logb_pos (by norm_num) (by exact_mod_cast hn)).le
  have hceil :=
    Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hlogb0)
  have hloglower : (1 : ℝ) ≤ 2 * Real.log n := by
    have : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) hnreal
    linarith
  have hrle : (Erdos1037.r_val n : ℝ) ≤ 8 * Real.log n := by
    have hceil' :
        (Nat.ceil (3 * Real.logb 2 (n : ℝ)) : ℝ) <
          3 * (Real.log (n : ℝ) / Real.log 2) + 1 := by
      simpa [Real.logb] using hceil
    have hx :
        3 * (Real.log (n : ℝ) / Real.log 2) ≤ 6 * Real.log n := by
      calc
        3 * (Real.log (n : ℝ) / Real.log 2) ≤ 3 * (2 * Real.log n) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 3)
        _ = 6 * Real.log n := by ring
    rw [Erdos1037.r_val]
    nlinarith
  change |(Erdos1037.r_val n : ℝ)| ≤ 8 * |Real.log (n : ℝ)|
  rw [abs_of_nonneg (by positivity), abs_of_nonneg hlogn0]
  exact hrle

/-- An elementary polynomial bound on a Ramsey number when its second
parameter is fixed. -/
lemma ramseyNumber_le_add_pow {h q : ℕ} (hh : 1 ≤ h) (hq : 1 ≤ q) :
    Ramsey.ramseyNumber h q ≤ (h + q) ^ q := by
  have hr := Ramsey.ramseyNumber_le_choose (h - 1) q
  have hh' : h - 1 + 1 = h := by omega
  rw [hh'] at hr
  calc
    Ramsey.ramseyNumber h q
        ≤ Nat.choose (h - 1 + q - 1) (h - 1) := hr
    _ = Nat.choose (h - 1 + (q - 1)) (q - 1) := by
      rw [show h - 1 + q - 1 = (h - 1) + (q - 1) by omega,
        Nat.choose_symm_add]
    _ ≤ (h - 1 + (q - 1)) ^ (q - 1) := Nat.choose_le_pow _ _
    _ ≤ (h + q) ^ q := by
      gcongr <;> omega

/-- If `h = O(log n)`, then for each fixed positive `q`, `R(h(n),q) = o(n)`. -/
lemma ramsey_remainder_isLittleO (h : ℕ → ℕ) (q : ℕ) (hq : 0 < q)
    (hhpos : Filter.Eventually (fun n ↦ 1 ≤ h n) atTop)
    (hhlog : (fun n : ℕ ↦ (h n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ))) :
    (fun n : ℕ ↦ (Ramsey.ramseyNumber (h n) q : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hconst : (fun _n : ℕ ↦ (q : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) :=
    (Real.isLittleO_const_log_atTop (c := (q : ℝ))).natCast_atTop.isBigO
  have hadd : (fun n : ℕ ↦ (h n : ℝ) + q) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := hhlog.add hconst
  have hpowO : (fun n : ℕ ↦ ((h n : ℝ) + q) ^ q) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ q) := hadd.pow q
  have hlogpow : (fun n : ℕ ↦ Real.log (n : ℝ) ^ q) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.natCast_atTop
  have hmajor : (fun n : ℕ ↦ ((h n : ℝ) + q) ^ q) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := hpowO.trans_isLittleO hlogpow
  have hdomO :
      (fun n : ℕ ↦ (Ramsey.ramseyNumber (h n) q : ℝ)) =O[atTop]
        (fun n : ℕ ↦ ((h n : ℝ) + q) ^ q) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hhpos] with n hn
    have hnonneg₁ : (0 : ℝ) ≤ Ramsey.ramseyNumber (h n) q := by positivity
    have hnonneg₂ : (0 : ℝ) ≤ ((h n : ℝ) + q) ^ q := by positivity
    change |(Ramsey.ramseyNumber (h n) q : ℝ)| ≤
      1 * |((h n : ℝ) + q) ^ q|
    rw [one_mul, abs_of_nonneg hnonneg₁, abs_of_nonneg hnonneg₂]
    exact_mod_cast ramseyNumber_le_add_pow hn hq
  exact hdomO.trans_isLittleO hmajor

/-- The smallest of the list-colouring bounds obtained by choosing a positive
independent-set size `q`. -/
noncomputable def ramseyDiagonalBound (n : ℕ) : ℕ :=
  sInf {b : ℕ | ∃ q : ℕ, 0 < q ∧
    b = n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1}

/-- The diagonal bound is at most the expression obtained from any positive
fixed value of `q`. -/
lemma ramseyDiagonalBound_le (n q : ℕ) (hq : 0 < q) :
    ramseyDiagonalBound n ≤
      n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1 := by
  apply Nat.sInf_le
  exact ⟨q, hq, rfl⟩

/-- The diagonal Ramsey bound is sublinear. -/
theorem ramseyDiagonalBound_isLittleO :
    (fun n : ℕ ↦ (ramseyDiagonalBound n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨q, hq⟩ := exists_nat_gt (3 / c)
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := lt_trans (div_pos (by norm_num) hc) hq
    exact_mod_cast this
  have hqsmall : (1 : ℝ) / q < c / 3 := by
    have hthree : (3 : ℝ) < c * q := by
      simpa [mul_comm] using (div_lt_iff₀ hc).mp hq
    rw [div_lt_iff₀ (show (0 : ℝ) < q by exact_mod_cast hqpos)]
    nlinarith
  have hrem :=
    (ramsey_remainder_isLittleO Erdos1037.r_val q hqpos
      r_val_eventually_one_le r_val_isBigO_log).def
      (show 0 < c / 3 by positivity)
  have hone :=
    ((Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop).def
      (show 0 < c / 3 by positivity)
  filter_upwards [hrem, hone] with n hn hone
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hbnonneg : (0 : ℝ) ≤ ramseyDiagonalBound n := by positivity
  have hrnonneg :
      (0 : ℝ) ≤ Ramsey.ramseyNumber (Erdos1037.r_val n) q := by
    positivity
  have hr :
      (Ramsey.ramseyNumber (Erdos1037.r_val n) q : ℝ) ≤ c / 3 * n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hrnonneg,
      abs_of_nonneg hnnonneg] using hn
  have hone' : (1 : ℝ) ≤ c / 3 * n := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnnonneg] using hone
  have hfirst : ((n / q : ℕ) : ℝ) ≤ c / 3 * n := by
    calc
      ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / q := Nat.cast_div_le
      _ = (1 / (q : ℝ)) * n := by ring
      _ ≤ (c / 3) * n :=
        mul_le_mul_of_nonneg_right hqsmall.le hnnonneg
  have hb : (ramseyDiagonalBound n : ℝ) ≤ c * n := by
    calc
      (ramseyDiagonalBound n : ℝ)
          ≤ (n / q + Ramsey.ramseyNumber (Erdos1037.r_val n) q + 1 : ℕ) := by
            exact_mod_cast ramseyDiagonalBound_le n q hqpos
      _ = ((n / q : ℕ) : ℝ) +
            (Ramsey.ramseyNumber (Erdos1037.r_val n) q : ℝ) + 1 := by
        norm_num
      _ ≤ c / 3 * n + c / 3 * n + c / 3 * n :=
        add_le_add (add_le_add hfirst hr) hone'
      _ = c * n := by ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg hbnonneg,
    abs_of_nonneg hnnonneg] using hb

end Erdos799
