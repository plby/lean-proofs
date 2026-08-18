import ErdosProblems.Erdos140.Counting
import ErdosProblems.Erdos140.Endpoint

/-!
# Quantitative ordered counting implies the Erdős 140 bound

The Kelley--Meka input is isolated below in the form in which its constants
are used.  A set of density at least `2⁻ᵈ` has at least
`exp (-K d^12) N^2` ordered three-term progressions.  The logarithmic
hypothesis in the definition is the equivalent, division-free-in-the-density
form `log (N / |A|) ≤ d log 2`; nonemptiness makes this equivalence honest.

The proofs in this file are elementary.  They choose an extremal AP-free set,
observe that its ordered progressions are precisely the diagonal ones, and
choose `d = ceil (log (N / |A|) / log 2)`.  Taking logarithms then gives a
stretched-exponential upper bound for `r3`.
-/

open Filter Finset
open scoped Topology

namespace Erdos140

/-- The explicit quantitative ordered-count statement supplied by the
Kelley--Meka theorem (with an absolute constant and a harmless threshold).

The count includes all ordered triples `(a,b,c)` satisfying `a+c=2b`, so the
diagonal solutions are included. -/
def KelleyMekaOrderedCountHypothesis (K : ℝ) (N₀ : ℕ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), N₀ ≤ N →
      ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → A.Nonempty →
        ∀ d : ℕ,
          1 ≤ d →
          Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2 →
            Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤
              (threeAPCount A : ℝ)

/-- The ordered-count hypothesis forces the Kelley--Meka
stretched-exponential bound for the literal extremal function `r3`.

The constants are explicit: the exponent is `1/12`, and the decay constant is
`log 2 / (2 * K^(1/12))`. -/
theorem eventually_r3_le_stretchedExp_of_orderedCount
    {K : ℝ} {N₀ : ℕ} (hKM : KelleyMekaOrderedCountHypothesis K N₀) :
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤
        (N : ℝ) * Real.exp
          (-(Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) := by
  have hK : 0 < K := hKM.1
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) / K) atTop atTop :=
    Tendsto.atTop_div_const hK hlog
  have hroot :
      Tendsto
        (fun N : ℕ => (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hlog_div
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 3,
      hroot.eventually_ge_atTop 2] with N hNN₀ hN hroot_large
  obtain ⟨A, hAIcc, hAcard, hAfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  have hAcard' : #A = r3 N := by simpa [r3] using hAcard
  have hr3_le_nat : r3 N ≤ N := by
    rw [r3_eq_rothNumberNat]
    exact rothNumberNat_le N
  have hr3_pos : 0 < r3 N := by
    have hsingleton : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N := by
      simpa using (show 1 ≤ N by omega)
    have hmono := addRothNumber.mono hsingleton
    have hmono' : 1 ≤ addRothNumber (Finset.Icc 1 N) := by simpa using hmono
    have : 0 < addRothNumber (Finset.Icc 1 N) := by omega
    simpa [r3] using this
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    simpa [hAcard'] using hr3_pos
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hr3_pos_real : (0 : ℝ) < r3 N := by exact_mod_cast hr3_pos
  have hr3_le_real : (r3 N : ℝ) ≤ N := by exact_mod_cast hr3_le_nat
  have hratio_one : (1 : ℝ) ≤ (N : ℝ) / (r3 N : ℝ) := by
    rw [one_le_div hr3_pos_real]
    exact hr3_le_real
  have hratio_pos : (0 : ℝ) < (N : ℝ) / (r3 N : ℝ) :=
    div_pos hN_pos hr3_pos_real
  let q : ℝ := Real.log ((N : ℝ) / (r3 N : ℝ)) / Real.log 2
  let d : ℕ := Nat.ceil q
  have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg (Real.log_nonneg hratio_one) hlog_two.le
  have hlog_density :
      Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2 := by
    rw [hAcard']
    rw [← div_le_iff₀ hlog_two]
    simpa [q, d] using Nat.le_ceil q
  have hr3_lt_nat : r3 N < N := by
    apply lt_of_le_of_ne hr3_le_nat
    intro heq
    have hcard_Icc : #(Finset.Icc 1 N) = N := by
      rw [Nat.card_Icc]
      omega
    have hAeq : A = Finset.Icc 1 N := by
      apply Finset.eq_of_subset_of_card_le hAIcc
      rw [hcard_Icc, hAcard', heq]
    have hfree_Icc : ThreeAPFree (Finset.Icc 1 N : Set ℕ) := by
      simpa [hAeq] using hAfree
    have hbad := hfree_Icc (a := 1) (b := 2) (c := 3)
      (by simp [show 1 ≤ N by omega]) (by simp [show 2 ≤ N by omega])
      (by simp [show 3 ≤ N by omega]) (by norm_num)
    omega
  have hq_pos : 0 < q := by
    have hratio_gt : (1 : ℝ) < (N : ℝ) / (r3 N : ℝ) := by
      rw [lt_div_iff₀ hr3_pos_real]
      norm_num
      exact_mod_cast hr3_lt_nat
    exact div_pos (Real.log_pos hratio_gt) hlog_two
  have hd_one : 1 ≤ d := by
    exact (Nat.ceil_pos.mpr hq_pos)
  have hcount := hKM.2 N hNN₀ A hAIcc hAne d hd_one hlog_density
  rw [threeAPCount_eq_card hAfree, hAcard'] at hcount
  have hcountN :
      Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤ (N : ℝ) :=
    hcount.trans hr3_le_real
  have hdecay_mul_N :
      Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ≤ 1 := by
    have hscaled :
        (Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ)) * (N : ℝ) ≤
          1 * (N : ℝ) := by
      simpa [pow_two, mul_assoc] using hcountN
    exact (le_of_mul_le_mul_right hscaled hN_pos)
  have hlog_bound : Real.log (N : ℝ) ≤ K * (d : ℝ) ^ 12 := by
    have hlog_ineq :=
      Real.log_le_log
        (mul_pos (Real.exp_pos _) hN_pos)
        hdecay_mul_N
    rw [Real.log_mul (Real.exp_ne_zero _) hN_pos.ne', Real.log_exp,
      Real.log_one] at hlog_ineq
    linarith
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hdiv_nonneg : 0 ≤ Real.log (N : ℝ) / K :=
    div_nonneg hlog_nonneg hK.le
  have hdiv_le_pow : Real.log (N : ℝ) / K ≤ (d : ℝ) ^ 12 := by
    rw [div_le_iff₀ hK]
    simpa [mul_comm] using hlog_bound
  have hroot_le_d :
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤ (d : ℝ) := by
    calc
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤
          ((d : ℝ) ^ 12) ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow hdiv_nonneg hdiv_le_pow (by norm_num)
      _ = (d : ℝ) := by
        convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ d by positivity)
          (by norm_num : (12 : ℕ) ≠ 0) using 1
        all_goals norm_num
  have hceil_upper : (d : ℝ) < q + 1 := by
    simpa [d] using Nat.ceil_lt_add_one hq_nonneg
  have hhalf_root_le_q :
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) / 2 ≤ q := by
    linarith
  have hlog_ratio_lower :
      (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤
        Real.log ((N : ℝ) / (r3 N : ℝ)) := by
    calc
      (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) =
          ((Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) / 2) * Real.log 2 := by ring
      _ ≤ q * Real.log 2 :=
        mul_le_mul_of_nonneg_right hhalf_root_le_q hlog_two.le
      _ = Real.log ((N : ℝ) / (r3 N : ℝ)) := by
        simp [q, hlog_two.ne']
  have hKroot_pos : 0 < K ^ (1 / 12 : ℝ) :=
    Real.rpow_pos_of_pos hK _
  have hcoefficient :
      (Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
          (Real.log (N : ℝ)) ^ (1 / 12 : ℝ) =
        (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) := by
    rw [Real.div_rpow hlog_nonneg hK.le]
    field_simp [hKroot_pos.ne']
  have hexp_le_ratio :
      Real.exp
          ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) ≤
        (N : ℝ) / (r3 N : ℝ) := by
    rw [← Real.le_log_iff_exp_le hratio_pos]
    rw [hcoefficient]
    exact hlog_ratio_lower
  have hmul_exp_le :
      (r3 N : ℝ) *
          Real.exp
            ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
              (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) ≤
        (N : ℝ) := by
    have := (le_div_iff₀ hr3_pos_real).mp hexp_le_ratio
    simpa [mul_comm] using this
  calc
    (r3 N : ℝ) ≤
        (N : ℝ) /
          Real.exp
            ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
              (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) :=
      (le_div_iff₀ (Real.exp_pos _)).2 hmul_exp_le
    _ = (N : ℝ) *
        Real.exp
          (-((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ))) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    _ = (N : ℝ) * Real.exp
        (-(Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
          (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) := by
      congr 2
      ring

/-- The ordered-count hypothesis yields every logarithmic saving in the exact
`IsBigO` form used by Erdős Problem 140. -/
theorem isBigO_r3_log_rpow_of_orderedCount
    {K : ℝ} {N₀ : ℕ} (hKM : KelleyMekaOrderedCountHypothesis K N₀)
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  have hc : 0 < Real.log 2 / (2 * K ^ (1 / 12 : ℝ)) := by
    exact div_pos (Real.log_pos (by norm_num))
      (mul_pos two_pos (Real.rpow_pos_of_pos hKM.1 _))
  apply isBigO_r3_log_rpow_of_stretchedExp
      (K := 1) (c := Real.log 2 / (2 * K ^ (1 / 12 : ℝ)))
      (beta := (1 / 12 : ℝ)) zero_le_one hc (by norm_num) _ C
  simpa using eventually_r3_le_stretchedExp_of_orderedCount hKM

#print axioms eventually_r3_le_stretchedExp_of_orderedCount
#print axioms isBigO_r3_log_rpow_of_orderedCount

end Erdos140
