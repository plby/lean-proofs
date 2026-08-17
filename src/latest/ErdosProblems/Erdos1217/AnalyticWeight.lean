/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos164
import ErdosProblems.Erdos1217.Basic

/-!
# The invariant ABLLPSTT weight

This file constructs the measure on the positive integers used in the solution of Erdős
Problem 1217.  In the notation of the paper, for `n > 1` it is

`nuLambda n = ∫ s in (1,∞), log n / (zeta(s) * n^s)`,

while `nuLambda 1 = 1` and `nuLambda 0 = 0`.  The main result is the exact incoming
identity `tsum_incomingWeight`, which is the row-normalisation identity for the adjoint
upward Markov chain.
-/

open scoped Topology
open Set Filter MeasureTheory

noncomputable section

namespace Erdos1217

/-- The reciprocal of the real Dirichlet series for the Riemann zeta function. -/
noncomputable def inverseZeta (s : ℝ) : ℝ := 1 / Erdos164.zetaSeries s

/-- The integrand defining the invariant ABLLPSTT weight. -/
noncomputable def nuLambdaIntegrand (n : ℕ) (s : ℝ) : ℝ :=
  Real.log (n : ℝ) / (Erdos164.zetaSeries s * Real.rpow (n : ℝ) s)

/-- The invariant ABLLPSTT weight.  The exceptional value at `1` is the mass entering from
the pole of zeta at `s = 1`; the value at `0` is set to zero. -/
noncomputable def nuLambda (n : ℕ) : ℝ :=
  if n = 1 then 1
  else if 2 ≤ n then ∫ s in Ioi (1 : ℝ), nuLambdaIntegrand n s
  else 0

/-- The contribution of the multiplier `q` to the incoming mass at `n`. -/
noncomputable def incomingWeight (n q : ℕ) : ℝ :=
  nuLambda (n * q) * ArithmeticFunction.vonMangoldt q /
    Real.log ((n * q : ℕ) : ℝ)

/-- The summed incoming density before integrating in the zeta parameter. -/
noncomputable def incomingIntegrand (n : ℕ) (s : ℝ) : ℝ :=
  (Erdos164.analyticSeries s / Erdos164.zetaSeries s) * Real.rpow (n : ℝ) (-s)

/-- One nonnegative summand of `incomingIntegrand`, indexed by a multiplier at least two. -/
noncomputable def incomingPiece (n : ℕ) (q : {q : ℕ // 2 ≤ q}) (s : ℝ) : ℝ :=
  inverseZeta s * Real.rpow (n : ℝ) (-s) *
    (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) s)

lemma zetaSeries_pos {s : ℝ} (hs : 1 < s) : 0 < Erdos164.zetaSeries s := by
  have h := Erdos164.zetaSeries_ge_one_div_sub_add_one_half hs
  have hsub : 0 < s - 1 := sub_pos.mpr hs
  have : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by positivity
  exact this.trans_le h

lemma zetaSeries_ge_one {s : ℝ} (hs : 1 < s) : 1 ≤ Erdos164.zetaSeries s := by
  rw [Erdos164.zetaSeries]
  have hsum := Erdos164.zetaSeries_term_summable hs
  have hnonneg (k : ℕ) :
      0 ≤ 1 / Real.rpow (((k + 1 : ℕ) : ℝ)) s :=
    one_div_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
  have hle := hsum.sum_le_tsum ({0} : Finset ℕ) (fun k hk ↦ hnonneg k)
  simpa using hle

lemma inverseZeta_nonneg {s : ℝ} (hs : 1 < s) : 0 ≤ inverseZeta s := by
  exact one_div_nonneg.mpr (zetaSeries_pos hs).le

lemma inverseZeta_le_one {s : ℝ} (hs : 1 < s) : inverseZeta s ≤ 1 := by
  simpa [inverseZeta] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (zetaSeries_ge_one hs)

lemma analyticSeries_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ Erdos164.analyticSeries s := by
  rw [Erdos164.analyticSeries]
  exact tsum_nonneg fun q ↦
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity : 0 ≤ (q.1 : ℝ)) _)

lemma inverseZeta_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt inverseZeta
      (Erdos164.analyticSeries s / Erdos164.zetaSeries s) s := by
  have hzpos := zetaSeries_pos hs
  have hz := Erdos164.zetaSeries_hasDerivAt hs
  have hinv := hz.inv hzpos.ne'
  rw [Erdos164.analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries hs]
  unfold inverseZeta
  simp only [one_div]
  have heq :
      (-deriv Erdos164.zetaSeries s / Erdos164.zetaSeries s) /
          Erdos164.zetaSeries s =
        -deriv Erdos164.zetaSeries s / Erdos164.zetaSeries s ^ 2 := by
    field_simp [hzpos.ne']
  rw [heq]
  exact hinv

lemma inverseZeta_deriv_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ Erdos164.analyticSeries s / Erdos164.zetaSeries s := by
  exact div_nonneg (analyticSeries_nonneg hs) (zetaSeries_pos hs).le

@[simp] lemma nuLambda_zero : nuLambda 0 = 0 := by simp [nuLambda]

@[simp] lemma nuLambda_one : nuLambda 1 = 1 := by simp [nuLambda]

lemma nuLambda_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    nuLambda n = ∫ s in Ioi (1 : ℝ), nuLambdaIntegrand n s := by
  simp [nuLambda, hn, ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hn)]

lemma nuLambdaIntegrand_nonneg {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    0 ≤ nuLambdaIntegrand n s := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn)
  exact div_nonneg (Real.log_nonneg hnreal)
    (mul_nonneg (zetaSeries_pos hs).le (Real.rpow_nonneg (by positivity) _))

lemma nuLambdaIntegrand_le_model {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    nuLambdaIntegrand n s ≤
      Real.log (n : ℝ) / Real.rpow (n : ℝ) s := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn))
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hpow : 0 < Real.rpow (n : ℝ) s := Real.rpow_pos_of_pos hnp _
  rw [nuLambdaIntegrand, div_eq_mul_inv, div_eq_mul_inv]
  have hz : 1 ≤ Erdos164.zetaSeries s := zetaSeries_ge_one hs
  have hmul : Real.rpow (n : ℝ) s ≤
      Erdos164.zetaSeries s * Real.rpow (n : ℝ) s := by
    nlinarith [hpow]
  simpa only [one_div] using
    mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpow hmul) hlog

lemma zetaSeries_le_one_add_inv_sub_one {s : ℝ} (hs : 1 < s) :
    Erdos164.zetaSeries s ≤ 1 + 1 / (s - 1) := by
  let f : ℝ → ℝ := fun x ↦ Real.rpow x (-s)
  have hfanti : AntitoneOn f (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (fun x hx ↦ lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hx)
  have hfint : IntegrableOn f (Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hfnonneg : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (le_trans (by norm_num) hx.le) _
  have hfanti' : AntitoneOn f (Ici (((1 : ℕ) : ℝ))) := by simpa using hfanti
  have hfint' : IntegrableOn f (Ioi (((1 : ℕ) : ℝ))) := by simpa using hfint
  have hfnonneg' : ∀ x ∈ Ioi (((1 : ℕ) : ℝ)), 0 ≤ f x := by simpa using hfnonneg
  have htail := hfanti'.tsum_comp_add_le_integral (f := f) 1 hfint' hfnonneg'
  norm_num at htail
  have hint : ∫ x in Ioi (1 : ℝ), f x = 1 / (s - 1) := by
    change ∫ x in Ioi (1 : ℝ), x ^ (-s) = _
    rw [integral_Ioi_rpow_of_lt (a := -s) (c := 1) (by linarith) (by norm_num),
      Real.one_rpow]
    field_simp [show -s + 1 ≠ 0 by linarith, show s - 1 ≠ 0 by linarith]
    ring
  have hsum := Erdos164.zetaSeries_term_summable hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  rw [Erdos164.zetaSeries]
  have hconvert :
      (∑' n : ℕ, 1 / Real.rpow (((n + 1 + 1 : ℕ) : ℝ)) s) =
        ∑' n : ℕ, f (n + 1 + 1 : ℕ) := by
    apply tsum_congr
    intro n
    simp only [f, one_div]
    simpa only [one_div, Real.rpow_eq_pow] using
      (Real.rpow_neg (by positivity : 0 ≤ ((n + 1 + 1 : ℕ) : ℝ)) s).symm
  calc
    (∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s) =
        ∑ i ∈ Finset.range 1, 1 / Real.rpow (((i + 1 : ℕ) : ℝ)) s +
          ∑' i : ℕ, 1 / Real.rpow (((i + 1 + 1 : ℕ) : ℝ)) s := hsplit.symm
    _ = 1 + ∑' i : ℕ, 1 / Real.rpow (((i + 1 + 1 : ℕ) : ℝ)) s := by simp
    _ ≤ 1 + 1 / (s - 1) := by
      rw [hconvert]
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        add_le_add_left (htail.trans_eq hint) 1

lemma tendsto_zetaSeries_atTop :
    Tendsto Erdos164.zetaSeries atTop (nhds 1) := by
  have hupper : Tendsto (fun s : ℝ ↦ 1 + 1 / (s - 1)) atTop (nhds 1) := by
    have hsub : Tendsto (fun s : ℝ ↦ s - 1) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop (b + 1)] with s hs
      linarith
    have hinv : Tendsto (fun s : ℝ ↦ (s - 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hsub
    simpa only [one_div, add_zero] using (tendsto_const_nhds.add hinv :
      Tendsto (fun s : ℝ ↦ 1 + (s - 1)⁻¹) atTop (nhds (1 + 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact zetaSeries_ge_one hs
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact zetaSeries_le_one_add_inv_sub_one hs

lemma tendsto_inverseZeta_atTop : Tendsto inverseZeta atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := hconst.div tendsto_zetaSeries_atTop (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun s : ℝ ↦ 1 / Erdos164.zetaSeries s) atTop (nhds 1)
  convert h using 1
  · funext s
    rfl
  · norm_num

lemma inverseZeta_le_sub_one {s : ℝ} (hs : 1 < s) : inverseZeta s ≤ s - 1 := by
  have hsub : 0 < s - 1 := sub_pos.mpr hs
  have hzlower : 1 / (s - 1) ≤ Erdos164.zetaSeries s := by
    have h := Erdos164.zetaSeries_ge_one_div_sub_add_one_half hs
    linarith
  have hrecip := one_div_le_one_div_of_le (one_div_pos.mpr hsub) hzlower
  simpa [inverseZeta, one_div_div] using hrecip

lemma tendsto_inverseZeta_one_right :
    Tendsto inverseZeta (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) := by
  have hright : Tendsto (fun s : ℝ ↦ s - 1)
      (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ s - 1) 1 :=
      continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 1)
    have h : Tendsto (fun s : ℝ ↦ s - 1) (nhds 1) (nhds (1 - 1)) := hcont.tendsto
    convert h.mono_left (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left) using 1 <;>
      norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hright ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact inverseZeta_nonneg hs
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact inverseZeta_le_sub_one hs

lemma zetaSeries_one : Erdos164.zetaSeries 1 = 0 := by
  rw [Erdos164.zetaSeries, tsum_eq_zero_of_not_summable]
  have hshift : ¬ Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    simpa using mt (_root_.summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast
  simpa [Real.rpow_one] using hshift

@[simp] lemma inverseZeta_one : inverseZeta 1 = 0 := by
  simp [inverseZeta, zetaSeries_one]

lemma inverseZeta_continuousWithinAt_one :
    ContinuousWithinAt inverseZeta (Ici (1 : ℝ)) 1 := by
  rw [ContinuousWithinAt, inverseZeta_one]
  have hright : Tendsto (fun s : ℝ ↦ s - 1)
      (nhdsWithin (1 : ℝ) (Ici 1)) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ s - 1) 1 :=
      continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 1)
    have h : Tendsto (fun s : ℝ ↦ s - 1) (nhds 1) (nhds (1 - 1)) := hcont.tendsto
    convert h.mono_left (show nhdsWithin (1 : ℝ) (Ici 1) ≤ nhds 1 from inf_le_left) using 1 <;>
      norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hright ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rcases (show (1 : ℝ) ≤ s from hs).eq_or_lt with h | hs
    · subst s; simp
    · exact inverseZeta_nonneg hs
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rcases (show (1 : ℝ) ≤ s from hs).eq_or_lt with h | hs
    · subst s; simp
    · exact inverseZeta_le_sub_one hs

lemma inverseZetaDeriv_integrable :
    IntegrableOn
      (fun s : ℝ ↦ Erdos164.analyticSeries s / Erdos164.zetaSeries s) (Ioi 1) := by
  exact integrableOn_Ioi_deriv_of_nonneg inverseZeta_continuousWithinAt_one
    (fun s hs ↦ inverseZeta_hasDerivAt hs)
    (fun s hs ↦ inverseZeta_deriv_nonneg hs) tendsto_inverseZeta_atTop

lemma integral_inverseZetaDeriv :
    ∫ s in Ioi (1 : ℝ), Erdos164.analyticSeries s / Erdos164.zetaSeries s = 1 := by
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg inverseZeta_continuousWithinAt_one
    (fun s hs ↦ inverseZeta_hasDerivAt hs)
    (fun s hs ↦ inverseZeta_deriv_nonneg hs) tendsto_inverseZeta_atTop

private lemma modelIntegrableAux {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun s : ℝ ↦ Real.log (n : ℝ) / Real.rpow (n : ℝ) s) (Ioi 1) := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hbase := (Erdos164.integrableOn_rpow_neg_Ioi hnreal).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hcongr :
      (fun s : ℝ ↦ Real.log (n : ℝ) / Real.rpow (n : ℝ) s) =
        fun s : ℝ ↦ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s) := by
    funext s
    rw [div_eq_mul_inv]
    congr 1
    exact (Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) s).symm
  rw [hcongr]
  exact hbase.const_mul _

private lemma nuLambdaIntegrableAux {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (nuLambdaIntegrand n) (Ioi (1 : ℝ)) := by
  have hmodel := modelIntegrableAux hn
  refine hmodel.mono' ?_ ?_
  · refine (continuousOn_of_forall_continuousAt fun s hs ↦ ?_).aestronglyMeasurable
      measurableSet_Ioi
    have hz := (Erdos164.zetaSeries_hasDerivAt hs).continuousAt
    have hpow := Real.continuous_const_rpow (by positivity : (n : ℝ) ≠ 0)
    exact continuousAt_const.div (hz.mul hpow.continuousAt)
      (mul_ne_zero (zetaSeries_pos hs).ne' (Real.rpow_pos_of_pos (by positivity) _).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (nuLambdaIntegrand_nonneg hn hs)]
    exact nuLambdaIntegrand_le_model hn hs

lemma incomingIntegrand_one (s : ℝ) :
    incomingIntegrand 1 s = Erdos164.analyticSeries s / Erdos164.zetaSeries s := by
  simp [incomingIntegrand]

lemma incomingIntegrand_nonneg {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 1 < s) :
    0 ≤ incomingIntegrand n s := by
  exact mul_nonneg (inverseZeta_deriv_nonneg hs)
    (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) _)

lemma incomingIntegrand_integrable {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (incomingIntegrand n) (Ioi (1 : ℝ)) := by
  rcases hn.eq_or_lt with rfl | hn
  · convert inverseZetaDeriv_integrable using 1
    funext s
    simp [incomingIntegrand]
  · have hderiv := inverseZetaDeriv_integrable
    refine hderiv.mono' ?_ ?_
    · exact hderiv.1.mul
        (((Real.continuous_const_rpow (by positivity : (n : ℝ) ≠ 0)).comp
          continuous_neg).aestronglyMeasurable.mono_measure (Measure.restrict_le_self))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Real.norm_of_nonneg (incomingIntegrand_nonneg hn.le hs), incomingIntegrand]
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
      have hpow : Real.rpow (n : ℝ) (-s) ≤ 1 := by
        exact Real.rpow_le_one_of_one_le_of_nonpos hnreal
          (neg_nonpos.mpr (le_trans (by norm_num) hs.le))
      exact mul_le_of_le_one_right (inverseZeta_deriv_nonneg hs) hpow

lemma nuLambdaIntegrand_eq (n : ℕ) {s : ℝ} (hs : 1 < s) :
    nuLambdaIntegrand n s =
      inverseZeta s * (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) := by
  by_cases hn : n = 0
  · subst n
    simp [nuLambdaIntegrand, inverseZeta]
  · have hnp : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hz := (zetaSeries_pos hs).ne'
    rw [nuLambdaIntegrand, inverseZeta]
    have hpow : 1 / Real.rpow (n : ℝ) s = Real.rpow (n : ℝ) (-s) :=
      by simpa only [one_div, Real.rpow_eq_pow] using (Real.rpow_neg hnp.le s).symm
    rw [div_mul_eq_div_mul_one_div, hpow]
    field_simp [hz]

lemma rpowNeg_hasDerivAt {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.rpow (n : ℝ) (-t))
      (Real.log (n : ℝ) * (-1) * Real.rpow (n : ℝ) (-s)) s := by
  exact (hasDerivAt_id s).neg.const_rpow (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))

lemma tendsto_rpowNeg_atTop {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun s : ℝ ↦ Real.rpow (n : ℝ) (-s)) atTop (nhds 0) := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  exact (tendsto_rpow_atBot_of_base_gt_one (n : ℝ) hnreal).comp tendsto_neg_atTop_atBot

lemma integral_incomingIntegrand {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in Ioi (1 : ℝ), incomingIntegrand n s = nuLambda n := by
  rcases hn.eq_or_lt with rfl | hn
  · simp only [incomingIntegrand_one, nuLambda_one, integral_inverseZetaDeriv]
  · have hn2 : 2 ≤ n := by omega
    have hu := fun s (hs : s ∈ Ioi (1 : ℝ)) ↦ inverseZeta_hasDerivAt hs
    have hv := fun s (_hs : s ∈ Ioi (1 : ℝ)) ↦ rpowNeg_hasDerivAt hn.le s
    have huv' : IntegrableOn
        (fun s : ℝ ↦ inverseZeta s *
          (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s))) (Ioi 1) := by
      have hnu := (nuLambdaIntegrableAux hn2).neg
      refine hnu.congr_fun ?_ measurableSet_Ioi
      intro s hs
      change -nuLambdaIntegrand n s = _
      rw [nuLambdaIntegrand_eq n hs]
      ring
    have hu'v : IntegrableOn
        (fun s : ℝ ↦ (Erdos164.analyticSeries s / Erdos164.zetaSeries s) *
          Real.rpow (n : ℝ) (-s)) (Ioi 1) := incomingIntegrand_integrable hn.le
    have hzero : Tendsto
        (fun s : ℝ ↦ inverseZeta s * Real.rpow (n : ℝ) (-s))
        (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) := by
      convert tendsto_inverseZeta_one_right.mul
        (((Real.continuous_const_rpow (by positivity : (n : ℝ) ≠ 0)).comp
          continuous_neg).continuousAt.tendsto.mono_left inf_le_left) using 1 <;> simp
    have hinfty : Tendsto
        (fun s : ℝ ↦ inverseZeta s * Real.rpow (n : ℝ) (-s)) atTop (nhds 0) := by
      convert tendsto_inverseZeta_atTop.mul (tendsto_rpowNeg_atTop hn2) using 1 <;> norm_num
    have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
    rw [nuLambda_of_two_le hn2]
    have hleft :
        (∫ s in Ioi (1 : ℝ), inverseZeta s *
          (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s))) =
          -(∫ s in Ioi (1 : ℝ), nuLambdaIntegrand n s) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change inverseZeta s * (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s)) =
        -(nuLambdaIntegrand n s)
      rw [nuLambdaIntegrand_eq n hs]
      ring
    have hright :
        (∫ s in Ioi (1 : ℝ),
          (Erdos164.analyticSeries s / Erdos164.zetaSeries s) * Real.rpow (n : ℝ) (-s)) =
          ∫ s in Ioi (1 : ℝ), incomingIntegrand n s := by rfl
    rw [hleft, hright] at hparts
    linarith

lemma summable_vonMangoldt_div_rpow_subtype {s : ℝ} (hs : 1 < s) :
    Summable (fun q : {q : ℕ // 2 ≤ q} ↦
      ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) s) := by
  let F : ℕ → ℝ := fun q ↦
    if 2 ≤ q then ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) s else 0
  have hfull : Summable F := by
    simpa [F, show 1 + (s - 1) = s by ring] using
      (Erdos164.summable_vonMangoldt_div_rpow_if
        (v := s - 1) (by linarith) (P := fun q ↦ 2 ≤ q) (fun h ↦ h))
  exact (hfull.comp_injective Subtype.val_injective).congr fun q ↦ by simp [F, q.2]

lemma tsum_incomingPiece {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 1 < s) :
    (∑' q : {q : ℕ // 2 ≤ q}, incomingPiece n q s) = incomingIntegrand n s := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  calc
    (∑' q : {q : ℕ // 2 ≤ q}, incomingPiece n q s) =
        inverseZeta s * Real.rpow (n : ℝ) (-s) *
          (∑' q : {q : ℕ // 2 ≤ q},
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) s) := by
      simp only [incomingPiece]
      rw [tsum_mul_left]
    _ = inverseZeta s * Real.rpow (n : ℝ) (-s) * Erdos164.analyticSeries s := by
      rfl
    _ = incomingIntegrand n s := by
      rw [incomingIntegrand, inverseZeta]
      field_simp [(zetaSeries_pos hs).ne']

lemma incomingPiece_nonneg {n : ℕ} (hn : 1 ≤ n) (q : {q : ℕ // 2 ≤ q})
    {s : ℝ} (hs : 1 < s) : 0 ≤ incomingPiece n q s := by
  exact mul_nonneg
    (mul_nonneg (inverseZeta_nonneg hs) (Real.rpow_nonneg (by positivity) _))
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _))

lemma incomingPiece_continuousOn {n : ℕ} (hn : 1 ≤ n) (q : {q : ℕ // 2 ≤ q}) :
    ContinuousOn (incomingPiece n q) (Ioi (1 : ℝ)) := by
  intro s hs
  have hinv := (inverseZeta_hasDerivAt hs).continuousAt
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hncont := (Real.continuous_const_rpow hn0).comp
      continuous_neg
  have hq0 : (q.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two q.2))
  have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two q.2)
  have hqcont := Real.continuous_const_rpow hq0
  exact ((hinv.mul hncont.continuousAt).mul
    (continuousAt_const.div hqcont.continuousAt (Real.rpow_pos_of_pos hqpos _).ne')).continuousWithinAt

lemma integral_incomingPiece {n : ℕ} (hn : 1 ≤ n) (q : {q : ℕ // 2 ≤ q}) :
    (∫ s in Ioi (1 : ℝ), incomingPiece n q s) = incomingWeight n q.1 := by
  have hnq2 : 2 ≤ n * q.1 := by
    calc 2 = 1 * 2 := by norm_num
         _ ≤ n * q.1 := Nat.mul_le_mul hn q.2
  have hnqgt : 1 < n * q.1 := lt_of_lt_of_le Nat.one_lt_two hnq2
  have hlog : Real.log ((n * q.1 : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hnqgt)).ne'
  rw [incomingWeight, nuLambda_of_two_le hnq2]
  rw [div_eq_mul_inv, ← MeasureTheory.integral_mul_const,
    ← MeasureTheory.integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [nuLambdaIntegrand, incomingPiece, inverseZeta]
  simp only [Real.rpow_eq_pow]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two q.2)
  have hlog' : Real.log ((n : ℝ) * (q.1 : ℝ)) ≠ 0 := by
    simpa only [Nat.cast_mul] using hlog
  rw [Nat.cast_mul,
    Real.mul_rpow hnpos.le hqpos.le, Real.rpow_neg hnpos.le s]
  field_simp [hlog, hlog', (zetaSeries_pos hs).ne',
    (Real.rpow_pos_of_pos hnpos s).ne', (Real.rpow_pos_of_pos hqpos s).ne']

lemma tsum_integral_incomingPiece {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : {q : ℕ // 2 ≤ q}, ∫ s in Ioi (1 : ℝ), incomingPiece n q s) =
      ∫ s in Ioi (1 : ℝ), incomingIntegrand n s := by
  let μ := volume.restrict (Ioi (1 : ℝ))
  have hmeas (q : {q : ℕ // 2 ≤ q}) :
      AEStronglyMeasurable (incomingPiece n q) μ :=
    (incomingPiece_continuousOn hn q).aestronglyMeasurable measurableSet_Ioi
  have hsummable {s : ℝ} (hs : 1 < s) : Summable (fun q : {q : ℕ // 2 ≤ q} ↦
      incomingPiece n q s) := by
    simpa [incomingPiece] using
      (summable_vonMangoldt_div_rpow_subtype hs).mul_left
        (inverseZeta s * Real.rpow (n : ℝ) (-s))
  have henorm (s : ℝ) (hs : s ∈ Ioi (1 : ℝ)) :
      (∑' q : {q : ℕ // 2 ≤ q}, ‖incomingPiece n q s‖ₑ) =
        ‖incomingIntegrand n s‖ₑ := by
    rw [Real.enorm_of_nonneg (incomingIntegrand_nonneg hn hs),
      ← tsum_incomingPiece hn hs, ENNReal.ofReal_tsum_of_nonneg]
    · apply tsum_congr
      intro q
      rw [Real.enorm_of_nonneg (incomingPiece_nonneg hn q hs)]
    · intro q
      exact incomingPiece_nonneg hn q hs
    · exact hsummable hs
  have hfinite :
      (∑' q : {q : ℕ // 2 ≤ q}, ∫⁻ s, ‖incomingPiece n q s‖ₑ ∂μ) ≠ ⊤ := by
    rw [← lintegral_tsum (fun q ↦ (hmeas q).enorm)]
    have heq :
        (∫⁻ s, ∑' q : {q : ℕ // 2 ≤ q}, ‖incomingPiece n q s‖ₑ ∂μ) =
          ∫⁻ s, ‖incomingIntegrand n s‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact henorm s hs
    rw [heq]
    exact (incomingIntegrand_integrable hn).2.ne
  have hswap := integral_tsum hmeas hfinite
  have hleft :
      (∫ s, ∑' q : {q : ℕ // 2 ≤ q}, incomingPiece n q s ∂μ) =
        ∫ s in Ioi (1 : ℝ), incomingIntegrand n s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact tsum_incomingPiece hn hs
  simpa [μ] using hswap.symm.trans hleft

/-- Exact source-invariance on positive integers, in the natural subtype indexing used by
`analyticSeries`. -/
theorem tsum_incomingWeight_subtype {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : {q : ℕ // 2 ≤ q}, incomingWeight n q.1) = nuLambda n := by
  calc
    (∑' q : {q : ℕ // 2 ≤ q}, incomingWeight n q.1) =
        ∑' q : {q : ℕ // 2 ≤ q}, ∫ s in Ioi (1 : ℝ), incomingPiece n q s := by
          apply tsum_congr
          intro q
          exact (integral_incomingPiece hn q).symm
    _ = ∫ s in Ioi (1 : ℝ), incomingIntegrand n s := tsum_integral_incomingPiece hn
    _ = nuLambda n := integral_incomingIntegrand hn

/-- Exact ABLLPSTT invariance identity.  The `q = 0,1` terms vanish, so the identity is
also available as a sum over all natural multipliers. -/
theorem tsum_incomingWeight {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : ℕ, incomingWeight n q) = nuLambda n := by
  rw [← tsum_incomingWeight_subtype hn]
  symm
  apply tsum_subtype_eq_of_support_subset
  intro q hq
  change 2 ≤ q
  by_contra hq2
  have hqsmall : q = 0 ∨ q = 1 := by omega
  rcases hqsmall with rfl | rfl
  · exact hq (by simp [incomingWeight])
  · exact hq (by simp [incomingWeight])

lemma modelIntegrable {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun s : ℝ ↦ Real.log (n : ℝ) / Real.rpow (n : ℝ) s) (Ioi 1) :=
  modelIntegrableAux hn

lemma nuLambdaIntegrable {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (nuLambdaIntegrand n) (Ioi (1 : ℝ)) :=
  nuLambdaIntegrableAux hn

lemma nuLambda_nonneg (n : ℕ) : 0 ≤ nuLambda n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · have : n = 0 := by omega
    simp [this]
  · simp
  · have hn2 : 2 ≤ n := by omega
    rw [nuLambda_of_two_le hn2]
    exact integral_nonneg_of_ae <| ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦
      nuLambdaIntegrand_nonneg hn2 hs

lemma nuLambdaIntegrand_pos {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    0 < nuLambdaIntegrand n s := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  exact div_pos (Real.log_pos hnreal)
    (mul_pos (zetaSeries_pos hs)
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hnreal) s))

lemma nuLambda_pos {n : ℕ} (hn : 1 ≤ n) : 0 < nuLambda n := by
  rcases hn.eq_or_lt with rfl | hn
  · simp
  · have hn2 : 2 ≤ n := by omega
    rw [nuLambda_of_two_le hn2]
    refine (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦
        (nuLambdaIntegrand_nonneg hn2 hs)) (nuLambdaIntegrable hn2)).2 ?_
    have hsubset : Ioo (1 : ℝ) 2 ⊆ Function.support (nuLambdaIntegrand n) ∩ Ioi 1 := by
      intro s hs
      exact ⟨ne_of_gt (nuLambdaIntegrand_pos hn2 hs.1), hs.1⟩
    have hmeasure : volume (Ioo (1 : ℝ) 2) = 1 := by norm_num
    calc
      0 < volume (Ioo (1 : ℝ) 2) := by rw [hmeasure]; norm_num
      _ ≤ volume (Function.support (nuLambdaIntegrand n) ∩ Ioi 1) := measure_mono hsubset

lemma incomingWeight_nonneg {n q : ℕ} (hn : 1 ≤ n) : 0 ≤ incomingWeight n q := by
  by_cases hq : 2 ≤ q
  · have hnq2 : 2 ≤ n * q := by
      calc 2 = 1 * 2 := by norm_num
           _ ≤ n * q := Nat.mul_le_mul hn hq
    have hnqgt : 1 < n * q := lt_of_lt_of_le Nat.one_lt_two hnq2
    have hlog : 0 < Real.log (((n * q : ℕ) : ℝ)) :=
      Real.log_pos (by exact_mod_cast hnqgt)
    exact div_nonneg
      (mul_nonneg (nuLambda_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
      hlog.le
  · have hqsmall : q = 0 ∨ q = 1 := by omega
    rcases hqsmall with rfl | rfl <;> simp [incomingWeight]

lemma summable_incomingWeight_subtype {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun q : {q : ℕ // 2 ≤ q} ↦ incomingWeight n q.1) := by
  by_contra hsum
  have hz := tsum_eq_zero_of_not_summable hsum
  rw [tsum_incomingWeight_subtype hn] at hz
  exact (nuLambda_pos hn).ne' hz

lemma hasSum_incomingWeight_subtype {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun q : {q : ℕ // 2 ≤ q} ↦ incomingWeight n q.1) (nuLambda n) := by
  rw [← tsum_incomingWeight_subtype hn]
  exact (summable_incomingWeight_subtype hn).hasSum

lemma nuLambda_le_inv (n : ℕ) : nuLambda n ≤ 1 / (n : ℝ) := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · have : n = 0 := by omega
    simp [this]
  · simp
  · have hn2 : 2 ≤ n := by omega
    rw [nuLambda_of_two_le hn2]
    have hmodel := modelIntegrable hn2
    have hle := setIntegral_mono_ae_restrict (nuLambdaIntegrable hn2) hmodel
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ nuLambdaIntegrand_le_model hn2 hs)
    refine hle.trans_eq ?_
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
    have hfun :
        (fun s : ℝ ↦ Real.log (n : ℝ) / Real.rpow (n : ℝ) s) =
          fun s : ℝ ↦ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s) := by
      funext s
      rw [div_eq_mul_inv]
      congr 1
      simpa only [Real.rpow_eq_pow] using
        (Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) s).symm
    calc
      ∫ s in Ioi (1 : ℝ), Real.log (n : ℝ) / Real.rpow (n : ℝ) s
          = Real.log (n : ℝ) * ∫ s in Ioi (1 : ℝ), Real.rpow (n : ℝ) (-s) := by
              rw [hfun]
              rw [MeasureTheory.integral_const_mul]
      _ = Real.log (n : ℝ) * (1 / Real.log (n : ℝ) / (n : ℝ)) := by
            congr 1
            calc
              ∫ s in Ioi (1 : ℝ), Real.rpow (n : ℝ) (-s) =
                  ∫ s in Ioi (1 : ℝ), Real.exp ((-Real.log (n : ℝ)) * s) := by
                    apply setIntegral_congr_fun measurableSet_Ioi
                    intro s hs
                    simp [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ))]
              _ = -Real.exp ((-Real.log (n : ℝ)) * 1) / (-Real.log (n : ℝ)) := by
                    exact integral_exp_mul_Ioi (by linarith) 1
              _ = 1 / Real.log (n : ℝ) / (n : ℝ) := by
                    rw [show Real.exp ((-Real.log (n : ℝ)) * 1) = ((n : ℝ))⁻¹ by
                      simp [Real.exp_neg, Real.exp_log (by positivity : 0 < (n : ℝ))]]
                    field_simp [hlog.ne', (by positivity : (n : ℝ) ≠ 0)]
      _ = 1 / (n : ℝ) := by field_simp [hlog.ne']

lemma integral_sub_one_mul_rpowNeg {n : ℕ} (hn : 2 ≤ n) :
    ∫ s in Ioi (1 : ℝ), (s - 1) * Real.rpow (n : ℝ) (-s) =
      1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  let L : ℝ := Real.log (n : ℝ)
  let F : ℝ → ℝ := fun s ↦ -((s - 1) / L + 1 / L ^ 2) * Real.rpow (n : ℝ) (-s)
  let g : ℝ → ℝ := fun s ↦ (s - 1) * Real.rpow (n : ℝ) (-s)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hL : 0 < L := Real.log_pos hnreal
  have hderiv (s : ℝ) : HasDerivAt F (g s) s := by
    have hA : HasDerivAt (fun t : ℝ ↦ -((t - 1) / L + 1 / L ^ 2)) (-1 / L) s := by
      have hA0 := (((hasDerivAt_id s).sub_const 1).div_const L).add_const
        (1 / L ^ 2) |>.neg
      change HasDerivAt (fun t : ℝ ↦ -((t - 1) / L + 1 / L ^ 2)) (-(1 / L)) s at hA0
      exact hA0.congr_deriv (by ring)
    have hB := rpowNeg_hasDerivAt (le_trans (by decide : 1 ≤ 2) hn) s
    have hval :
        (-1 / L) * Real.rpow (n : ℝ) (-s) +
            (-((s - 1) / L + 1 / L ^ 2)) *
              (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s)) =
          (s - 1) * Real.rpow (n : ℝ) (-s) := by
      have hlogne : Real.log (n : ℝ) ≠ 0 := by simpa only [L] using hL.ne'
      field_simp [hL.ne', hlogne]
      ring
    have hprod := hA.mul hB
    change HasDerivAt
      (fun t : ℝ ↦ -((t - 1) / L + 1 / L ^ 2) * Real.rpow (n : ℝ) (-t))
      ((-1 / L) * Real.rpow (n : ℝ) (-s) +
        (-((s - 1) / L + 1 / L ^ 2)) *
          (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s))) s at hprod
    exact hprod.congr_deriv hval
  have hg_nonneg (s : ℝ) (hs : s ∈ Ioi (1 : ℝ)) : 0 ≤ g s := by
    exact mul_nonneg (sub_nonneg.mpr hs.le) (Real.rpow_nonneg (by positivity) _)
  have hB : Tendsto (fun s : ℝ ↦ Real.rpow (n : ℝ) (-s)) atTop (nhds 0) :=
    tendsto_rpowNeg_atTop hn
  have hSB : Tendsto (fun s : ℝ ↦ s * Real.rpow (n : ℝ) (-s)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) L hL
    convert h using 1
    funext s
    rw [Real.rpow_eq_pow, Real.rpow_one,
      Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ))]
    congr 1
    dsimp only [L]
    ring
  have hFtop : Tendsto F atTop (nhds 0) := by
    have haffine : Tendsto
        (fun s : ℝ ↦ -((s - 1) / L + 1 / L ^ 2) * Real.rpow (n : ℝ) (-s))
        atTop (nhds 0) := by
      have hdecomp : (fun s : ℝ ↦ -((s - 1) / L + 1 / L ^ 2) *
          Real.rpow (n : ℝ) (-s)) =
          fun s ↦ (-1 / L) * (s * Real.rpow (n : ℝ) (-s)) +
            (1 / L - 1 / L ^ 2) * Real.rpow (n : ℝ) (-s) := by
        funext s
        ring
      rw [hdecomp]
      convert (tendsto_const_nhds.mul hSB).add (tendsto_const_nhds.mul hB) using 1 <;> ring
    exact haffine
  have hFTC := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hderiv 1).continuousAt.continuousWithinAt)
    (fun s hs ↦ hderiv s) hg_nonneg hFtop
  simpa [F, g, L, Real.rpow_eq_pow, Real.rpow_neg_one] using hFTC

lemma nuLambdaIntegrand_le_sharpModel {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    nuLambdaIntegrand n s ≤
      Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))
  have hinv := inverseZeta_le_sub_one hs
  rw [nuLambdaIntegrand_eq n hs]
  have hpow : 0 ≤ Real.rpow (n : ℝ) (-s) := Real.rpow_nonneg (by positivity) _
  calc
    inverseZeta s * (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) ≤
        (s - 1) * (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hlog.le hpow)
    _ = Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) := by ring

lemma sqSharpModel_integrable_and_integral {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun s : ℝ ↦ (s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)) (Ioi 1) ∧
      (∫ s in Ioi (1 : ℝ), (s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)) =
        2 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 3) := by
  let L : ℝ := Real.log (n : ℝ)
  let F : ℝ → ℝ := fun s ↦
    -((s - 1) ^ 2 / L + 2 * (s - 1) / L ^ 2 + 2 / L ^ 3) *
      Real.rpow (n : ℝ) (-s)
  let g : ℝ → ℝ := fun s ↦ (s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hL : 0 < L := Real.log_pos hnreal
  have hderiv (s : ℝ) : HasDerivAt F (g s) s := by
    have hpoly : HasDerivAt
        (fun t : ℝ ↦ -((t - 1) ^ 2 / L + 2 * (t - 1) / L ^ 2 + 2 / L ^ 3))
        (-(2 * (s - 1) / L + 2 / L ^ 2)) s := by
      have hpoly0 := (((((hasDerivAt_id s).sub_const 1).pow 2).div_const L).add
        ((((hasDerivAt_id s).sub_const 1).const_mul 2).div_const (L ^ 2))).add_const
          (2 / L ^ 3) |>.neg
      refine (hpoly0.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_deriv ?_
      · intro t
        simp only [Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq]
      · norm_num
    have hB := rpowNeg_hasDerivAt (le_trans (by decide : 1 ≤ 2) hn) s
    have hval :
        (-(2 * (s - 1) / L + 2 / L ^ 2)) * Real.rpow (n : ℝ) (-s) +
            (-((s - 1) ^ 2 / L + 2 * (s - 1) / L ^ 2 + 2 / L ^ 3)) *
              (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s)) =
          (s - 1) ^ 2 * Real.rpow (n : ℝ) (-s) := by
      have hlogne : Real.log (n : ℝ) ≠ 0 := by simpa only [L] using hL.ne'
      field_simp [hL.ne', hlogne]
      ring
    have hprod := hpoly.mul hB
    change HasDerivAt
      (fun t : ℝ ↦
        -((t - 1) ^ 2 / L + 2 * (t - 1) / L ^ 2 + 2 / L ^ 3) *
          Real.rpow (n : ℝ) (-t))
      ((-(2 * (s - 1) / L + 2 / L ^ 2)) * Real.rpow (n : ℝ) (-s) +
        (-((s - 1) ^ 2 / L + 2 * (s - 1) / L ^ 2 + 2 / L ^ 3)) *
          (Real.log (n : ℝ) * -1 * Real.rpow (n : ℝ) (-s))) s at hprod
    exact hprod.congr_deriv hval
  have hg_nonneg (s : ℝ) (hs : s ∈ Ioi (1 : ℝ)) : 0 ≤ g s := by
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hB := tendsto_rpowNeg_atTop hn
  have hSB : Tendsto (fun s : ℝ ↦ s * Real.rpow (n : ℝ) (-s)) atTop (nhds 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 L hL using 1
    funext s
    rw [Real.rpow_eq_pow, Real.rpow_one,
      Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ))]
    congr 1
    dsimp only [L]
    ring
  have hS2B : Tendsto (fun s : ℝ ↦ s ^ 2 * Real.rpow (n : ℝ) (-s)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 L hL
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    rw [Real.rpow_eq_pow, Real.rpow_two s,
      Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ))]
    congr 1
    dsimp only [L]
    ring
  have hFtop : Tendsto F atTop (nhds 0) := by
    have hdecomp : F = fun s ↦
        (-1 / L) * (s ^ 2 * Real.rpow (n : ℝ) (-s)) +
        (2 / L - 2 / L ^ 2) * (s * Real.rpow (n : ℝ) (-s)) +
        (-1 / L + 2 / L ^ 2 - 2 / L ^ 3) * Real.rpow (n : ℝ) (-s) := by
      funext s
      dsimp [F]
      ring
    rw [hdecomp]
    convert ((tendsto_const_nhds.mul hS2B).add (tendsto_const_nhds.mul hSB)).add
      (tendsto_const_nhds.mul hB) using 1 <;> ring
  have hint : IntegrableOn g (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg ((hderiv 1).continuousAt.continuousWithinAt)
      (fun s hs ↦ hderiv s) hg_nonneg hFtop
  refine ⟨hint, ?_⟩
  have hFTC := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hderiv 1).continuousAt.continuousWithinAt) (fun s hs ↦ hderiv s) hg_nonneg hFtop
  simpa [F, g, L, Real.rpow_eq_pow, Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev,
    mul_assoc] using hFTC

lemma inverseZeta_lower {s : ℝ} (hs : 1 < s) :
    (s - 1) / s ≤ inverseZeta s := by
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hupper := zetaSeries_le_one_add_inv_sub_one hs
  have hzpos := zetaSeries_pos hs
  have hden : 1 + 1 / (s - 1) = s / (s - 1) := by
    field_simp [sub_ne_zero.mpr hs.ne']
    ring
  have hrecip := one_div_le_one_div_of_le hzpos hupper
  have : 1 / (s / (s - 1)) = (s - 1) / s := by field_simp [hspos.ne', sub_ne_zero.mpr hs.ne']
  change (s - 1) / s ≤ 1 / Erdos164.zetaSeries s
  rw [← this, ← hden]
  exact hrecip

lemma sharpDifference_pointwise {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    0 ≤ Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) -
        nuLambdaIntegrand n s ∧
    Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) -
        nuLambdaIntegrand n s ≤
      Real.log (n : ℝ) * ((s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))
  have hpow : 0 ≤ Real.rpow (n : ℝ) (-s) := Real.rpow_nonneg (by positivity) _
  have hu := inverseZeta_le_sub_one hs
  have hl := inverseZeta_lower hs
  rw [nuLambdaIntegrand_eq n hs]
  have hC : 0 ≤ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s) :=
    mul_nonneg hlog.le hpow
  constructor
  · calc
      0 ≤ ((s - 1) - inverseZeta s) *
          (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) :=
        mul_nonneg (sub_nonneg.mpr hu) hC
      _ = Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) -
          inverseZeta s * (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) := by ring
  · have hspos : 0 < s := lt_trans zero_lt_one hs
    have halg : (s - 1) - inverseZeta s ≤ (s - 1) ^ 2 := by
      calc
        (s - 1) - inverseZeta s ≤ (s - 1) - (s - 1) / s := by linarith
        _ ≤ (s - 1) ^ 2 := by
          have heq : (s - 1) - (s - 1) / s = (s - 1) ^ 2 / s := by
            field_simp [hspos.ne']
          rw [heq]
          apply (div_le_iff₀ hspos).2
          nlinarith [sq_nonneg (s - 1)]
    calc
      Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) -
          inverseZeta s * (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) =
        ((s - 1) - inverseZeta s) *
          (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) := by ring
      _ ≤ (s - 1) ^ 2 *
          (Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s)) :=
        mul_le_mul_of_nonneg_right halg hC
      _ = Real.log (n : ℝ) * ((s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)) := by ring

/-- Uniform pointwise discrepancy estimate from the paper. -/
theorem nuLambda_error_bound {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ doublyHarmonicWeight n - nuLambda n ∧
      doublyHarmonicWeight n - nuLambda n ≤
        2 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))
  have hnu := nuLambdaIntegrable hn
  have hsq := sqSharpModel_integrable_and_integral hn
  have hsharp : IntegrableOn
      (fun s : ℝ ↦ Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)))
      (Ioi 1) := by
    have hbase := modelIntegrable hn
    have hmajor := hbase.add (hsq.1.const_mul (Real.log (n : ℝ)))
    refine hmajor.mono' ?_ ?_
    · exact (continuous_const.mul
        ((continuous_id.sub continuous_const).mul
          ((Real.continuous_const_rpow (by positivity : (n : ℝ) ≠ 0)).comp
            continuous_neg))).aestronglyMeasurable.mono_measure (Measure.restrict_le_self)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have ht : 0 ≤ s - 1 := sub_nonneg.mpr hs.le
      have hpow : 0 ≤ Real.rpow (n : ℝ) (-s) := Real.rpow_nonneg (by positivity) _
      rw [Real.norm_of_nonneg (mul_nonneg hlog.le (mul_nonneg ht hpow))]
      change Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) ≤
        Real.log (n : ℝ) / Real.rpow (n : ℝ) s +
          Real.log (n : ℝ) * ((s - 1) ^ 2 * Real.rpow (n : ℝ) (-s))
      have hbase : Real.log (n : ℝ) / Real.rpow (n : ℝ) s =
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s) := by
        rw [div_eq_mul_inv]
        congr 1
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) s).symm
      rw [hbase]
      have htineq : s - 1 ≤ 1 + (s - 1) ^ 2 := by
        nlinarith [sq_nonneg ((s - 1) - (1 / 2 : ℝ))]
      have hC : 0 ≤ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-s) :=
        mul_nonneg hlog.le hpow
      nlinarith [mul_le_mul_of_nonneg_right htineq hC]
  have hdiffInt := hsharp.sub hnu
  have hnonneg : 0 ≤ ∫ s in Ioi (1 : ℝ),
      Real.log (n : ℝ) * ((s - 1) * Real.rpow (n : ℝ) (-s)) -
        nuLambdaIntegrand n s := by
    exact integral_nonneg_of_ae (μ := volume.restrict (Ioi (1 : ℝ)))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s (hs : 1 < s) ↦
        (sharpDifference_pointwise hn hs).1)
  have hupper := setIntegral_mono_ae_restrict hdiffInt (hsq.1.const_mul (Real.log (n : ℝ)))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s (hs : 1 < s) ↦
      (sharpDifference_pointwise hn hs).2)
  rw [doublyHarmonicWeight, if_pos hn, nuLambda_of_two_le hn]
  have hsharpEval :
      (∫ s in Ioi (1 : ℝ), Real.log (n : ℝ) *
        ((s - 1) * Real.rpow (n : ℝ) (-s))) =
        ((n : ℝ) * Real.log (n : ℝ))⁻¹ := by
    rw [integral_const_mul, integral_sub_one_mul_rpowNeg hn]
    field_simp [hlog.ne', (by positivity : (n : ℝ) ≠ 0)]
  rw [integral_sub hsharp hnu, hsharpEval] at hnonneg
  have hupper' :
      (∫ s in Ioi (1 : ℝ), Real.log (n : ℝ) *
          ((s - 1) * Real.rpow (n : ℝ) (-s))) -
          ∫ s in Ioi (1 : ℝ), nuLambdaIntegrand n s ≤
        ∫ s in Ioi (1 : ℝ), Real.log (n : ℝ) *
          ((s - 1) ^ 2 * Real.rpow (n : ℝ) (-s)) := by
    rw [← integral_sub hsharp hnu]
    exact hupper
  rw [hsharpEval] at hupper'
  constructor
  · exact hnonneg
  · refine hupper'.trans_eq ?_
    rw [integral_const_mul, hsq.2]
    field_simp [hlog.ne', (by positivity : (n : ℝ) ≠ 0)]

/-- The sharp comparison used in the moment estimates.  It is intentionally stated on
`n ≥ 2`, since the exceptional normalizing mass is `nuLambda 1 = 1` whereas the literal
doubly harmonic weight vanishes at `1`. -/
theorem nuLambda_le_doublyHarmonicWeight {n : ℕ} (hn : 2 ≤ n) :
    nuLambda n ≤ doublyHarmonicWeight n :=
  sub_nonneg.mp (nuLambda_error_bound hn).1

/-- The elementary comparison series which controls the total error between the invariant
weight and `1 / (n log n)`. -/
theorem summable_inv_mul_log_sq_from_two :
    Summable (fun n : ℕ =>
      if 2 ≤ n then 1 / ((n : ℝ) * (Real.log n) ^ 2) else 0) := by
  let f : ℕ → ℝ := fun n =>
    if 2 ≤ n then 1 / ((n : ℝ) * (Real.log n) ^ 2) else 0
  have hf_nonneg : ∀ᶠ n in atTop, 0 ≤ f n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    simp only [f, if_pos hn]
    positivity
  have hf_mono : ∀ᶠ n in atTop, f (n + 1) ≤ f n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    simp only [f, if_pos hn, if_pos (by omega : 2 ≤ n + 1)]
    gcongr
    · exact mul_pos (Nat.cast_pos.mpr (by omega))
        (sq_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega))))
    · omega
    · omega
  apply (summable_condensed_iff_of_eventually_nonneg hf_nonneg hf_mono).mp
  have hsquare : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := by
    exact Real.summable_one_div_nat_pow.2 (by norm_num)
  refine (hsquare.mul_left (1 / (Real.log 2) ^ 2)).congr ?_
  intro k
  rcases k with _ | k
  · simp [f]
  · have hpow : 2 ≤ 2 ^ (k + 1) := by
      exact Nat.one_lt_pow (by norm_num) (by omega)
    simp only [f, if_pos hpow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
    field_simp

/-- The discrepancy is absolutely summable after removing the exceptional value `n = 1`. -/
theorem summable_nuLambda_discrepancy :
    Summable (fun n : ℕ =>
      if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) := by
  apply Summable.of_nonneg_of_le
  · intro n
    split_ifs with hn
    · exact (nuLambda_error_bound hn).1
    · exact le_rfl
  · intro n
    split_ifs with hn
    · exact (nuLambda_error_bound hn).2
    · positivity
  · refine (summable_inv_mul_log_sq_from_two.mul_left 2).congr ?_
    intro n
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]
      ring
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl <;> norm_num

/-- A finite-set form of the uniform discrepancy estimate. -/
theorem finite_sum_nuLambda_discrepancy_le_tsum (S : Finset ℕ) :
    ∑ n ∈ S, (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) ≤
      ∑' n : ℕ, (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) := by
  exact summable_nuLambda_discrepancy.sum_le_tsum S fun n _ ↦ by
    split_ifs with hn
    · exact (nuLambda_error_bound hn).1
    · exact le_rfl

/-- Uniform discrepancy for a finite set of genuine (`n ≥ 2`) terms. -/
theorem finite_sum_nuLambda_error_bound (S : Finset ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n) :
    0 ≤ ∑ n ∈ S, (doublyHarmonicWeight n - nuLambda n) ∧
      ∑ n ∈ S, (doublyHarmonicWeight n - nuLambda n) ≤
        ∑' n : ℕ, (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) := by
  have heq :
      ∑ n ∈ S, (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) =
        ∑ n ∈ S, (doublyHarmonicWeight n - nuLambda n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos (hS n hn)]
  constructor
  · exact Finset.sum_nonneg fun n hn ↦ (nuLambda_error_bound (hS n hn)).1
  · rw [← heq]
    exact finite_sum_nuLambda_discrepancy_le_tsum S

end Erdos1217
