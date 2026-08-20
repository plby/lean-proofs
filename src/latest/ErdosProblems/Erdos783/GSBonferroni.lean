/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSLocalSolution
import ErdosProblems.Erdos783.GSSolution

/-! # The finite GS expansion and its Bonferroni inequalities -/

open MeasureTheory Set Finset
open scoped BigOperators Convolution

namespace Erdos783

noncomputable section

lemma gsMoment_eq_zero_of_le_one
    (chi : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    gsMoment chi n u = 0 := by
  cases n with
  | zero => omega
  | succ m =>
      rw [gsMoment]
      by_cases h1u : 1 ≤ u
      · have hu : u = 1 := le_antisymm hu1 h1u
        subst u
        simp
      · simp [h1u]

lemma gsAlternatingMomentSum_eq_one_of_le_one
    (chi : ℝ → ℝ) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    gsAlternatingMomentSum chi N u = 1 := by
  rw [gsAlternatingMomentSum]
  have hzero : ∀ j ∈ Finset.range (N + 1), j ≠ 0 →
      (-1 : ℝ) ^ j * gsMoment chi j u / j.factorial = 0 := by
    intro j hj hj0
    rw [gsMoment_eq_zero_of_le_one chi (Nat.one_le_iff_ne_zero.mpr hj0)
      hu0 hu1, mul_zero, zero_div]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    exact hzero j hj hj0
  · simp

lemma gs_weightedDefect_convolution_moment_nonneg
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {K u : ℝ} (hu0 : 0 ≤ u) (huK : u < K) :
    0 ≤ (gsWeightedDefectLocal chi K ⋆[ContinuousLinearMap.mul ℝ ℝ]
      gsMomentLocal chi K N) u := by
  rw [gsWeightedDefectLocal, gsMomentLocal,
    gsLocalize_convolution_apply hu0 huK]
  apply intervalIntegral.integral_nonneg hu0
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hut0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
  apply mul_nonneg
  · by_cases htZero : t = 0
    · simp [htZero]
    · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htZero)
      have heq : t * gsDefectWeight chi t = 1 - chi t := by
        unfold gsDefectWeight
        field_simp [htZero]
      rw [heq]
      exact sub_nonneg.mpr (hchi.2.2.1 t htPos.le)
  · exact gsMoment_nonneg hchi N hut0

lemma abs_gsAlternatingMomentSum_le
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {U u : ℝ} (hU : 1 ≤ U) (hu0 : 0 ≤ u) (huU : u ≤ U) :
    |gsAlternatingMomentSum chi N u| ≤
      ∑ j ∈ Finset.range (N + 1),
        gsLogScale chi U ^ j / j.factorial := by
  rw [gsAlternatingMomentSum]
  calc
    |∑ j ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ j * gsMoment chi j u / j.factorial| ≤
        ∑ j ∈ Finset.range (N + 1),
          |(-1 : ℝ) ^ j * gsMoment chi j u / j.factorial| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          gsLogScale chi U ^ j / j.factorial := by
      apply Finset.sum_le_sum
      intro j hj
      have hm : gsMoment chi j u ≤ gsMoment chi j U :=
        gsMoment_mono_Ici_zero hchi j (mem_Ici.mpr hu0)
          (mem_Ici.mpr (zero_le_one.trans hU)) huU
      have hm' : gsMoment chi j u ≤ gsLogScale chi U ^ j :=
        hm.trans (gsMoment_le_logScale_pow hchi j hU)
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (gsMoment_nonneg hchi j hu0),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.factorial)]
      apply (div_le_div_iff_of_pos_right
        (by positivity : (0 : ℝ) < j.factorial)).2
      simpa using hm'

lemma gs_alternatingMomentSum_bound_nonneg
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {U : ℝ} (hU : 1 ≤ U) :
    0 ≤ ∑ j ∈ Finset.range (N + 1),
      gsLogScale chi U ^ j / j.factorial := by
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (pow_nonneg (gsLogScale_nonneg hchi hU) j) (by positivity)

lemma intervalIntegrable_gs_solution_kernel
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu0 : 0 ≤ u) :
    IntervalIntegrable (fun t : ℝ ↦ chi t * sigma (u - t)) volume 0 u := by
  have hsub : ContinuousOn (fun t : ℝ ↦ u - t) (Icc 0 u) :=
    continuousOn_const.sub continuousOn_id
  have hmap : MapsTo (fun t : ℝ ↦ u - t) (Icc 0 u) (Ici 0) := by
    intro t ht
    exact mem_Ici.mpr (sub_nonneg.mpr ht.2)
  have hs : ContinuousOn (fun t : ℝ ↦ sigma (u - t)) (uIcc 0 u) := by
    rw [uIcc_of_le hu0]
    exact hsigma.1.comp hsub hmap
  exact (hchi.1 0 u).mul_continuousOn hs

/-- The odd Bonferroni inequalities are the one-sided residual inequalities
of the finite alternating moment sums. -/
theorem gs_oddBonferroni
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) :
    GSOddBonferroni chi sigma := by
  intro u hu0 r
  let N : ℕ := 2 * r + 1
  let U : ℝ := max 1 u
  let B : ℝ := ∑ j ∈ Finset.range (N + 1),
    gsLogScale chi U ^ j / j.factorial
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hU1 : 1 ≤ U := le_max_left _ _
  have huU : u ≤ U := le_max_right _ _
  have hcompare := gs_local_subsolution_le_of_bounded hchi hU
    (U := U) (B := B) (sigma := sigma)
    (tau := gsAlternatingMomentSum chi N)
    (fun v hv0 hv1 ↦ by
      rw [gsAlternatingMomentSum_eq_one_of_le_one chi N hv0 hv1,
        hsigma.2.1 v hv0 hv1])
    (fun v hv1 hvU ↦ by rw [← hsigma.2.2 v hv1])
    (fun v hv1 hvU ↦ by
      let K : ℝ := max 1 v + 1
      have hK1 : 1 ≤ K := by
        dsimp only [K]
        linarith [le_max_left (1 : ℝ) v]
      have hvK : v < K := by
        dsimp only [K]
        linarith [le_max_right (1 : ℝ) v]
      have hid := gs_kernel_convolution_alternating_identity hchi N hK1
        (zero_le_one.trans hv1) hvK
      have hconv := gs_weightedDefect_convolution_moment_nonneg hchi N
        (zero_le_one.trans hv1) hvK
      have hpow : (-1 : ℝ) ^ (N + 1) = 1 := by
        dsimp only [N]
        rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]
        norm_num
      have hcoef : 0 ≤ (-1 : ℝ) ^ (N + 1) / N.factorial := by
        rw [hpow]
        positivity
      rw [hid]
      exact le_add_of_nonneg_right (mul_nonneg hcoef hconv))
    (fun v hv1 hvU ↦ intervalIntegrable_gs_solution_kernel hchi hsigma
      (zero_le_one.trans hv1))
    (fun v hv1 hvU ↦ intervalIntegrable_gsKernel_mul_alternating hchi N
      (zero_le_one.trans hv1))
    (fun v hv ↦ by
      have hs0 : 0 ≤ sigma v :=
        (gs_solution_mem_Icc hchi hsigma v hv.1).1
      have habs := abs_gsAlternatingMomentSum_le hchi N hU1 hv.1 hv.2
      have hB0 : 0 ≤ B := by
        exact gs_alternatingMomentSum_bound_nonneg hchi N hU1
      apply max_le
      · exact (sub_le_self _ hs0).trans ((le_abs_self _).trans habs)
      · exact hB0)
  exact hcompare u ⟨hu0, huU⟩

/-- Local finiteness makes the finite alternating moment expansion equal to
the normalized solution once its truncation dimension lies beyond the whole
compact interval. -/
theorem gs_solution_eq_alternatingMomentSum_of_lt
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) (N : ℕ)
    {U : ℝ} (hU : 1 ≤ U) (hUN : U < (N : ℝ) + 1) :
    ∀ u ∈ Icc (0 : ℝ) U,
      sigma u = gsAlternatingMomentSum chi N u := by
  let B : ℝ := 1 + ∑ j ∈ Finset.range (N + 1),
    gsLogScale chi U ^ j / j.factorial
  apply gs_local_solution_unique_of_bounded hchi (zero_le_one.trans hU)
    (U := U) (B := B)
    hsigma.2.1
    (fun v hv0 hv1 ↦ gsAlternatingMomentSum_eq_one_of_le_one chi N hv0 hv1)
    (fun v hv1 hvU ↦ hsigma.2.2 v hv1)
    (fun v hv1 hvU ↦ (gs_alternatingMomentSum_equation_of_lt hchi N
      (zero_le_one.trans hv1) (hvU.trans_lt hUN)).symm)
    (fun v hv1 hvU ↦ intervalIntegrable_gs_solution_kernel hchi hsigma
      (zero_le_one.trans hv1))
    (fun v hv1 hvU ↦ intervalIntegrable_gsKernel_mul_alternating hchi N
      (zero_le_one.trans hv1))
    (fun v hv ↦ by
      have hs := gs_solution_mem_Icc hchi hsigma v hv.1
      have ha := abs_gsAlternatingMomentSum_le hchi N hU hv.1 hv.2
      have hsabs : |sigma v| ≤ 1 := by
        rw [abs_of_nonneg hs.1]
        exact hs.2
      calc
        |sigma v - gsAlternatingMomentSum chi N v| ≤
            |sigma v| + |gsAlternatingMomentSum chi N v| := abs_sub _ _
        _ ≤ B := by dsimp only [B]; linarith)

/-- A finite moment expansion whose truncation dimension lies beyond a
compact interval is, on that interval, a normalized solution taking values
in `[0,1]`.  This constructs the local filled-kernel solution needed in the
kernel-change argument without any global existence assumption. -/
theorem gs_alternatingMomentSum_mem_Icc_of_lt
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ)
    {U : ℝ} (hU : 1 ≤ U) (hUN : U < (N : ℝ) + 1) :
    ∀ u ∈ Icc (0 : ℝ) U,
      gsAlternatingMomentSum chi N u ∈ Icc (0 : ℝ) 1 := by
  let tau : ℝ → ℝ := gsAlternatingMomentSum chi N
  let C : ℝ := ∑ j ∈ Finset.range (N + 1),
    gsLogScale chi U ^ j / j.factorial
  have hC0 : 0 ≤ C := gs_alternatingMomentSum_bound_nonneg hchi N hU
  have htauBound : ∀ v ∈ Icc (0 : ℝ) U, |tau v| ≤ C := by
    intro v hv
    exact abs_gsAlternatingMomentSum_le hchi N hU hv.1 hv.2
  have htauEq : ∀ v : ℝ, 1 ≤ v → v ≤ U →
      (∫ t : ℝ in 0..v, chi t * tau (v - t)) = v * tau v := by
    intro v hv1 hvU
    exact gs_alternatingMomentSum_equation_of_lt hchi N
      (zero_le_one.trans hv1) (hvU.trans_lt hUN)
  have htauInt : ∀ v : ℝ, 1 ≤ v → v ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ chi t * tau (v - t)) volume 0 v := by
    intro v hv1 hvU
    exact intervalIntegrable_gsKernel_mul_alternating hchi N
      (zero_le_one.trans hv1)
  have hnonneg : ∀ v ∈ Icc (0 : ℝ) U, 0 ≤ tau v := by
    have hcmp := gs_local_subsolution_le_of_bounded hchi
      (zero_le_one.trans hU) (U := U) (B := C)
      (sigma := tau) (tau := fun _v : ℝ ↦ 0)
      (fun v hv0 hv1 ↦ by
        dsimp only [tau]
        rw [gsAlternatingMomentSum_eq_one_of_le_one chi N hv0 hv1]
        norm_num)
      (fun v hv1 hvU ↦ by rw [htauEq v hv1 hvU])
      (fun v hv1 hvU ↦ by simp)
      htauInt
      (fun v hv1 hvU ↦ by simp)
      (fun v hv ↦ by
        apply max_le
        · simpa using (neg_le_abs (tau v)).trans (htauBound v hv)
        · exact hC0)
    intro v hv
    exact hcmp v hv
  have hupper : ∀ v ∈ Icc (0 : ℝ) U, tau v ≤ 1 := by
    have hcmp := gs_local_subsolution_le_of_bounded hchi
      (zero_le_one.trans hU) (U := U) (B := C + 1)
      (sigma := fun _v : ℝ ↦ 1) (tau := tau)
      (fun v hv0 hv1 ↦ by
        dsimp only [tau]
        rw [gsAlternatingMomentSum_eq_one_of_le_one chi N hv0 hv1])
      (fun v hv1 hvU ↦ by
        simpa [gsB] using gsB_le hchi (zero_le_one.trans hv1))
      (fun v hv1 hvU ↦ by rw [htauEq v hv1 hvU])
      (fun v hv1 hvU ↦ by
        convert hchi.1 0 v using 1
        ext t
        simp)
      htauInt
      (fun v hv ↦ by
        apply max_le
        · have ha := htauBound v hv
          have ht : tau v ≤ C := (le_abs_self (tau v)).trans ha
          linarith
        · linarith)
    intro v hv
    exact hcmp v hv
  intro u hu
  exact ⟨hnonneg u hu, hupper u hu⟩

end

end Erdos783
