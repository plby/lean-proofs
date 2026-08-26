import ErdosProblems.Erdos67b.LSeriesLogPhaseBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

open scoped BigOperators
open Set MeasureTheory intervalIntegral

namespace Erdos67b.LSeriesHeightTail

noncomputable section

def shiftPow (s : ℂ) (u x : ℝ) : ℂ :=
  (((x + u : ℝ) : ℂ) ^ (-s))

lemma hasDerivAt_shiftPow {s : ℂ} {u x : ℝ} (hxu : x + u ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (shiftPow s u) ((-s) * (((x + u : ℝ) : ℂ) ^ (-s - 1))) x := by
  unfold shiftPow
  convert (hasDerivAt_ofReal_cpow_const hxu (neg_ne_zero.mpr hs)).comp_add_const x u using 1 <;>
    ring

lemma integral_shiftPow {s : ℂ} {u a b : ℝ} (ha : 0 < a + u)
    (hab : a ≤ b) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (∫ x in a..b, shiftPow s u x) =
      (((b + u : ℝ) : ℂ) ^ (1 - s) - (((a + u : ℝ) : ℂ) ^ (1 - s))) / (1 - s) := by
  let F : ℝ → ℂ := fun x ↦ (((x + u : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
  have hs10 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (shiftPow s u x) x := by
    intro x hx
    have hxu : x + u ≠ 0 := ne_of_gt (ha.trans_le (by linarith [hx.1]))
    have h := (hasDerivAt_ofReal_cpow_const hxu hs10).comp_add_const x u
      |>.mul_const (1 - s)⁻¹
    simpa [F, shiftPow, div_eq_mul_inv, show 1 - s - 1 = -s by ring,
      hs10, mul_assoc, mul_left_comm, mul_comm] using h
  have hcont : ContinuousOn F (Set.Icc a b) :=
    HasDerivAt.continuousOn hderiv
  have hint : IntervalIntegrable (shiftPow s u) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_shiftPow (ne_of_gt (ha.trans_le (by linarith [hx.1])))
      hs0).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun x hx ↦ hderiv x (Set.Ioo_subset_Icc_self hx)) hint]
  simp only [F]
  ring

lemma norm_shiftPow_deriv {s : ℂ} {u x : ℝ} (hxu : 0 < x + u) :
    ‖(-s) * (((x + u : ℝ) : ℂ) ^ (-s - 1))‖ =
      ‖s‖ * (x + u) ^ (-s.re - 1) := by
  rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxu]
  congr 2

lemma norm_shiftPow_sub_left_le {s : ℂ} {u a x : ℝ}
    (hu : 0 ≤ u) (ha : 0 < a) (hs0 : s ≠ 0) (hsigma : 0 ≤ s.re)
    (hx : x ∈ Set.Icc a (a + 1)) :
    ‖shiftPow s u x - shiftPow s u a‖ ≤
      (‖s‖ * (a + u) ^ (-s.re - 1)) * (x - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' (a := a) (b := a + 1)
      (f := shiftPow s u)
      (f' := fun y ↦ (-s) * (((y + u : ℝ) : ℂ) ^ (-s - 1))) ?_ ?_ x hx
  · intro y hy
    exact (hasDerivAt_shiftPow (ne_of_gt (by linarith [hy.1])) hs0).hasDerivWithinAt
  · intro y hy
    rw [norm_shiftPow_deriv (by linarith [hy.1])]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hy.1]) (by linarith))
      (norm_nonneg s)

lemma norm_shiftPow_sub_cellIntegral_le {s : ℂ} {u a : ℝ}
    (hu : 0 ≤ u) (ha : 0 < a) (hs0 : s ≠ 0) (hsigma : 0 ≤ s.re) :
    ‖shiftPow s u a - ∫ x in a..a + 1, shiftPow s u x‖ ≤
      ‖s‖ * (a + u) ^ (-s.re - 1) := by
  have hfint : IntervalIntegrable (shiftPow s u) MeasureTheory.volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (hasDerivAt_shiftPow (ne_of_gt (by linarith [hx.1])) hs0).continuousAt.continuousWithinAt
  calc
    ‖shiftPow s u a - ∫ x in a..a + 1, shiftPow s u x‖ =
        ‖∫ x in a..a + 1, (shiftPow s u a - shiftPow s u x)‖ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hfint]
      simp
    _ ≤ (‖s‖ * (a + u) ^ (-s.re - 1)) * |(a + 1) - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [norm_sub_rev]
      have hxi : x ∈ Set.Icc a (a + 1) := by
        rw [← Set.uIcc_of_le (by linarith)]
        exact Set.uIoc_subset_uIcc hx
      have h := norm_shiftPow_sub_left_le hu ha hs0 hsigma hxi
      have hC : 0 ≤ ‖s‖ * (a + u) ^ (-s.re - 1) :=
        mul_nonneg (norm_nonneg s) (Real.rpow_nonneg (by linarith) _)
      exact h.trans (by
        have hxsub : x - a ≤ 1 := by linarith [hxi.2]
        simpa using mul_le_mul_of_nonneg_left hxsub hC)
    _ = ‖s‖ * (a + u) ^ (-s.re - 1) := by norm_num

lemma sum_Icc_shift_decay_le {u sigma : ℝ} {A B : ℕ}
    (hu : 0 ≤ u) (hsigma : 1 ≤ sigma) (hA : 3 ≤ A) (hAB : A ≤ B) :
    ∑ n ∈ Finset.Icc A B, ((n : ℝ) + u) ^ (-sigma - 1) ≤
      ((A - 1 : ℕ) : ℝ)⁻¹ := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-2 : ℝ)
  have hpoint : ∀ n ∈ Finset.Icc A B,
      ((n : ℝ) + u) ^ (-sigma - 1) ≤ f n := by
    intro n hn
    have hnA : A ≤ n := (Finset.mem_Icc.mp hn).1
    have hnNat : 1 ≤ n := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    calc
      ((n : ℝ) + u) ^ (-sigma - 1) ≤ ((n : ℝ) + u) ^ (-2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      _ ≤ (n : ℝ) ^ (-2 : ℝ) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      _ = f n := rfl
  calc
    _ ≤ ∑ n ∈ Finset.Icc A B, f n := Finset.sum_le_sum hpoint
    _ = ∑ n ∈ Finset.range (B + 1 - A), f (A + n) := by
      rw [show Finset.Icc A B = Finset.Ico A (B + 1) by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega]
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.cast_add]
    _ ≤ ∑' n : ℕ, f (A + n) := by
      apply Summable.sum_le_tsum
      · intro n hn
        positivity
      · have hfSum : Summable (fun n : ℕ ↦ f n) := by
          simpa [f] using (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
        simpa [add_comm] using (summable_nat_add_iff A).mpr hfSum
    _ ≤ ∫ x in Set.Ioi ((A - 1 : ℕ) : ℝ), f x := by
      have hmain := AntitoneOn.tsum_comp_add_le_integral (f := f) (A - 1) ?_ ?_ ?_
      · rw [show (fun n : ℕ ↦ f ((A : ℝ) + n)) =
            (fun n : ℕ ↦ f ((n + (A - 1) + 1 : ℕ) : ℝ)) by
          funext n
          simp only [Nat.add_assoc, Nat.sub_add_cancel (show 1 ≤ A by omega), Nat.cast_add]
          congr 1
          ring]
        exact hmain
      · intro x hx y hy hxy
        have hAm1R : (0 : ℝ) < (A - 1 : ℕ) := by exact_mod_cast (show 0 < A - 1 by omega)
        exact Real.rpow_le_rpow_of_nonpos (hAm1R.trans_le hx) hxy (by norm_num)
      · exact integrableOn_Ioi_rpow_of_lt (by norm_num)
          (by exact_mod_cast (show 0 < A - 1 by omega))
      · intro x hx
        have hAm1R : (0 : ℝ) < (A - 1 : ℕ) := by exact_mod_cast (show 0 < A - 1 by omega)
        exact Real.rpow_nonneg (le_of_lt (hAm1R.trans hx)) _
    _ = ((A - 1 : ℕ) : ℝ)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num)
        (by exact_mod_cast (show 0 < A - 1 by omega))]
      norm_num [Real.rpow_neg_one]

lemma norm_sum_Icc_shiftPow_sub_integral_le {s : ℂ} {u : ℝ} {A B : ℕ}
    (hu : 0 ≤ u) (hs0 : s ≠ 0) (hsigma : 1 ≤ s.re) (hA : 3 ≤ A) (hAB : A ≤ B) :
    ‖(∑ n ∈ Finset.Icc A B, shiftPow s u n) -
        ∫ x in (A : ℝ)..(B : ℝ) + 1, shiftPow s u x‖ ≤
      ‖s‖ * ((A - 1 : ℕ) : ℝ)⁻¹ := by
  have hint : ∀ n ∈ Set.Ico A (B + 1),
      IntervalIntegrable (shiftPow s u) MeasureTheory.volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact (hasDerivAt_shiftPow (ne_of_gt (by
      have hnA : A ≤ n := hn.1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      linarith [hx.1])) hs0).continuousAt.continuousWithinAt
  have hInt :
      ∑ n ∈ Finset.Icc A B, ∫ x in (n : ℝ)..(n : ℝ) + 1, shiftPow s u x =
        ∫ x in (A : ℝ)..(B : ℝ) + 1, shiftPow s u x := by
    rw [show Finset.Icc A B = Finset.Ico A (B + 1) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (intervalIntegral.sum_integral_adjacent_intervals_Ico
        (f := shiftPow s u) (μ := MeasureTheory.volume)
        (a := fun n : ℕ ↦ (n : ℝ)) (m := A) (n := B + 1)
        (by omega) hint)
  calc
    _ = ‖∑ n ∈ Finset.Icc A B,
        (shiftPow s u n - ∫ x in (n : ℝ)..(n : ℝ) + 1, shiftPow s u x)‖ := by
      rw [Finset.sum_sub_distrib, hInt]
    _ ≤ ∑ n ∈ Finset.Icc A B,
        ‖shiftPow s u n - ∫ x in (n : ℝ)..(n : ℝ) + 1, shiftPow s u x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc A B, ‖s‖ * ((n : ℝ) + u) ^ (-s.re - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_shiftPow_sub_cellIntegral_le hu (by
        have hnA : A ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (show 0 < n by omega)) hs0 (by linarith)
    _ = ‖s‖ * ∑ n ∈ Finset.Icc A B, ((n : ℝ) + u) ^ (-s.re - 1) := by
      rw [Finset.mul_sum]
    _ ≤ ‖s‖ * ((A - 1 : ℕ) : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_shift_decay_le hu hsigma hA hAB) (norm_nonneg s)

lemma norm_integral_shiftPow_le_one {s : ℂ} {u : ℝ} {A B : ℕ}
    (hu : 0 ≤ u) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsigma : 1 ≤ s.re)
    (hA : 3 ≤ A) (hAB : A ≤ B) (him : 3 ≤ |s.im|) :
    ‖∫ x in (A : ℝ)..(B : ℝ) + 1, shiftPow s u x‖ ≤ 1 := by
  have hAu : 0 < (A : ℝ) + u := by positivity
  rw [integral_shiftPow hAu (by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith) hs0 hs1, norm_div]
  have hleft : ‖(((A : ℝ) + u : ℝ) : ℂ) ^ (1 - s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hAu]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have hAR : (3 : ℝ) ≤ A := by exact_mod_cast hA
      linarith
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  have hright : ‖(((B : ℝ) + 1 + u : ℝ) : ℂ) ^ (1 - s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have hBR : (3 : ℝ) ≤ B := by exact_mod_cast (hA.trans hAB)
      linarith
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  have hnum :
      ‖(((B : ℝ) + 1 + u : ℝ) : ℂ) ^ (1 - s) -
        (((A : ℝ) + u : ℝ) : ℂ) ^ (1 - s)‖ ≤ 2 := by
    calc
      _ ≤ ‖(((B : ℝ) + 1 + u : ℝ) : ℂ) ^ (1 - s)‖ +
          ‖(((A : ℝ) + u : ℝ) : ℂ) ^ (1 - s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hright hleft
      _ = 2 := by norm_num
  have hden : 3 ≤ ‖1 - s‖ := by
    have hi := Complex.abs_im_le_norm (1 - s)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hi
    exact him.trans hi
  exact (div_le_one (by positivity)).mpr (hnum.trans (by linarith))

lemma norm_mul_inv_nat_sub_one_le_three {s : ℂ} {A : ℕ}
    (hsigma : 1 ≤ s.re) (hsigma2 : s.re ≤ 2) (hA : 3 ≤ A)
    (himA : |s.im| ≤ A) :
    ‖s‖ * ((A - 1 : ℕ) : ℝ)⁻¹ ≤ 3 := by
  have hnorm : ‖s‖ ≤ 2 + (A : ℝ) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_nonneg (by linarith)]
      _ ≤ 2 + (A : ℝ) := add_le_add hsigma2 (by exact_mod_cast himA)
  have hAm1 : (0 : ℝ) < (A - 1 : ℕ) := by
    exact_mod_cast (show 0 < A - 1 by omega)
  rw [mul_inv_le_iff₀ hAm1]
  have hAR : (3 : ℝ) ≤ A := by exact_mod_cast hA
  have hcast : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  linarith

lemma norm_sum_Icc_shiftPow_le_four {s : ℂ} {u : ℝ} {A B : ℕ}
    (hu : 0 ≤ u) (hsigma : 1 ≤ s.re) (hsigma2 : s.re ≤ 2)
    (hA : 3 ≤ A) (hAB : A ≤ B) (him : 3 ≤ |s.im|) (himA : |s.im| ≤ A) :
    ‖∑ n ∈ Finset.Icc A B, shiftPow s u n‖ ≤ 4 := by
  have hs0 : s ≠ 0 := by
    intro hs
    simp only [hs, Complex.zero_im, abs_zero] at him
    norm_num at him
  have hs1 : s ≠ 1 := by
    intro hs
    simp only [hs, Complex.one_im, abs_zero] at him
    norm_num at him
  let I : ℂ := ∫ x in (A : ℝ)..(B : ℝ) + 1, shiftPow s u x
  calc
    ‖∑ n ∈ Finset.Icc A B, shiftPow s u n‖ ≤
        ‖(∑ n ∈ Finset.Icc A B, shiftPow s u n) - I‖ + ‖I‖ := by
      have := norm_add_le
        ((∑ n ∈ Finset.Icc A B, shiftPow s u n) - I) I
      simpa using this
    _ ≤ 3 + 1 := add_le_add
      ((norm_sum_Icc_shiftPow_sub_integral_le hu hs0 hsigma hA hAB).trans
        (norm_mul_inv_nat_sub_one_le_three hsigma hsigma2 hA himA))
      (norm_integral_shiftPow_le_one hu hs0 hs1 hsigma hA hAB him)
    _ = 4 := by norm_num

lemma summable_shiftPow {s : ℂ} {u : ℝ} (hu : 0 ≤ u) (hsigma : 1 < s.re) :
    Summable (fun n : ℕ ↦ shiftPow s u n) := by
  rw [← summable_nat_add_iff 1]
  apply Summable.of_norm
  have hp := (Real.summable_one_div_nat_add_rpow (1 + u) s.re).mpr hsigma
  convert hp using 1
  funext n
  unfold shiftPow
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity :
    0 < ((n + 1 : ℕ) : ℝ) + u)]
  simp only [Complex.neg_re]
  have hbase : ((n + 1 : ℕ) : ℝ) + u = |(n : ℝ) + (1 + u)| := by
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + (1 + u))]
    push_cast
    ring
  rw [hbase, one_div, Real.rpow_neg (abs_nonneg _)]

lemma norm_tsum_shiftPow_nat_add_le_four {s : ℂ} {u : ℝ} {A : ℕ}
    (hu : 0 ≤ u) (hsigma : 1 < s.re) (hsigma2 : s.re ≤ 2)
    (hA : 3 ≤ A) (him : 3 ≤ |s.im|) (himA : |s.im| ≤ A) :
    ‖∑' n : ℕ, shiftPow s u (((n + A : ℕ) : ℝ))‖ ≤ 4 := by
  apply Erdos67b.LSeriesLogPhaseBridge.norm_tsum_nat_add_le_of_Icc_bound
    (fun n : ℕ ↦ shiftPow s u n) (summable_shiftPow hu hsigma) (by norm_num)
  intro B hAB
  exact norm_sum_Icc_shiftPow_le_four hu hsigma.le hsigma2 hA hAB him himA

lemma nat_add_mul_cpow_neg_eq {q j M : ℕ} [NeZero q] (s : ℂ) :
    ((j + q * M : ℕ) : ℂ) ^ (-s) =
      (q : ℂ) ^ (-s) * shiftPow s ((j : ℝ) / q) M := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hreal : ((j + q * M : ℕ) : ℝ) =
      (q : ℝ) * ((M : ℝ) + (j : ℝ) / q) := by
    push_cast
    field_simp
    ring
  rw [← Complex.ofReal_natCast, hreal, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  rfl

lemma dirichletCharacter_add_mul {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ZMod q) (M : ℕ) :
    chi (((j.val + q * M : ℕ) : ZMod q)) = chi j := by
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_self, zero_mul, add_zero]

lemma character_LSeries_term_residue_tail_eq {q A m : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) (j : ZMod q) (hA : 0 < A) :
    LSeries.term (fun n : ℕ ↦ chi n) s (j.val + q * m + q * A) =
      (chi j * (q : ℂ) ^ (-s)) *
        shiftPow s ((j.val : ℝ) / q) (((m + A : ℕ) : ℝ)) := by
  rw [show j.val + q * m + q * A = j.val + q * (m + A) by
    rw [Nat.mul_add, Nat.add_assoc]]
  rw [LSeries.term_of_ne_zero (by
    have hq : 0 < q := NeZero.pos q
    have : 0 < q * (m + A) := Nat.mul_pos hq (by omega)
    omega)]
  rw [dirichletCharacter_add_mul, div_eq_mul_inv, ← Complex.cpow_neg,
    nat_add_mul_cpow_neg_eq]
  ring

lemma norm_character_LSeries_aligned_tail_le {q A : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hsigma : 1 < s.re) (hsigma2 : s.re ≤ 2) (hA : 3 ≤ A)
    (him : 3 ≤ |s.im|) (himA : |s.im| ≤ A) :
    ‖∑' n : ℕ, LSeries.term (fun k : ℕ ↦ chi k) s (n + q * A)‖ ≤
      4 * q := by
  have hf : Summable (LSeries.term (fun k : ℕ ↦ chi k) s) := by
    exact LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ chi.norm_le_one n) hsigma
  have hftail : Summable
      (fun n : ℕ ↦ LSeries.term (fun k : ℕ ↦ chi k) s (n + q * A)) :=
    (summable_nat_add_iff (q * A)).mpr (by simpa [add_comm] using hf)
  rw [Nat.sumByResidueClasses hftail q]
  calc
    ‖∑ j : ZMod q, ∑' m : ℕ,
        LSeries.term (fun k : ℕ ↦ chi k) s (j.val + q * m + q * A)‖ ≤
        ∑ j : ZMod q, ‖∑' m : ℕ,
          LSeries.term (fun k : ℕ ↦ chi k) s (j.val + q * m + q * A)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod q, 4 := by
      apply Finset.sum_le_sum
      intro j hj
      have heq :
          (∑' m : ℕ, LSeries.term (fun k : ℕ ↦ chi k) s
            (j.val + q * m + q * A)) =
            (chi j * (q : ℂ) ^ (-s)) *
              (∑' m : ℕ, shiftPow s ((j.val : ℝ) / q)
                (((m + A : ℕ) : ℝ))) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro m
        exact character_LSeries_term_residue_tail_eq chi s j (by omega)
      rw [heq, norm_mul]
      have hqpow : ‖(q : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos
            (by exact_mod_cast (NeZero.pos q) : (0 : ℝ) < q)]
        simp only [Complex.neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (NeZero.pos q)) (by linarith)
      have hcoef : ‖chi j * (q : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖(q : ℂ) ^ (-s)‖ ≤ 1 * 1 :=
            mul_le_mul (chi.norm_le_one j) hqpow (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hu : 0 ≤ (j.val : ℝ) / q := by positivity
      have htail := norm_tsum_shiftPow_nat_add_le_four
        hu hsigma hsigma2 hA him himA
      calc
        ‖chi j * (q : ℂ) ^ (-s)‖ *
            ‖∑' m : ℕ, shiftPow s ((j.val : ℝ) / q) (((m + A : ℕ) : ℝ))‖ ≤
            1 * 4 := mul_le_mul hcoef htail (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    _ = 4 * q := by simp [mul_comm]

lemma norm_character_LSeries_term_le_inv_start {q A n : ℕ}
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hsigma : 1 ≤ s.re)
    (hA : 0 < A) (hAn : A ≤ n) :
    ‖LSeries.term (fun k : ℕ ↦ chi k) s n‖ ≤ ((A : ℝ))⁻¹ := by
  have hn : n ≠ 0 := by omega
  rw [LSeries.norm_term_eq, if_neg hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  calc
    ‖chi n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
      exact (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hnpos _)).mpr
        (chi.norm_le_one n)
    _ = (n : ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg (le_of_lt hnpos), one_div]
    _ ≤ (n : ℝ) ^ (-1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
    _ ≤ (A : ℝ) ^ (-1 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos hApos hAnR (by norm_num)
    _ = ((A : ℝ))⁻¹ := Real.rpow_neg_one A

lemma norm_character_LSeries_gap_le {q A : ℕ}
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hsigma : 1 ≤ s.re)
    (hA : 0 < A) :
    ‖∑ n ∈ Finset.Ico A (q * A),
        LSeries.term (fun k : ℕ ↦ chi k) s n‖ ≤ q := by
  calc
    _ ≤ ∑ n ∈ Finset.Ico A (q * A),
        ‖LSeries.term (fun k : ℕ ↦ chi k) s n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico A (q * A), ((A : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_character_LSeries_term_le_inv_start chi hsigma hA
        (Finset.mem_Ico.mp hn).1
    _ = ((q * A - A : ℕ) : ℝ) * ((A : ℝ))⁻¹ := by
      simp
    _ ≤ ((q * A : ℕ) : ℝ) * ((A : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (q * A) A)
        (inv_nonneg.mpr (Nat.cast_nonneg A))
    _ = q := by
      push_cast
      field_simp

lemma norm_character_LSeries_sub_sum_range_le_five_mul {q A : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hsigma : 1 < s.re) (hsigma2 : s.re ≤ 2) (hA : 3 ≤ A)
    (him : 3 ≤ |s.im|) (himA : |s.im| ≤ A) :
    ‖LSeries (fun k : ℕ ↦ chi k) s -
        ∑ n ∈ Finset.range A, LSeries.term (fun k : ℕ ↦ chi k) s n‖ ≤
      5 * q := by
  let f : ℕ → ℂ := LSeries.term (fun k : ℕ ↦ chi k) s
  have hf : Summable f := by
    exact LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ chi.norm_le_one n) hsigma
  have hq : 1 ≤ q := NeZero.one_le
  have hAqA : A ≤ q * A := by nlinarith
  have hsplit :
      LSeries (fun k : ℕ ↦ chi k) s - ∑ n ∈ Finset.range A, f n =
        (∑ n ∈ Finset.Ico A (q * A), f n) + ∑' n : ℕ, f (n + q * A) := by
    change (∑' n : ℕ, f n) - ∑ n ∈ Finset.range A, f n = _
    rw [← hf.sum_add_tsum_nat_add (q * A)]
    rw [← Finset.sum_range_add_sum_Ico f hAqA]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖∑ n ∈ Finset.Ico A (q * A), f n‖ +
        ‖∑' n : ℕ, f (n + q * A)‖ := norm_add_le _ _
    _ ≤ q + 4 * q := add_le_add
      (norm_character_LSeries_gap_le chi hsigma.le (by omega))
      (norm_character_LSeries_aligned_tail_le chi hsigma hsigma2 hA him himA)
    _ = 5 * q := by ring

/-- Beyond the height, a Dirichlet-character L-series has a uniformly bounded
tail depending only linearly on the conductor. -/
theorem norm_character_LSeries_height_tail_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma v : ℝ}
    (hsigma : 1 < sigma) (hsigma2 : sigma ≤ 2) (hv : 3 ≤ |v|) :
    ‖LSeries (fun k : ℕ ↦ chi k) ((sigma : ℂ) + Complex.I * (v : ℂ)) -
        ∑ n ∈ Finset.range (Nat.ceil |v|),
          LSeries.term (fun k : ℕ ↦ chi k)
            ((sigma : ℂ) + Complex.I * (v : ℂ)) n‖ ≤
      5 * q := by
  apply norm_character_LSeries_sub_sum_range_le_five_mul chi
  · simpa using hsigma
  · simpa using hsigma2
  · exact_mod_cast hv.trans (Nat.le_ceil |v|)
  · simpa using hv
  · simpa using (Nat.le_ceil |v|)

end

end Erdos67b.LSeriesHeightTail
