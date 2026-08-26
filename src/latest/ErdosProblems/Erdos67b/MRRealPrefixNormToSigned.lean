import ErdosProblems.Erdos67b.MRGranvilleSoundararajanRealPrefixStability

/-!
# From norm stability to signed stability for real prefix means

Real prefix means can change sign only by crossing zero.  Their adjacent
increments are `O(1/N)`, so uniform stability of their absolute values on
an integer interval already gives uniform stability of the means themselves.
-/

open scoped ComplexConjugate

namespace Erdos67b

noncomputable section

/-- A one-bounded prefix mean changes by at most `2/(N+1)` in one step. -/
theorem norm_positivePrefixMean_succ_sub_le
    {f : ℕ → ℂ} (hbound : ∀ n, ‖f n‖ ≤ 1)
    {N : ℕ} (hN : 0 < N) :
    ‖positivePrefixMean f (N + 1) - positivePrefixMean f N‖ ≤
      2 / (N + 1 : ℕ) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1C : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero N)
  have hsum : positivePrefixSum f (N + 1) =
      positivePrefixSum f N + f (N + 1) := by
    unfold positivePrefixSum
    rw [Finset.sum_range_succ]
    ring
  have hmean : positivePrefixMean f (N + 1) - positivePrefixMean f N =
      (f (N + 1) - positivePrefixMean f N) / ((N + 1 : ℕ) : ℂ) := by
    unfold positivePrefixMean
    rw [hsum]
    field_simp [hNC, hN1C]
    push_cast
    ring
  have hmeanNorm : ‖positivePrefixMean f N‖ ≤ 1 := by
    have hprefix : positivePrefixSum f N = ∑ n ∈ Finset.Ioc 0 N, f n := by
      have h := sum_Ioc_eq_positivePrefixSum_sub f (Nat.zero_le N)
      have hzero : positivePrefixSum f 0 = 0 := by simp [positivePrefixSum]
      rw [hzero, sub_zero] at h
      exact h.symm
    unfold positivePrefixMean
    rw [hprefix]
    rw [norm_div, Complex.norm_natCast]
    have hNR : (0 : ℝ) < N := by positivity
    apply (div_le_iff₀ hNR).2
    calc
      ‖∑ n ∈ Finset.Ioc 0 N, f n‖ ≤
          ∑ n ∈ Finset.Ioc 0 N, ‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc 0 N, (1 : ℝ) := by
        exact Finset.sum_le_sum fun n _ ↦ hbound n
      _ = N := by simp
      _ = 1 * N := by ring
  rw [hmean, norm_div, Complex.norm_natCast]
  have hnum : ‖f (N + 1) - positivePrefixMean f N‖ ≤ 2 := by
    calc
      _ ≤ ‖f (N + 1)‖ + ‖positivePrefixMean f N‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hbound _) hmeanNorm
      _ = 2 := by norm_num
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- Discrete zero-crossing principle.  Uniform stability of absolute values,
together with a uniform adjacent-step bound, controls the signed values. -/
theorem abs_sub_le_three_mul_add_two_mul_of_uniform_abs_stable
    (g : ℕ → ℝ) {X U : ℕ} {delta eta : ℝ}
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (habs : ∀ n, X ≤ n → n ≤ U →
      abs (|g n| - |g X|) ≤ delta)
    (hstep : ∀ n, X ≤ n → n < U → |g (n + 1) - g n| ≤ eta) :
    ∀ n, X ≤ n → n ≤ U →
      |g n - g X| ≤ 3 * delta + 2 * eta := by
  have hsmall (n : ℕ) (hnX : X ≤ n) (hnU : n ≤ U)
      (hbase : |g X| ≤ delta + eta) :
      |g n - g X| ≤ 3 * delta + 2 * eta := by
    have hnabs := habs n hnX hnU
    have hnle : |g n| ≤ |g X| + delta := by
      rw [abs_le] at hnabs
      linarith
    calc
      |g n - g X| ≤ |g n| + |g X| := abs_sub _ _
      _ ≤ (|g X| + delta) + |g X| := by linarith
      _ ≤ 3 * delta + 2 * eta := by linarith
  intro n hnX hnU
  by_cases hbase : |g X| ≤ delta + eta
  · exact hsmall n hnX hnU hbase
  · have hbaseLarge : delta + eta < |g X| := lt_of_not_ge hbase
    have hgXne : g X ≠ 0 := by
      intro h
      rw [h, abs_zero] at hbaseLarge
      linarith
    rcases lt_or_gt_of_ne hgXne with hgXneg | hgXpos
    · have hnonpos : ∀ m, X ≤ m → m ≤ U → g m ≤ 0 := by
        intro m hmX hmU
        induction m, hmX using Nat.le_induction with
        | base => exact hgXneg.le
        | succ m hmX ih =>
            have hmU' : m < U := by omega
            have hm1U : m + 1 ≤ U := by omega
            by_contra hm1
            have hm1pos : 0 < g (m + 1) := lt_of_not_ge hm1
            have hm1abs := habs (m + 1) (by omega) hm1U
            have hm1large : eta < |g (m + 1)| := by
              rw [abs_le] at hm1abs
              linarith
            rw [abs_of_pos hm1pos] at hm1large
            have hmnonpos : g m ≤ 0 := ih (by omega)
            have hcross : eta < |g (m + 1) - g m| := by
              rw [abs_of_pos (sub_pos.mpr
                (lt_of_le_of_lt hmnonpos hm1pos))]
              linarith
            exact (not_lt_of_ge (hstep m hmX hmU')) hcross
      have hn := hnonpos n hnX hnU
      have h := habs n hnX hnU
      rw [abs_of_nonpos hn, abs_of_nonpos hgXneg.le] at h
      have heq : |g n - g X| = |-g n - -g X| := by
        rw [show -g n - -g X = -(g n - g X) by ring, abs_neg]
      rw [heq]
      exact h.trans (by linarith)
    · have hnonneg : ∀ m, X ≤ m → m ≤ U → 0 ≤ g m := by
        intro m hmX hmU
        induction m, hmX using Nat.le_induction with
        | base => exact hgXpos.le
        | succ m hmX ih =>
            have hmU' : m < U := by omega
            have hm1U : m + 1 ≤ U := by omega
            by_contra hm1
            have hm1neg : g (m + 1) < 0 := lt_of_not_ge hm1
            have hm1abs := habs (m + 1) (by omega) hm1U
            have hm1large : eta < |g (m + 1)| := by
              rw [abs_le] at hm1abs
              linarith
            rw [abs_of_neg hm1neg] at hm1large
            have hmnonneg : 0 ≤ g m := ih (by omega)
            have hcross : eta < |g (m + 1) - g m| := by
              rw [abs_of_neg (sub_neg.mpr
                (lt_of_lt_of_le hm1neg hmnonneg))]
              linarith
            exact (not_lt_of_ge (hstep m hmX hmU')) hcross
      have hn := hnonneg n hnX hnU
      have h := habs n hnX hnU
      rw [abs_of_nonneg hn, abs_of_nonneg hgXpos.le] at h
      exact h.trans (by linarith)

/-- Prefix-mean specialization of the discrete zero-crossing principle. -/
theorem uniform_positivePrefixMean_stable_of_real_of_norm_stable
    {f : ℕ → ℂ}
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X U : ℕ} (hX : 1 ≤ X) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hnorm : ∀ Z : ℕ, X ≤ Z → Z ≤ U →
      |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤ delta) :
    ∀ Z : ℕ, X ≤ Z → Z ≤ U →
      ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        3 * delta + 4 / X := by
  let g : ℕ → ℝ := fun N ↦ (positivePrefixMean f N).re
  have him (N : ℕ) : (positivePrefixMean f N).im = 0 :=
    positivePrefixMean_im_eq_zero_of_real hreal N
  have hnormReal (N : ℕ) : ‖positivePrefixMean f N‖ = |g N| := by
    have heq : positivePrefixMean f N = ((positivePrefixMean f N).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him N
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hmeanReal (N : ℕ) : positivePrefixMean f N = (g N : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him N
  have habs : ∀ N, X ≤ N → N ≤ U →
      abs (|g N| - |g X|) ≤ delta := by
    intro N hXN hNU
    simpa only [← hnormReal] using hnorm N hXN hNU
  have hstep : ∀ N, X ≤ N → N < U →
      |g (N + 1) - g N| ≤ 2 / X := by
    intro N hXN hNU
    have hcomplex := norm_positivePrefixMean_succ_sub_le hbound
      (show 0 < N by omega)
    have hre : |g (N + 1) - g N| =
        ‖positivePrefixMean f (N + 1) - positivePrefixMean f N‖ := by
      rw [hmeanReal (N + 1), hmeanReal N,
        show (g (N + 1) : ℂ) - (g N : ℂ) =
          ((g (N + 1) - g N : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hre]
    exact hcomplex.trans (by
      have hXR : (0 : ℝ) < X := by positivity
      exact div_le_div_of_nonneg_left (by norm_num) hXR
        (by exact_mod_cast (show X ≤ N + 1 by omega)))
  intro Z hXZ hZU
  have hsigned := abs_sub_le_three_mul_add_two_mul_of_uniform_abs_stable
    g hdelta (show 0 ≤ (2 : ℝ) / X by positivity) habs hstep Z hXZ hZU
  have hre : ‖positivePrefixMean f Z - positivePrefixMean f X‖ =
      |g Z - g X| := by
    rw [hmeanReal Z, hmeanReal X,
      show (g Z : ℂ) - (g X : ℂ) =
        ((g Z - g X : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hre]
  convert hsigned using 1 <;> ring

end

end Erdos67b
