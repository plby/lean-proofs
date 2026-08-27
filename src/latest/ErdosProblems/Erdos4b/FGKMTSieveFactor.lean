/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileDenominator

/-!
# The actual one-variable sieve profile

The function agrees with the rational cutoff on the nonnegative axis,
is globally smooth, and has explicit bounds in its two scale parameters.
-/

namespace Erdos4b.FGKMT

noncomputable section

def sieveFactor (T U t : ℝ) : ℝ := sieveCutoff (t / U) / profileDenominator (T * t)

theorem sieveFactor_contDiff (T U : ℝ) {n : ℕ∞} : ContDiff ℝ n (sieveFactor T U) := by
  unfold sieveFactor
  exact (sieveCutoff_contDiff.comp (by fun_prop)).div
    (profileDenominator_contDiff.comp (by fun_prop)) (fun t => (profileDenominator_pos _).ne')

theorem sieveFactor_nonneg (T U t : ℝ) : 0 ≤ sieveFactor T U t :=
  div_nonneg (sieveCutoff_nonneg _) (profileDenominator_pos _).le

theorem sieveFactor_eq {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (U : ℝ) :
    sieveFactor T U t = sieveCutoff (t / U) / (1 + T * t) := by
  rw [sieveFactor, profileDenominator_eq_linear (by nlinarith [mul_nonneg hT ht])]

theorem sieveFactor_le_inv {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (U : ℝ) :
    sieveFactor T U t ≤ 1 / (1 + T * t) := by
  rw [sieveFactor_eq hT ht]
  exact div_le_div_of_nonneg_right (sieveCutoff_le_one _) (by positivity)

theorem sieveFactor_le_one {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (U : ℝ) :
    sieveFactor T U t ≤ 1 := by
  refine (sieveFactor_le_inv hT ht U).trans ?_
  apply (div_le_one (by positivity : 0 < 1 + T * t)).mpr
  linarith [mul_nonneg hT ht]

theorem sieveFactor_eq_inv {T U t : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (ht : 0 ≤ t)
    (htU : t ≤ (9 / 10) * U) : sieveFactor T U t = 1 / (1 + T * t) := by
  rw [sieveFactor_eq hT ht, sieveCutoff_one_of_le ((div_le_iff₀ hU).mpr htU)]

theorem sieveFactor_zero_of_ge {U t : ℝ} (hU : 0 < U) (ht : U ≤ t) (T : ℝ) :
    sieveFactor T U t = 0 := by
  have htu : 1 ≤ t / U := (le_div_iff₀ hU).mpr (by simpa only [one_mul] using ht)
  rw [sieveFactor, sieveCutoff_zero_of_one_le htu, zero_div]

theorem sieveFactor_antitoneOn {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) :
    AntitoneOn (sieveFactor T U) (Set.Ici 0) := by
  intro t ht u hu htu
  change 0 ≤ t at ht
  change 0 ≤ u at hu
  rw [sieveFactor_eq hT ht U, sieveFactor_eq hT hu U]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + T * u)
    (by positivity : 0 < 1 + T * t)).mpr
  have hcut := sieveCutoff_antitone (div_le_div_of_nonneg_right htu hU.le)
  have hden : 1 + T * t ≤ 1 + T * u := by nlinarith
  exact mul_le_mul hcut hden (by positivity) (sieveCutoff_nonneg _)

theorem sieveFactor_deriv {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (U : ℝ) :
    deriv (sieveFactor T U) t =
      (deriv sieveCutoff (t / U) / U - T * sieveFactor T U t) / (1 + T * t) := by
  have hn : HasDerivAt (fun x : ℝ => sieveCutoff (x / U))
      (deriv sieveCutoff (t / U) / U) t := by
    have h := ((sieveCutoff_contDiff (n := 1)).differentiable_one (t / U)).hasDerivAt.comp t
      ((hasDerivAt_id t).div_const U)
    simpa only [Function.comp_apply, id_eq, div_eq_mul_inv, one_mul] using! h
  have hd : HasDerivAt (fun x : ℝ => profileDenominator (T * x)) T t := by
    have h := (profileDenominator_hasDerivAt (mul_nonneg hT ht)).comp t
      ((hasDerivAt_id t).const_mul T)
    simpa only [Function.comp_apply, id_eq, one_mul, mul_one] using! h
  have hlin := profileDenominator_eq_linear
    (show -(1 / 2 : ℝ) ≤ T * t by nlinarith [mul_nonneg hT ht])
  have hq : deriv (sieveFactor T U) t =
      ((deriv sieveCutoff (t / U) / U) * (1 + T * t) - sieveCutoff (t / U) * T) /
        (1 + T * t) ^ 2 := by
    simpa only [sieveFactor, Pi.div_apply, hlin] using!
      (hn.div hd (profileDenominator_pos (T * t)).ne').deriv
  rw [hq, sieveFactor_eq hT ht]
  have hden : 1 + T * t ≠ 0 := ne_of_gt (by positivity)
  field_simp [hden]

theorem sieveFactor_deriv_decay {T U t K : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (ht : 0 ≤ t)
    (hψ : BoundedCutoff sieveCutoff K) :
    |deriv (sieveFactor T U) t| ≤ (K / U + T) / (1 + T * t) := by
  rw [sieveFactor_deriv hT ht, abs_div, abs_of_pos (by positivity : 0 < 1 + T * t)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |deriv sieveCutoff (t / U) / U| + |T * sieveFactor T U t| := abs_sub _ _
    _ = |deriv sieveCutoff (t / U)| / U + T * sieveFactor T U t := by
      rw [abs_div, abs_of_pos hU, abs_mul, abs_of_nonneg hT,
        abs_of_nonneg (sieveFactor_nonneg T U t)]
    _ ≤ K / U + T := add_le_add
      (div_le_div_of_nonneg_right (hψ.deriv_bound _) hU.le)
      (by nlinarith [sieveFactor_le_one hT ht U])

theorem sieveFactor_deriv_bound {T U t K : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (ht : 0 ≤ t)
    (hψ : BoundedCutoff sieveCutoff K) : |deriv (sieveFactor T U) t| ≤ K / U + T := by
  refine (sieveFactor_deriv_decay hT hU ht hψ).trans ?_
  apply (div_le_iff₀ (by positivity : 0 < 1 + T * t)).mpr
  have hcost : 0 ≤ K / U + T := add_nonneg (div_nonneg hψ.constant_nonneg hU.le) hT
  nlinarith [mul_nonneg hcost (mul_nonneg hT ht)]

theorem sieveFactor_sq_deriv_bound {T U t K : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (ht : 0 ≤ t)
    (hψ : BoundedCutoff sieveCutoff K) :
    |deriv (fun x => sieveFactor T U x ^ 2) t| ≤ 2 * (K / U + T) := by
  have hd : deriv (fun x => sieveFactor T U x ^ 2) t =
      2 * sieveFactor T U t * deriv (sieveFactor T U) t := by
    simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using!
      (((sieveFactor_contDiff T U (n := 1)).differentiable_one t).hasDerivAt.pow 2).deriv
  have hA0 := sieveFactor_nonneg T U t
  rw [hd, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hA0]
  calc
    _ ≤ 2 * sieveFactor T U t * (K / U + T) :=
      mul_le_mul_of_nonneg_left (sieveFactor_deriv_bound hT hU ht hψ) (by positivity)
    _ ≤ 2 * (K / U + T) := by
      have hcost : 0 ≤ K / U + T := add_nonneg (div_nonneg hψ.constant_nonneg hU.le) hT
      nlinarith [sieveFactor_le_one hT ht U]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveFactor_deriv_decay
#print axioms Erdos4b.FGKMT.sieveFactor_sq_deriv_bound
