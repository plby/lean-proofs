/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSieveProfile
import ErdosProblems.Erdos4b.FGKMTLongFactor
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pointwise control when one sieve coordinate changes

The derivative is controlled by a tensor with one long-cutoff factor.
The constant is absolute and the short-factor product is retained.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem sieveProfile_cons_hasDerivAt (k j : ℕ) (t : Fin j → ℝ) (x : ℝ) :
    HasDerivAt (fun s => sieveProfile k (j + 1) (Fin.cons s t))
      ((∏ i, dimensionProfileFactor k (t i)) *
        (deriv (dimensionProfileFactor k) x * sieveCutoff ((∑ i, t i) + x) +
          dimensionProfileFactor k x * deriv sieveCutoff ((∑ i, t i) + x))) x := by
  have hA := ((dimensionProfileFactor_contDiff k (n := 1)).differentiable_one x).hasDerivAt
  have hψ : HasDerivAt (fun s => sieveCutoff ((∑ i, t i) + s))
      (deriv sieveCutoff ((∑ i, t i) + x)) x := by
    simpa only [Function.comp_apply, one_mul, mul_one] using!
      (((sieveCutoff_contDiff (n := 1)).differentiable_one
        ((∑ i, t i) + x)).hasDerivAt.comp x ((hasDerivAt_id x).const_add (∑ i, t i)))
  simpa only [sieveProfile_cons] using! (hA.mul hψ).const_mul (∏ i, dimensionProfileFactor k (t i))

theorem sieveProfile_cons_deriv_bound {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {K : ℝ} (hψ : BoundedCutoff sieveCutoff K)
    (j : ℕ) (t : Fin j → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    |deriv (fun s => sieveProfile k (j + 1) (Fin.cons s t)) x| ≤
      (2 * K + 1) * sieveProfileScale k * dimensionLongFactor k x *
        ∏ i, dimensionProfileFactor k (t i) := by
  have hT := (profile_scales_bounds hk hlog).1
  have hK := hψ.constant_nonneg
  have hA := dimensionProfileFactor_nonneg k x
  have hD := dimensionLongFactor_nonneg k x
  have hP : 0 ≤ ∏ i, dimensionProfileFactor k (t i) :=
    Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k (t i)
  have hcut : |sieveCutoff ((∑ i, t i) + x)| ≤ 1 := by
    rw [abs_of_nonneg (sieveCutoff_nonneg _)]
    exact sieveCutoff_le_one _
  rw [(sieveProfile_cons_hasDerivAt k j t x).deriv, abs_mul, abs_of_nonneg hP]
  calc
    _ ≤ (∏ i, dimensionProfileFactor k (t i)) *
        (|deriv (dimensionProfileFactor k) x| * |sieveCutoff ((∑ i, t i) + x)| +
          dimensionProfileFactor k x * |deriv sieveCutoff ((∑ i, t i) + x)|) := by
      apply mul_le_mul_of_nonneg_left _ hP
      simpa only [abs_mul, abs_of_nonneg hA] using abs_add_le
        (deriv (dimensionProfileFactor k) x * sieveCutoff ((∑ i, t i) + x))
        (dimensionProfileFactor k x * deriv sieveCutoff ((∑ i, t i) + x))
    _ ≤ (∏ i, dimensionProfileFactor k (t i)) *
        ((K + 1) * sieveProfileScale k * dimensionLongFactor k x +
          dimensionLongFactor k x * K) := by
      apply mul_le_mul_of_nonneg_left _ hP
      apply add_le_add
      · have hh := mul_le_mul (dimensionProfileFactor_deriv_le_long hk hlog hψ hx) hcut
          (abs_nonneg _) (by positivity :
            0 ≤ (K + 1) * sieveProfileScale k * dimensionLongFactor k x)
        simpa only [mul_one] using hh
      · exact mul_le_mul (dimensionProfileFactor_le_long hk hlog hx) (hψ.deriv_bound _)
          (abs_nonneg _) hD
    _ ≤ _ := by
      have hKD := mul_le_mul_of_nonneg_left hT (mul_nonneg hK hD)
      have hinner : (K + 1) * sieveProfileScale k * dimensionLongFactor k x +
          dimensionLongFactor k x * K ≤
          (2 * K + 1) * sieveProfileScale k * dimensionLongFactor k x := by nlinarith
      calc
        _ ≤ (∏ i, dimensionProfileFactor k (t i)) *
            ((2 * K + 1) * sieveProfileScale k * dimensionLongFactor k x) :=
          mul_le_mul_of_nonneg_left hinner hP
        _ = _ := by ring

theorem exists_sieveProfile_coordinate_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (t : Fin j → ℝ) (x : ℝ), 0 ≤ x →
        |deriv (fun s => sieveProfile k (j + 1) (Fin.cons s t)) x| ≤
          C * sieveProfileScale k * dimensionLongFactor k x *
            ∏ i, dimensionProfileFactor k (t i) := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  refine ⟨2 * K + 1, by linarith, ?_⟩
  intro k hk hlog j t x hx
  exact sieveProfile_cons_deriv_bound hk hlog hψ j t hx

theorem exists_sieveProfile_coordinate_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j : ℕ) (t : Fin j → ℝ) (x y : ℝ), 0 ≤ x → x ≤ y →
        |sieveProfile k (j + 1) (Fin.cons y t) - sieveProfile k (j + 1) (Fin.cons x t)| ≤
          (C * sieveProfileScale k * dimensionLongFactor k x *
            ∏ i, dimensionProfileFactor k (t i)) * (y - x) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_coordinate_deriv_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog j t x y hx hxy
  have hT : 0 ≤ sieveProfileScale k := zero_le_one.trans (profile_scales_bounds hk hlog).1
  have hP : 0 ≤ ∏ i, dimensionProfileFactor k (t i) :=
    Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k (t i)
  have hder (s : ℝ) : HasDerivAt (fun z => sieveProfile k (j + 1) (Fin.cons z t))
      (deriv (fun z => sieveProfile k (j + 1) (Fin.cons z t)) s) s :=
    (sieveProfile_cons_hasDerivAt k j t s).differentiableAt.hasDerivAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := x) (b := y)
    (fun s _hs => (hder s).hasDerivWithinAt)
    (C := C * sieveProfileScale k * dimensionLongFactor k x *
      ∏ i, dimensionProfileFactor k (t i)) (by
      intro s hs
      rw [Real.norm_eq_abs]
      have hs0 : 0 ≤ s := hx.trans hs.1
      have hD : dimensionLongFactor k s ≤ dimensionLongFactor k x :=
        sieveFactor_antitoneOn hT (by norm_num) hx hs0 hs.1
      exact (hbound hk hlog j t s hs0).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hD (mul_nonneg hC.le hT)) hP)) y ⟨hxy, le_rfl⟩
  simpa only [Real.norm_eq_abs] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_sieveProfile_coordinate_deriv_bound
#print axioms Erdos4b.FGKMT.exists_sieveProfile_coordinate_variation_bound
