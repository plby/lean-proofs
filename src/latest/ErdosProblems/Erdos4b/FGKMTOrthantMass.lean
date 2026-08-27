/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLongFactor
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Full positive-ray masses and tensor integration

Upper support, rather than an artificial unit truncation, identifies
the positive-ray integrals. All factors are proved integrable before
using them in finite sums and products.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem integral_positiveRay_eq_interval {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ x, b < x → f x = 0) :
    (∫ x in Set.Ioi (0 : ℝ), f x) = ∫ x in (0 : ℝ)..b, f x := by
  rw [setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  have heq : (∫ x in Set.Ici (0 : ℝ), f x) = ∫ x in Set.Icc (0 : ℝ) b, f x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici Set.Icc_subset_Ici_self
    intro x hx
    apply hf x
    by_contra hxb
    exact hx.2 ⟨hx.1, le_of_not_gt hxb⟩
  rw [heq, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hb]

theorem integrableOn_positiveRay_of_upperSupport {f : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hsupport : ∀ x, b < x → f x = 0) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have htail : IntegrableOn f (Set.Ioi b) := by
    apply (integrableOn_congr_fun (fun x hx => hsupport x hx) measurableSet_Ioi).mpr
    exact integrableOn_zero
  have hbase : IntegrableOn f (Set.Icc (0 : ℝ) b) := hf.integrableOn_Icc
  apply (hbase.union htail).mono_set
  intro x hx
  by_cases hxb : x ≤ b
  · exact Or.inl ⟨hx.le, hxb⟩
  · exact Or.inr (lt_of_not_ge hxb)

theorem sieveFactor_pow_integrableOn_positiveRay {U : ℝ} (hU : 0 < U) (T : ℝ) (m : ℕ) :
    IntegrableOn (fun t => sieveFactor T U t ^ (m + 1)) (Set.Ioi (0 : ℝ)) := by
  apply integrableOn_positiveRay_of_upperSupport
    ((sieveFactor_contDiff T U (n := 1)).continuous.pow _) (b := U)
  intro t ht
  change sieveFactor T U t ^ (m + 1) = 0
  rw [sieveFactor_zero_of_ge hU ht.le T, zero_pow (by omega)]

theorem dimensionProfileFactor_integrableOn_positiveRay {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (dimensionProfileFactor k) (Set.Ioi (0 : ℝ)) := by
  simpa only [Nat.zero_add, pow_one, dimensionProfileFactor] using!
    sieveFactor_pow_integrableOn_positiveRay (profile_scales_bounds hk hlog).2.1
      (sieveProfileScale k) 0

theorem dimensionProfileFactor_sq_integrableOn_positiveRay {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (fun t => dimensionProfileFactor k t ^ 2) (Set.Ioi (0 : ℝ)) :=
  sieveFactor_pow_integrableOn_positiveRay (profile_scales_bounds hk hlog).2.1
    (sieveProfileScale k) 1

theorem dimensionLongFactor_integrableOn_positiveRay (k : ℕ) :
    IntegrableOn (dimensionLongFactor k) (Set.Ioi (0 : ℝ)) := by
  simpa only [Nat.zero_add, pow_one, dimensionLongFactor] using!
    sieveFactor_pow_integrableOn_positiveRay (by norm_num : (0 : ℝ) < 2)
      (sieveProfileScale k) 0

theorem dimensionLongFactor_sq_integrableOn_positiveRay (k : ℕ) :
    IntegrableOn (fun t => dimensionLongFactor k t ^ 2) (Set.Ioi (0 : ℝ)) :=
  sieveFactor_pow_integrableOn_positiveRay (by norm_num) (sieveProfileScale k) 1

theorem dimensionProfileFirstMass_eq_positiveRay {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    dimensionProfileFirstMass k = ∫ t in Set.Ioi (0 : ℝ), dimensionProfileFactor k t := by
  symm
  apply integral_positiveRay_eq_interval zero_le_one
  intro t ht
  have hb := profile_scales_bounds hk hlog
  exact sieveFactor_zero_of_ge hb.2.1 (by linarith [hb.2.2.1]) _

theorem dimensionProfileMass_eq_positiveRay {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    dimensionProfileMass k = ∫ t in Set.Ioi (0 : ℝ), dimensionProfileFactor k t ^ 2 := by
  symm
  apply integral_positiveRay_eq_interval zero_le_one
  intro t ht
  have hb := profile_scales_bounds hk hlog
  have hz : dimensionProfileFactor k t = 0 :=
    sieveFactor_zero_of_ge hb.2.1 (by linarith [hb.2.2.1]) _
  rw [hz, zero_pow (by norm_num)]

theorem dimensionLongFirstMass_eq_positiveRay (k : ℕ) :
    dimensionLongFirstMass k = ∫ t in Set.Ioi (0 : ℝ), dimensionLongFactor k t := by
  symm
  exact integral_positiveRay_eq_interval (by norm_num)
    (fun t ht => dimensionLongFactor_zero ht.le k)

theorem dimensionLongMass_eq_positiveRay (k : ℕ) :
    dimensionLongMass k = ∫ t in Set.Ioi (0 : ℝ), dimensionLongFactor k t ^ 2 := by
  symm
  apply integral_positiveRay_eq_interval (by norm_num)
  intro t ht
  rw [dimensionLongFactor_zero ht.le k, zero_pow (by norm_num)]

theorem integral_orthant_tensor {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) :
    (∫ t : ι → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)), ∏ i, f i (t i)) =
      ∏ i, ∫ x in Set.Ioi (0 : ℝ), f i x := by
  have h := integral_fintype_prod_eq_prod f
    (μ := fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioi 0))
  rw [← Measure.restrict_pi_pi] at h
  exact h

theorem integrableOn_orthant_tensor {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ}
    (hf : ∀ i, IntegrableOn (f i) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun t : ι → ℝ => ∏ i, f i (t i))
      (Set.univ.pi (fun _ => Set.Ioi (0 : ℝ))) := by
  have h := Integrable.fintype_prod
    (μ := fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioi 0)) hf
  rw [← Measure.restrict_pi_pi] at h
  exact h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionLongMass_eq_positiveRay
#print axioms Erdos4b.FGKMT.integrableOn_orthant_tensor
