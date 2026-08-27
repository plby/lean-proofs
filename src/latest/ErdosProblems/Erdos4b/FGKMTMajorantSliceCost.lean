/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMajorantSlice

/-!
# First-mass control of the entire majorant slice

The long and short first masses both exceed `1/(2*k)`. This controls
the value and derivative of the two-term majorant slice by its full
face integral, with only the polynomial factor `k*T`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem dimensionProfileFirstMass_le_long {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    dimensionProfileFirstMass k ≤ dimensionLongFirstMass k := by
  rw [dimensionProfileFirstMass_eq_positiveRay hk hlog, dimensionLongFirstMass_eq_positiveRay]
  exact setIntegral_mono_on (dimensionProfileFactor_integrableOn_positiveRay hk hlog)
    (dimensionLongFactor_integrableOn_positiveRay k) measurableSet_Ioi
    (fun x hx => dimensionProfileFactor_le_long hk hlog hx.le)

theorem shortTensor_add_majorant_le_face {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m : ℕ) (t : Fin m → ℝ) :
    (∏ i, dimensionProfileFactor k (t i)) + sieveProfileMajorant k m t ≤
      2 * (k : ℝ) * majorantFaceValue k m t := by
  let P := ∏ i, dimensionProfileFactor k (t i)
  let Q := sieveProfileMajorant k m t
  let b := dimensionProfileFirstMass k
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg _ _
  have hQ : 0 ≤ Q := sieveProfileMajorant_nonneg k m t
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 1 ≤ (2 * (k : ℝ)) * b := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mp
      (dimensionProfileFirstMass_bounds hk hlog).1
    simpa only [b, mul_comm] using h
  have hV : b * (P + Q) ≤ majorantFaceValue k m t := by
    have h := mul_le_mul_of_nonneg_right (dimensionProfileFirstMass_le_long hk hlog) hP
    change b * (P + Q) ≤ dimensionLongFirstMass k * P + b * Q
    dsimp only [b] at *
    nlinarith
  calc
    _ ≤ (2 * (k : ℝ)) * (b * (P + Q)) := by
      have h := mul_le_mul_of_nonneg_right hb (add_nonneg hP hQ)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left hV (by positivity)

theorem sieveProfileMajorant_cons_contDiff (k m : ℕ) (t : Fin m → ℝ) :
    ContDiff ℝ 1 (fun x => sieveProfileMajorant k (m + 1) (Fin.cons x t)) := by
  simpa only [sieveProfileMajorant_cons] using!
    (((dimensionLongFactor_contDiff k (n := 1)).mul contDiff_const).add
      ((dimensionProfileFactor_contDiff k (n := 1)).mul contDiff_const))

theorem sieveProfileMajorant_cons_hasDerivAt (k m : ℕ) (t : Fin m → ℝ) (x : ℝ) :
    HasDerivAt (fun s => sieveProfileMajorant k (m + 1) (Fin.cons s t))
      (deriv (dimensionLongFactor k) x * (∏ i, dimensionProfileFactor k (t i)) +
        deriv (dimensionProfileFactor k) x * sieveProfileMajorant k m t) x := by
  have hD := ((dimensionLongFactor_contDiff k (n := 1)).differentiable_one x).hasDerivAt
  have hA := ((dimensionProfileFactor_contDiff k (n := 1)).differentiable_one x).hasDerivAt
  simpa only [sieveProfileMajorant_cons] using!
    (hD.mul_const (∏ i, dimensionProfileFactor k (t i))).add
      (hA.mul_const (sieveProfileMajorant k m t))

theorem exists_sieveProfileMajorant_cons_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (m : ℕ) (t : Fin m → ℝ) (x : ℝ), 0 ≤ x →
        |deriv (fun s => sieveProfileMajorant k (m + 1) (Fin.cons s t)) x| ≤
          C * (k : ℝ) * sieveProfileScale k * majorantFaceValue k m t := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  refine ⟨2 * (K + 1), by positivity, ?_⟩
  intro k hk hlog m t x hx
  have hT := (profile_scales_bounds hk hlog).1
  have hT0 : 0 ≤ sieveProfileScale k := zero_le_one.trans hT
  have hP : 0 ≤ ∏ i, dimensionProfileFactor k (t i) :=
    Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg _ _
  have hQ := sieveProfileMajorant_nonneg k m t
  have hD1 : dimensionLongFactor k x ≤ 1 := sieveFactor_le_one hT0 hx _
  have hDA : |deriv (dimensionProfileFactor k) x| ≤ (K + 1) * sieveProfileScale k := by
    have h := dimensionProfileFactor_deriv_le_long hk hlog hψ hx
    apply h.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hD1
      (by positivity : 0 ≤ (K + 1) * sieveProfileScale k)
  have hDD : |deriv (dimensionLongFactor k) x| ≤ (K + 1) * sieveProfileScale k := by
    have h := sieveFactor_deriv_bound hT0 (by norm_num : (0 : ℝ) < 2) hx hψ
    exact h.trans (by nlinarith)
  rw [(sieveProfileMajorant_cons_hasDerivAt k m t x).deriv]
  calc
    _ ≤ |deriv (dimensionLongFactor k) x * (∏ i, dimensionProfileFactor k (t i))| +
        |deriv (dimensionProfileFactor k) x * sieveProfileMajorant k m t| := abs_add_le _ _
    _ = |deriv (dimensionLongFactor k) x| * (∏ i, dimensionProfileFactor k (t i)) +
        |deriv (dimensionProfileFactor k) x| * sieveProfileMajorant k m t := by
      rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_nonneg hQ]
    _ ≤ ((K + 1) * sieveProfileScale k) *
        ((∏ i, dimensionProfileFactor k (t i)) + sieveProfileMajorant k m t) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hDD hP) (mul_le_mul_of_nonneg_right hDA hQ)
    _ ≤ ((K + 1) * sieveProfileScale k) * (2 * (k : ℝ) * majorantFaceValue k m t) :=
      mul_le_mul_of_nonneg_left (shortTensor_add_majorant_le_face hk hlog m t) (by positivity)
    _ = _ := by ring

theorem majorantFaceValue_eq_interval {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m : ℕ) (t : Fin m → ℝ) :
    majorantFaceValue k m t =
      ∫ x in (0 : ℝ)..2, sieveProfileMajorant k (m + 1) (Fin.cons x t) := by
  rw [majorantFaceValue_eq_integral hk hlog]
  apply integral_positiveRay_eq_interval (by norm_num)
  intro x hx
  exact sieveProfileMajorant_zero_of_coord_ge_two hk hlog (0 : Fin (m + 1)) hx.le

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.shortTensor_add_majorant_le_face
#print axioms Erdos4b.FGKMT.exists_sieveProfileMajorant_cons_deriv_bound
#print axioms Erdos4b.FGKMT.majorantFaceValue_eq_interval
