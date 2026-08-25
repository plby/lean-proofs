import ErdosProblems.Erdos964.ScalarFacePrimitiveBounds
import ErdosProblems.Erdos964.ScalarTransformRounding

/-!
# Uniform rounding errors at the two face endpoints
-/

namespace Erdos964

theorem normalized_strict_endpoint_bounds (R r : ℕ) (hr : 0 < r) (hrR : r < R) :
    let L := Real.log R
    let z := Real.log r / L
    let q := Real.log ((R - 1) / r : ℕ) / L
    z ∈ Set.Icc (0 : ℝ) 1 ∧ q ∈ Set.Icc (0 : ℝ) 1 ∧ |q - (1 - z)| ≤ Real.log 2 / L := by
  dsimp only
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hb := scalar_transform_log_endpoint_bounds R r hr hrR
  have hlogr := Real.log_natCast_nonneg r
  have hlogrR : Real.log r ≤ Real.log R := Real.log_le_log
    (by exact_mod_cast hr) (by exact_mod_cast hrR.le)
  have hz : Real.log r / Real.log R ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlogr hL.le, (div_le_one hL).mpr hlogrR⟩
  have hq : Real.log ((R - 1) / r : ℕ) / Real.log R ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb.1 hL.le, (div_le_one hL).mpr (hb.2.1.trans hb.2.2.1)⟩
  refine ⟨hz, hq, ?_⟩
  have hid : Real.log ((R - 1) / r : ℕ) / Real.log R - (1 - Real.log r / Real.log R) =
      (Real.log ((R - 1) / r : ℕ) - (Real.log R - Real.log r)) / Real.log R := by
    field_simp
  rw [hid, abs_div, abs_of_pos hL, abs_of_nonpos (sub_nonpos.mpr hb.2.1)]
  exact div_le_div_of_nonneg_right (by linarith [hb.2.2.2]) hL.le

theorem scalar_small_face_endpoint_error (R p : ℕ) (hp : 0 < p) (hpR : p < R) :
    let L := Real.log R
    let z := Real.log p / L
    let q₁ := Real.log (R - 1 : ℕ) / L
    let q₂ := Real.log ((R - 1) / p : ℕ) / L
    |scalarLargeFacePrimitive q₁ + scalarSmallFacePrimitive z q₂ - scalarLargeFacePrimitive q₂ -
      truncatedSieveFace z| ≤ 132 * (Real.log 2 / L) := by
  dsimp only
  let L := Real.log R
  let z := Real.log p / L
  let q₁ := Real.log (R - 1 : ℕ) / L
  let q₂ := Real.log ((R - 1) / p : ℕ) / L
  let e := Real.log 2 / L
  have h1 := normalized_strict_endpoint_bounds R 1 (by decide) (by omega)
  simp only [Nat.div_one, Nat.cast_one, Real.log_one, zero_div, sub_zero] at h1
  obtain ⟨hz, hq₂, he₂⟩ := normalized_strict_endpoint_bounds R p hp hpR
  have hqref : 1 - z ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have hlarge₁ : |scalarLargeFacePrimitive q₁ - scalarLargeFacePrimitive 1| ≤ 16 * e :=
    (scalarLargeFacePrimitive_lipschitz q₁ 1 h1.2.1 (by norm_num)).trans
      (mul_le_mul_of_nonneg_left h1.2.2 (by norm_num))
  have hsmall : |scalarSmallFacePrimitive z q₂ - scalarSmallFacePrimitive z (1 - z)| ≤ 100 * e :=
    (scalarSmallFacePrimitive_lipschitz z q₂ (1 - z) hz hq₂ hqref).trans
      (mul_le_mul_of_nonneg_left he₂ (by norm_num))
  have hlarge₂ : |scalarLargeFacePrimitive q₂ - scalarLargeFacePrimitive (1 - z)| ≤ 16 * e :=
    (scalarLargeFacePrimitive_lipschitz q₂ (1 - z) hq₂ hqref).trans
      (mul_le_mul_of_nonneg_left he₂ (by norm_num))
  change |scalarLargeFacePrimitive q₁ + scalarSmallFacePrimitive z q₂ -
    scalarLargeFacePrimitive q₂ -
    truncatedSieveFace z| ≤ 132 * e
  rw [← scalarFacePrimitive_eq_truncatedSieveFace z]
  have hid : scalarLargeFacePrimitive q₁ + scalarSmallFacePrimitive z q₂ -
      scalarLargeFacePrimitive q₂ -
      (scalarLargeFacePrimitive 1 + scalarSmallFacePrimitive z (1 - z) -
        scalarLargeFacePrimitive (1 - z)) =
      ((scalarLargeFacePrimitive q₁ - scalarLargeFacePrimitive 1) +
        (scalarSmallFacePrimitive z q₂ - scalarSmallFacePrimitive z (1 - z))) -
        (scalarLargeFacePrimitive q₂ - scalarLargeFacePrimitive (1 - z)) := by ring
  rw [hid]
  calc
    _ ≤ |(scalarLargeFacePrimitive q₁ - scalarLargeFacePrimitive 1) +
          (scalarSmallFacePrimitive z q₂ - scalarSmallFacePrimitive z (1 - z))| +
        |scalarLargeFacePrimitive q₂ - scalarLargeFacePrimitive (1 - z)| := abs_sub _ _
    _ ≤ (|scalarLargeFacePrimitive q₁ - scalarLargeFacePrimitive 1| +
          |scalarSmallFacePrimitive z q₂ - scalarSmallFacePrimitive z (1 - z)|) +
        |scalarLargeFacePrimitive q₂ - scalarLargeFacePrimitive (1 - z)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 132 * e := by linarith

theorem scalar_large_face_endpoint_error (R : ℕ) (hR : 2 ≤ R) :
    |scalarLargeFacePrimitive (Real.log (R - 1 : ℕ) / Real.log R) - truncatedSieveFace 1| ≤
      16 * (Real.log 2 / Real.log R) := by
  have hb := normalized_strict_endpoint_bounds R 1 (by decide) (by omega)
  simp only [Nat.div_one, Nat.cast_one, Real.log_one, zero_div, sub_zero] at hb
  have hface : scalarLargeFacePrimitive 1 = truncatedSieveFace 1 := by
    rw [scalarLargeFacePrimitive_one, truncatedSieveFace_eq]
    norm_num [sieveFaceKernel]
  rw [← hface]
  exact (scalarLargeFacePrimitive_lipschitz _ 1 hb.2.1 (by norm_num)).trans
    (mul_le_mul_of_nonneg_left hb.2.2 (by norm_num))

end Erdos964
