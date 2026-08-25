import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition

open Classical
noncomputable section

lemma PlanarRot90ConeAvoidsRay {d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0) (_hnot : ¬ ∃ a : ℝ, 0 < a ∧ v = a • d) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
        c • v ≠ t • d + s • PlanarRot90 d := by
  let A : ℝ := inner ℝ v d / (‖d‖ ^ 2)
  let B : ℝ := inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2)
  by_cases hB : B = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro c t s hc ht hs_ne hs_lt hEq
    have hcoeff := PlanarRot90CoefficientUniqueness (d := d) (v := c • v) hd hEq
    have hs_eq : s = c * B := by
      calc
        s = inner ℝ (c • v) (PlanarRot90 d) / (‖d‖ ^ 2) := hcoeff.2
        _ = c * B := by
          rw [real_inner_smul_left]
          ring
    have hs0 : s = 0 := by
      simp [hs_eq, hB]
    exact hs_ne hs0
  · let κ : ℝ := |B| / (2 * (|A| + 1))
    have hκpos : 0 < κ := by
      have hBpos : 0 < |B| := abs_pos.mpr hB
      have hden : 0 < 2 * (|A| + 1) := by positivity
      exact div_pos hBpos hden
    refine ⟨κ, hκpos, ?_⟩
    intro c t s hc ht hs_ne hs_lt hEq
    have hcoeff := PlanarRot90CoefficientUniqueness (d := d) (v := c • v) hd hEq
    have ht_eq : t = c * A := by
      calc
        t = inner ℝ (c • v) d / (‖d‖ ^ 2) := hcoeff.1
        _ = c * A := by
          rw [real_inner_smul_left]
          ring
    have hs_eq : s = c * B := by
      calc
        s = inner ℝ (c • v) (PlanarRot90 d) / (‖d‖ ^ 2) := hcoeff.2
        _ = c * B := by
          rw [real_inner_smul_left]
          ring
    have hcpos : 0 < c := by
      by_contra hnotc
      have hc0 : c = 0 := le_antisymm (le_of_not_gt hnotc) hc
      have : t = 0 := by simp [ht_eq, hc0]
      linarith
    have hApos : 0 < A := by
      have : 0 < c * A := by simpa [← ht_eq] using ht
      exact (pos_iff_pos_of_mul_pos this).mp hcpos
    have habs_s : |s| = c * |B| := by
      rw [hs_eq, abs_mul, abs_of_pos hcpos]
    have hratio_lt : c * |B| < κ * (c * A) := by
      simpa [habs_s, ht_eq] using hs_lt
    have hcancel : |B| < κ * A := by
      nlinarith [hratio_lt]
    have hκA_le : κ * A ≤ |B| / 2 := by
      have hA_le : A ≤ |A| + 1 := by
        have hA_abs : A ≤ |A| := le_abs_self A
        linarith
      have hdenpos : 0 < 2 * (|A| + 1) := by positivity
      have hnonnegB : 0 ≤ |B| := abs_nonneg B
      have hnonnegA : 0 ≤ A := le_of_lt hApos
      calc
        κ * A = (|B| / (2 * (|A| + 1))) * A := rfl
        _ = |B| * A / (2 * (|A| + 1)) := by ring
        _ ≤ |B| * (|A| + 1) / (2 * (|A| + 1)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA_le hnonnegB) (le_of_lt hdenpos)
        _ = |B| / 2 := by
          have hpos : |A| + 1 ≠ 0 := by positivity
          field_simp [hpos]
    have hBhalf_lt : |B| / 2 < |B| := by
      have hBpos : 0 < |B| := abs_pos.mpr hB
      linarith
    linarith
