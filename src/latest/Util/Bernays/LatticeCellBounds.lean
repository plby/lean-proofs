import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Counting lattice points by bounded fundamental cells

The two ball inclusions retain a boundary-width error. In dimension two this
gives the square-root error needed for the ideal-class Dirichlet series.
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise Classical

namespace Bernays

theorem fundamental_cell_ball_bounds {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (L : AddSubgroup E) [Countable L]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) {B R : ℝ}
    (hB : ∀ x ∈ F, ‖x‖ ≤ B) (a : E) (S : Finset L)
    (hS : ∀ l : L, l ∈ S ↔ ‖a + (l : E)‖ ≤ R) :
    μ (closedBall 0 (R - B)) ≤ (S.card : ℝ≥0∞) * μ F ∧
      (S.card : ℝ≥0∞) * μ F ≤ μ (closedBall 0 (R + B)) := by
  have hFa := hF.vadd_of_comm a
  have hcell (l : L) : μ (l +ᵥ (a +ᵥ F)) = μ F := by
    rw [measure_vadd, measure_vadd]
  have hnorm (l : L) {x : E} (hx : x ∈ l +ᵥ (a +ᵥ F)) :
      ‖x - (a + (l : E))‖ ≤ B := by
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    change ‖(l : E) + (a + z) - (a + (l : E))‖ ≤ B
    rw [show (l : E) + (a + z) - (a + (l : E)) = z by abel]
    exact hB z hz
  constructor
  · rw [hFa.measure_eq_tsum' (closedBall 0 (R - B))]
    calc
      (∑' l : L, μ (closedBall 0 (R - B) ∩ (l +ᵥ (a +ᵥ F)))) ≤
          ∑' l : L, if l ∈ S then μ F else 0 := by
        apply ENNReal.tsum_le_tsum
        intro l
        by_cases hl : l ∈ S
        · rw [if_pos hl, ← hcell l]
          exact measure_mono inter_subset_right
        · rw [if_neg hl]
          have hempty : closedBall 0 (R - B) ∩ (l +ᵥ (a +ᵥ F)) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hxnorm : ‖x‖ ≤ R - B := by simpa only [mem_closedBall, dist_zero_right] using hx.1
            have hcenter : ‖a + (l : E)‖ ≤ R := by
              have ht := norm_sub_le x (x - (a + (l : E)))
              rw [sub_sub_cancel] at ht
              exact ht.trans (by linarith [hnorm l hx.2])
            exact hl ((hS l).mpr hcenter)
          simp only [hempty, measure_empty, le_refl]
      _ = (S.card : ℝ≥0∞) * μ F := by
        rw [tsum_eq_sum (s := S) (fun l hl => if_neg hl)]
        simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
  · rw [hFa.measure_eq_tsum' (closedBall 0 (R + B))]
    calc
      (S.card : ℝ≥0∞) * μ F =
          ∑ l ∈ S, μ (closedBall 0 (R + B) ∩ (l +ᵥ (a +ᵥ F))) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro l hl
        have hsubset : (l +ᵥ (a +ᵥ F)) ⊆ closedBall 0 (R + B) := by
          intro x hx
          have ht := norm_add_le (x - (a + (l : E))) (a + (l : E))
          rw [sub_add_cancel] at ht
          have hxn : ‖x‖ ≤ R + B := ht.trans (by linarith [hnorm l hx, (hS l).mp hl])
          simpa only [mem_closedBall, dist_zero_right] using hxn
        rw [Set.inter_eq_right.mpr hsubset, hcell]
      _ ≤ _ := ENNReal.sum_le_tsum S

theorem complex_fundamental_cell_error (L : AddSubgroup ℂ) [Countable L]
    {F : Set ℂ} (hF : IsAddFundamentalDomain L F volume) {B R : ℝ}
    (hB₀ : 0 ≤ B) (hB : ∀ z ∈ F, ‖z‖ ≤ B) (hR : 0 ≤ R)
    (a : ℂ) (S : Finset L) (hS : ∀ l : L, l ∈ S ↔ ‖a + (l : ℂ)‖ ≤ R) :
    |(S.card : ℝ) * volume.real F - Real.pi * R ^ 2| ≤
      Real.pi * (2 * B * R + B ^ 2) := by
  obtain ⟨hlo, hhi⟩ := fundamental_cell_ball_bounds L volume hF hB a S hS
  have hFfinite : volume F ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (t := closedBall 0 B) ?_) measure_closedBall_lt_top
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hB z hz
  have hprod : (S.card : ℝ≥0∞) * volume F ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hFfinite
  have hball (r : ℝ) (hr : 0 ≤ r) : (volume (closedBall (0 : ℂ) r)).toReal = Real.pi * r ^ 2 := by
    rw [Complex.volume_closedBall]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.coe_toReal]
    exact mul_comm _ _
  have hhiR := (ENNReal.toReal_le_toReal hprod (ne_of_lt measure_closedBall_lt_top)).mpr hhi
  rw [hball (R + B) (by linarith), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hhiR
  change (S.card : ℝ) * volume.real F ≤ Real.pi * (R + B) ^ 2 at hhiR
  rw [abs_le]
  constructor
  · by_cases hBR : B ≤ R
    · have hloR := (ENNReal.toReal_le_toReal (ne_of_lt measure_closedBall_lt_top) hprod).mpr hlo
      rw [hball (R - B) (sub_nonneg.mpr hBR), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hloR
      change Real.pi * (R - B) ^ 2 ≤ (S.card : ℝ) * volume.real F at hloR
      nlinarith [Real.pi_pos, sq_nonneg B]
    · have hcount : 0 ≤ (S.card : ℝ) * volume.real F := by positivity
      have hsq : R ^ 2 ≤ B ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le,
        mul_nonneg (mul_nonneg Real.pi_pos.le hB₀) hR]
  · nlinarith [Real.pi_pos, sq_nonneg B]

end Bernays
